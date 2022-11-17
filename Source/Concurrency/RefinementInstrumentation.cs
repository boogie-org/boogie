using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  class RefinementInstrumentation
  {
    public virtual List<Variable> NewLocalVars => new List<Variable>();

    public virtual List<Cmd> CreateInitCmds()
    {
      return new List<Cmd>();
    }
    
    public virtual List<Cmd> CreateAssumeCmds()
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateActionEvaluationCmds()
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateAssertCmds()
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateReturnAssertCmds()
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateUnchangedAssertCmds()
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateUpdatesToRefinementVars(bool isMarkedCall)
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateUpdatesToOldOutputVars()
    {
      return new List<Cmd>();
    }
  }

  class ActionRefinementInstrumentation : RefinementInstrumentation
  {
    private CivlTypeChecker civlTypeChecker;
    private Dictionary<Variable, Variable> oldGlobalMap;
    private Dictionary<Variable, Variable> oldOutputMap;
    private List<Variable> newLocalVars;
    private Variable pc;
    private Variable ok;
    private Variable eval;
    private Expr gate;
    private Expr transitionRelation;
    private IToken tok;
    private int layerNum;

    private Dictionary<AtomicAction, Expr> transitionRelationCache;

    public ActionRefinementInstrumentation(
      CivlTypeChecker civlTypeChecker,
      Implementation impl,
      Implementation originalImpl,
      Dictionary<Variable, Variable> oldGlobalMap)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.tok = impl.tok;
      this.oldGlobalMap = new Dictionary<Variable, Variable>();
      ActionProc actionProc = civlTypeChecker.procToYieldingProc[originalImpl.Proc] as ActionProc;
      this.layerNum = actionProc.upperLayer;
      foreach (Variable v in civlTypeChecker.GlobalVariables)
      {
        var layerRange = civlTypeChecker.GlobalVariableLayerRange(v);
        if (layerRange.lowerLayerNum <= layerNum && layerNum < layerRange.upperLayerNum)
        {
          this.oldGlobalMap[v] = oldGlobalMap[v];
        }
      }

      this.newLocalVars = new List<Variable>();
      pc = civlTypeChecker.LocalVariable("pc", Type.Bool);
      newLocalVars.Add(pc);
      if (!civlTypeChecker.Options.TrustRefinement)
      {
        ok = civlTypeChecker.LocalVariable("ok", Type.Bool);
        newLocalVars.Add(ok);
        eval = civlTypeChecker.LocalVariable("eval", Type.Bool);
        newLocalVars.Add(eval);
      }

      this.transitionRelationCache = new Dictionary<AtomicAction, Expr>();

      oldOutputMap = new Dictionary<Variable, Variable>();
      foreach (Variable f in impl.OutParams)
      {
        LocalVariable copy = Old(f);
        newLocalVars.Add(copy);
        oldOutputMap[f] = copy;
      }

      Dictionary<Variable, Expr> foroldMap = new Dictionary<Variable, Expr>();
      foreach (Variable g in civlTypeChecker.GlobalVariables)
      {
        foroldMap[g] = Expr.Ident(oldGlobalMap[g]);
      }

      // The parameters of an atomic action come from the implementation that denotes the atomic action specification.
      // To use the transition relation computed below in the context of the yielding procedure of the refinement check,
      // we need to substitute the parameters.
      AtomicAction atomicAction = actionProc.refinedAction;
      Implementation atomicActionImpl = atomicAction.impl;
      Dictionary<Variable, Expr> alwaysMap = new Dictionary<Variable, Expr>();
      for (int i = 0, j = 0; i < impl.InParams.Count; i++)
      {
        if (civlTypeChecker.FormalRemainsInAction(actionProc, actionProc.proc.InParams[i]))
        {
          alwaysMap[atomicActionImpl.InParams[j]] = Expr.Ident(impl.InParams[i]);
          j++;
        }
      }

      for (int i = 0, j = 0; i < impl.OutParams.Count; i++)
      {
        if (civlTypeChecker.FormalRemainsInAction(actionProc, actionProc.proc.OutParams[i]))
        {
          alwaysMap[atomicActionImpl.OutParams[j]] = Expr.Ident(impl.OutParams[i]);
          j++;
        }
      }

      if (atomicAction.HasPendingAsyncs)
      {
        Variable collectedPAs = civlTypeChecker.implToPendingAsyncCollector[originalImpl];
        alwaysMap[atomicActionImpl.OutParams.Last()] = Expr.Ident(collectedPAs);
        LocalVariable copy = Old(collectedPAs);
        newLocalVars.Add(copy);
        oldOutputMap[collectedPAs] = copy;
      }

      Substitution always = Substituter.SubstitutionFromDictionary(alwaysMap);
      Substitution forold = Substituter.SubstitutionFromDictionary(foroldMap);
      Expr transitionRelationExpr = GetTransitionRelation(atomicAction);
      transitionRelation = Substituter.ApplyReplacingOldExprs(always, forold, transitionRelationExpr);
      Expr gateExpr = Expr.And(atomicAction.gate.Select(g => g.Expr));
      gateExpr.Type = Type.Bool;
      gate = Substituter.Apply(always, gateExpr);
    }

    public override List<Variable> NewLocalVars => newLocalVars;

    public override List<Cmd> CreateInitCmds()
    {
      var lhss = new List<IdentifierExpr> { Expr.Ident(pc) };
      var rhss = new List<Expr> { Expr.False };
      if (!civlTypeChecker.Options.TrustRefinement)
      {
        lhss.AddRange(new List<IdentifierExpr> { Expr.Ident(ok), Expr.Ident(eval) });
        rhss.AddRange(new List<Expr> { Expr.False, Expr.False });
      }
      var cmds = new List<Cmd> { CmdHelper.AssignCmd(lhss, rhss) };
      cmds.AddRange(CreateUpdatesToOldOutputVars());
      // assume spec gate at procedure entry
      cmds.Add(CmdHelper.AssumeCmd(gate));
      return cmds;
    }

    public override List<Cmd> CreateAssumeCmds()
    {
      // assume pc || gate(i, g);
      Expr assumeExpr = Expr.Or(Expr.Ident(pc), gate);
      assumeExpr.Type = Type.Bool;
      return new List<Cmd> { CmdHelper.AssumeCmd(assumeExpr) };
    }

    public override List<Cmd> CreateActionEvaluationCmds()
    {
      // eval := transitionRelation(i, g_old, o, g);
      if (civlTypeChecker.Options.TrustRefinement)
      {
        return new List<Cmd>();
      }
      return new List<Cmd> { CmdHelper.AssignCmd(eval, transitionRelation) };
    }
    
    public override List<Cmd> CreateAssertCmds()
    {
      // assert pc ==> g_old == g && o_old == o;
      AssertCmd skipAssertCmd = CmdHelper.AssertCmd(
        tok,
        Expr.Imp(Expr.Ident(pc), Expr.And(OldEqualityExprForGlobals(), OldEqualityExprForOutputs())),
        $"A yield-to-yield fragment modifies layer-{layerNum + 1} state subsequent to a yield-to-yield fragment that already modified layer-{layerNum + 1} state");
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, skipAssertCmd);
      if (civlTypeChecker.Options.TrustRefinement)
      {
        return new List<Cmd> { skipAssertCmd };
      }

      // assert pc || g_old == g || eval;
      var skipOrTransitionRelationAssertCmd = CmdHelper.AssertCmd(
        tok,
        Expr.Or(Expr.Ident(pc), Expr.Or(OldEqualityExprForGlobals(), Expr.Ident(eval))),
        $"A yield-to-yield fragment modifies layer-{layerNum + 1} state in a way that does not match the refined atomic action");
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, skipOrTransitionRelationAssertCmd);
      return new List<Cmd> { skipOrTransitionRelationAssertCmd, skipAssertCmd };
    }

    public override List<Cmd> CreateReturnAssertCmds()
    {
      if (civlTypeChecker.Options.TrustRefinement)
      {
        return new List<Cmd>();
      }
      AssertCmd assertCmd = CmdHelper.AssertCmd(
        tok,
        Expr.Ident(ok),
        "On some path no yield-to-yield fragment matched the refined atomic action");
      return new List<Cmd> { assertCmd };
    }

    public override List<Cmd> CreateUnchangedAssertCmds()
    {
      AssertCmd globalsAssertCmd = CmdHelper.AssertCmd(
        tok,
        Expr.And(this.oldGlobalMap.Select(kvPair => Expr.Eq(Expr.Ident(kvPair.Key), Expr.Ident(kvPair.Value)))),
        $"A yield-to-yield fragment illegally modifies layer-{layerNum + 1} globals");
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, globalsAssertCmd);

      // assert pc ==> o_old == o;
      AssertCmd outputsAssertCmd = CmdHelper.AssertCmd(
        tok,
        Expr.Imp(Expr.Ident(pc), OldEqualityExprForOutputs()),
        $"A yield-to-yield fragment illegally modifies layer-{layerNum + 1} outputs");
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, outputsAssertCmd);

      return new List<Cmd> { globalsAssertCmd, outputsAssertCmd };
    }

    public override List<Cmd> CreateUpdatesToRefinementVars(bool isMarkedCall)
    {
      var cmds = new List<Cmd>();
      var pcOkUpdateLHS = new List<IdentifierExpr> { Expr.Ident(pc) };
      if (!civlTypeChecker.Options.TrustRefinement)
      {
        pcOkUpdateLHS.Add(Expr.Ident(ok));
      }
      if (isMarkedCall)
      {
        // assert !pc;
        // pc, ok := true, true;
        cmds.Add(CmdHelper.AssertCmd(tok, Expr.Not(Expr.Ident(pc)), $"Layer-{layerNum + 1} state modified before marked call"));
        var pcOkUpdateRHS = new List<Expr> { Expr.True };
        if (!civlTypeChecker.Options.TrustRefinement)
        {
          pcOkUpdateRHS.Add(Expr.True);
        }
        cmds.Add(CmdHelper.AssignCmd(pcOkUpdateLHS, pcOkUpdateRHS));
      }
      else
      {
        // pc, ok := g_old == g ==> pc, eval || (o_old == o && ok);
        var pcOkUpdateRHS = new List<Expr> {
          Expr.Imp(OldEqualityExprForGlobals(), Expr.Ident(pc))
        };
        if (!civlTypeChecker.Options.TrustRefinement)
        {
          pcOkUpdateRHS.Add(Expr.Or(Expr.Ident(eval), Expr.And(OldEqualityExprForOutputs(), Expr.Ident(ok))));
        }
        cmds.Add(CmdHelper.AssignCmd(pcOkUpdateLHS, pcOkUpdateRHS));
      }

      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, cmds);

      return cmds;
    }

    public override List<Cmd> CreateUpdatesToOldOutputVars()
    {
      var lhss = new List<IdentifierExpr>();
      var rhss = new List<Expr>();
      foreach (Variable o in oldOutputMap.Keys)
      {
        lhss.Add(Expr.Ident(oldOutputMap[o]));
        rhss.Add(Expr.Ident(o));
      }
      if (lhss.Count > 0)
      {
        return new List<Cmd> { CmdHelper.AssignCmd(lhss,rhss) };
      }
      return new List<Cmd>();
    }

    private Expr GetTransitionRelation(AtomicAction atomicAction)
    {
      if (!transitionRelationCache.ContainsKey(atomicAction))
      {
        transitionRelationCache[atomicAction] =
          TransitionRelationComputation.Refinement(civlTypeChecker, atomicAction, new HashSet<Variable>(this.oldGlobalMap.Keys));
      }
      return transitionRelationCache[atomicAction];
    }

    private Expr OldEqualityExprForGlobals()
    {
      return Expr.And(this.oldGlobalMap.Select(kvPair => Expr.Eq(Expr.Ident(kvPair.Key), Expr.Ident(kvPair.Value))));
    }

    private Expr OldEqualityExprForOutputs()
    {
      return Expr.And(this.oldOutputMap.Select(kvPair => Expr.Eq(Expr.Ident(kvPair.Key), Expr.Ident(kvPair.Value))));
    }

    private LocalVariable Old(Variable v)
    {
      return civlTypeChecker.LocalVariable($"old_{v.Name}", v.TypedIdent.Type);
    }
  }
}