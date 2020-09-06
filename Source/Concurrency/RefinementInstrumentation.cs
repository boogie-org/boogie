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

    public virtual List<Cmd> CreateAssertCmds()
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateReturnAssertCmds()
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateUnchangedGlobalsAssertCmds()
    {
      return new List<Cmd>();
    }

    public virtual List<Cmd> CreateUnchangedOutputsAssertCmds()
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
    private Expr gate;
    private Expr transitionRelation;

    private Dictionary<AtomicAction, Expr> transitionRelationCache;

    public ActionRefinementInstrumentation(
      CivlTypeChecker civlTypeChecker,
      Implementation impl,
      Implementation originalImpl,
      Dictionary<Variable, Variable> oldGlobalMap)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.oldGlobalMap = new Dictionary<Variable, Variable>();
      ActionProc actionProc = civlTypeChecker.procToYieldingProc[originalImpl.Proc] as ActionProc;
      int layerNum = actionProc.upperLayer;
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
      ok = civlTypeChecker.LocalVariable("ok", Type.Bool);
      newLocalVars.Add(ok);

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

      Substitution always = Substituter.SubstitutionFromHashtable(alwaysMap);
      Substitution forold = Substituter.SubstitutionFromHashtable(foroldMap);
      Expr transitionRelationExpr = GetTransitionRelation(atomicAction);
      transitionRelation = Substituter.ApplyReplacingOldExprs(always, forold, transitionRelationExpr);
      Expr gateExpr = Expr.And(atomicAction.gate.Select(g => g.Expr));
      gateExpr.Type = Type.Bool;
      gate = Substituter.Apply(always, gateExpr);
    }

    public override List<Variable> NewLocalVars => newLocalVars;

    public override List<Cmd> CreateInitCmds()
    {
      List<AssignLhs> lhss = new List<AssignLhs>
      {
        new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)),
        new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok))
      };
      List<Expr> rhss = new List<Expr> {Expr.False, Expr.False};
      var cmds = new List<Cmd> {new AssignCmd(Token.NoToken, lhss, rhss)};
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
      return new List<Cmd> {new AssumeCmd(Token.NoToken, assumeExpr)};
    }

    public override List<Cmd> CreateAssertCmds()
    {
      Expr assertExpr;

      // assert pc || g_old == g || transitionRelation(i, g_old, o, g);
      assertExpr = Expr.Or(Expr.Ident(pc), Expr.Or(OldEqualityExprForGlobals(), transitionRelation));
      assertExpr.Typecheck(new TypecheckingContext(null));
      var skipOrTransitionRelationAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
      skipOrTransitionRelationAssertCmd.ErrorData = "Transition invariant violated in initial state";

      // assert pc ==> g_old == g && o_old == o;
      assertExpr = Expr.Imp(Expr.Ident(pc), Expr.And(OldEqualityExprForGlobals(), OldEqualityExprForOutputs()));
      assertExpr.Typecheck(new TypecheckingContext(null));
      AssertCmd skipAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
      skipAssertCmd.ErrorData = "Transition invariant violated in final state";
      return new List<Cmd> {skipOrTransitionRelationAssertCmd, skipAssertCmd};
    }

    public override List<Cmd> CreateReturnAssertCmds()
    {
      AssertCmd assertCmd = new AssertCmd(Token.NoToken, Expr.Ident(ok));
      assertCmd.ErrorData = "Failed to execute atomic action before procedure return";
      return new List<Cmd> {assertCmd};
    }

    public override List<Cmd> CreateUnchangedGlobalsAssertCmds()
    {
      var assertExpr =
        Expr.And(this.oldGlobalMap.Select(kvPair => Expr.Eq(Expr.Ident(kvPair.Key), Expr.Ident(kvPair.Value))));
      assertExpr.Typecheck(new TypecheckingContext(null));
      AssertCmd skipAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
      skipAssertCmd.ErrorData = "Globals must not be modified";
      return new List<Cmd> {skipAssertCmd};
    }

    public override List<Cmd> CreateUnchangedOutputsAssertCmds()
    {
      // assert pc ==> o_old == o;
      var assertExpr = Expr.Imp(Expr.Ident(pc), OldEqualityExprForOutputs());
      assertExpr.Typecheck(new TypecheckingContext(null));
      AssertCmd skipAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
      skipAssertCmd.ErrorData = "Outputs must not be modified";
      return new List<Cmd> {skipAssertCmd};
    }

    public override List<Cmd> CreateUpdatesToRefinementVars(bool isMarkedCall)
    {
      var cmds = new List<Cmd>();
      List<AssignLhs> pcOkUpdateLHS = new List<AssignLhs>
      {
        new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)),
        new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok))
      };
      if (isMarkedCall)
      {
        // assert !pc;
        // pc, ok := true, true;
        cmds.Add(new AssertCmd(Token.NoToken, Expr.Not(Expr.Ident(pc))));
        List<Expr> pcOkUpdateRHS = new List<Expr>(new Expr[] {Expr.True, Expr.True});
        cmds.Add(new AssignCmd(Token.NoToken, pcOkUpdateLHS, pcOkUpdateRHS));
      }
      else
      {
        // pc, ok := g_old == g ==> pc, transitionRelation(i, g_old, o, g) || (o_old == o && ok);
        List<Expr> pcOkUpdateRHS = new List<Expr>(
          new Expr[]
          {
            Expr.Imp(OldEqualityExprForGlobals(), Expr.Ident(pc)),
            Expr.Or(transitionRelation, Expr.And(OldEqualityExprForOutputs(), Expr.Ident(ok))),
          });
        cmds.Add(new AssignCmd(Token.NoToken, pcOkUpdateLHS, pcOkUpdateRHS));
      }

      foreach (var cmd in cmds)
      {
        cmd.Typecheck(new TypecheckingContext(null));
      }

      return cmds;
    }

    public override List<Cmd> CreateUpdatesToOldOutputVars()
    {
      List<AssignLhs> lhss = new List<AssignLhs>();
      List<Expr> rhss = new List<Expr>();
      foreach (Variable o in oldOutputMap.Keys)
      {
        lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldOutputMap[o])));
        rhss.Add(Expr.Ident(o));
      }

      return lhss.Count > 0 ? new List<Cmd> {new AssignCmd(Token.NoToken, lhss, rhss)} : new List<Cmd>();
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