using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public abstract class Action
  {
    public Implementation Impl;
    public List<AssertCmd> Gate;
    public HashSet<Variable> UsedGlobalVarsInGate;
    public HashSet<Variable> UsedGlobalVarsInAction;
    public HashSet<Variable> ModifiedGlobalVars;
    public List<ActionDecl> PendingAsyncs;
    public Function InputOutputRelation;

    protected Action(Implementation impl, CivlTypeChecker civlTypeChecker)
    {
      this.Impl = impl;
      
      // We usually declare the Boogie procedure and implementation of an atomic action together.
      // Since Boogie only stores the supplied attributes (in particular linearity) in the procedure parameters,
      // we copy them into the implementation parameters here.
      for (int i = 0; i < ActionDecl.InParams.Count; i++)
      {
        impl.InParams[i].Attributes = ActionDecl.InParams[i].Attributes;
      }

      for (int i = 0; i < ActionDecl.OutParams.Count; i++)
      {
        impl.OutParams[i].Attributes = ActionDecl.OutParams[i].Attributes;
      }
      
      this.PendingAsyncs = ActionDecl.Creates.Select(x => x.ActionDecl).ToList();
      var lhss = new List<IdentifierExpr>();
      var rhss = new List<Expr>();
      PendingAsyncs.Iter(decl =>
      {
        var pa = civlTypeChecker.Formal($"PAs_{decl.Name}", decl.PendingAsyncMultisetType, false);
        impl.OutParams.Add(pa);
        ActionDecl.OutParams.Add(pa);
        lhss.Add(Expr.Ident(pa));
        rhss.Add(ExprHelper.FunctionCall(decl.PendingAsyncConst, Expr.Literal(0)));
        var paLocal = civlTypeChecker.LocalVariable($"local_PAs_{decl.Name}", decl.PendingAsyncMultisetType);
        impl.LocVars.Add(paLocal);
      });
      if (PendingAsyncs.Any())
      {
        var tc = new TypecheckingContext(null, civlTypeChecker.Options);
        var assignCmd = CmdHelper.AssignCmd(lhss, rhss);
        assignCmd.Typecheck(tc);
        impl.Blocks[0].Cmds.Insert(0, assignCmd);
      }
      DesugarCreateAsyncs(civlTypeChecker);
    }

    public ActionDecl ActionDecl => (ActionDecl)Impl.Proc;
    
    public LayerRange LayerRange => ActionDecl.LayerRange;

    public int LowerLayer => LayerRange.LowerLayer;

    public bool HasPendingAsyncs => PendingAsyncs.Count > 0;

    public Variable PAs(CtorType pendingAsyncType)
    {
      var pendingAsyncMultisetType = TypeHelper.MapType(pendingAsyncType, Type.Int);
      return Impl.OutParams.Skip(ActionDecl.PendingAsyncStartIndex).First(v => v.TypedIdent.Type.Equals(pendingAsyncMultisetType));
    }

    public Variable LocalPAs(CtorType pendingAsyncType)
    {
      var pendingAsyncMultisetType = TypeHelper.MapType(pendingAsyncType, Type.Int);
      return Impl.LocVars.Last(v => v.TypedIdent.Type.Equals(pendingAsyncMultisetType));
    }
    
    public bool HasAssumeCmd => Impl.Blocks.Any(b => b.Cmds.Any(c => c is AssumeCmd));

    // The flag initializeInputOutputRelation is added just so the Boogie function representing the input-output relation
    // of SkipAtomicAction (not needed) is not injected into TopLevelDeclarations. This trick ensures that if the input
    // program does not use Civl features then the program is not modified.
    public virtual void CompleteInitialization(CivlTypeChecker civlTypeChecker, bool initializeInputOutputRelation = false)
    {
      Gate = HoistAsserts(Impl, civlTypeChecker.Options);
      UsedGlobalVarsInGate = new HashSet<Variable>(VariableCollector.Collect(Gate).Where(x => x is GlobalVariable));
      UsedGlobalVarsInAction = new HashSet<Variable>(VariableCollector.Collect(Impl).Where(x => x is GlobalVariable));
      ModifiedGlobalVars = new HashSet<Variable>(ActionDecl.Modifies.Select(x => x.Decl));

      if (initializeInputOutputRelation)
      {
        var alwaysMap = new Dictionary<Variable, Expr>();
        var foroldMap = new Dictionary<Variable, Expr>();
        civlTypeChecker.program.GlobalVariables.Iter(g =>
        {
          alwaysMap[g] = Expr.Ident(civlTypeChecker.BoundVariable(g.Name, g.TypedIdent.Type));
          foroldMap[g] = Expr.Ident(civlTypeChecker.BoundVariable($"old_{g.Name}", g.TypedIdent.Type));
        });
        Impl.InParams.Concat(Impl.OutParams).Iter(v =>
        {
          alwaysMap[v] = Expr.Ident(VarHelper.Formal(v.Name, v.TypedIdent.Type, true));
        });
        var always = Substituter.SubstitutionFromDictionary(alwaysMap);
        var forold = Substituter.SubstitutionFromDictionary(foroldMap);
        var transitionRelationExpr =
          Substituter.ApplyReplacingOldExprs(always, forold,
            TransitionRelationComputation.Refinement(civlTypeChecker, this, new HashSet<Variable>(ModifiedGlobalVars)));
        var gateExprs = Gate.Select(assertCmd =>
          Substituter.ApplyReplacingOldExprs(always, forold, ExprHelper.Old(assertCmd.Expr)));
        var transitionRelationInputs = Impl.InParams.Concat(Impl.OutParams)
          .Select(key => alwaysMap[key]).OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList();
        InputOutputRelation = new Function(Token.NoToken, $"Civl_InputOutputRelation_{ActionDecl.Name}",
          new List<TypeVariable>(),
          transitionRelationInputs, VarHelper.Formal(TypedIdent.NoName, Type.Bool, false), null,
          new QKeyValue(Token.NoToken, "inline", new List<object>(), null));
        var existsVars = foroldMap.Values
          .Concat(alwaysMap.Keys.Where(key => key is GlobalVariable).Select(key => alwaysMap[key]))
          .OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList();
        InputOutputRelation.Body =
          ExprHelper.ExistsExpr(existsVars, Expr.And(gateExprs.Append(transitionRelationExpr)));
        CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, InputOutputRelation.Body);
        civlTypeChecker.program.AddTopLevelDeclaration(InputOutputRelation);
      }
    }

    private void DesugarCreateAsyncs(CivlTypeChecker civlTypeChecker)
    {
      Impl.Blocks.Iter(block =>
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd)
          {
            var originalProc = (Procedure)civlTypeChecker.program.monomorphizer.GetOriginalDecl(callCmd.Proc);
            if (originalProc.Name == "create_async" || originalProc.Name == "create_asyncs" || originalProc.Name == "create_multi_asyncs")
            {
              var pendingAsyncType =
                (CtorType)civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
              var pendingAsync = PendingAsyncs.First(decl => decl.PendingAsyncType.Equals(pendingAsyncType));
              var tc = new TypecheckingContext(null, civlTypeChecker.Options);
              var pendingAsyncMultiset = originalProc.Name == "create_async"
                ? Expr.Store(ExprHelper.FunctionCall(pendingAsync.PendingAsyncConst, Expr.Literal(0)), callCmd.Ins[0],
                  Expr.Literal(1))
                : originalProc.Name == "create_asyncs"
                  ? ExprHelper.FunctionCall(pendingAsync.PendingAsyncIte, callCmd.Ins[0],
                    ExprHelper.FunctionCall(pendingAsync.PendingAsyncConst, Expr.Literal(1)),
                    ExprHelper.FunctionCall(pendingAsync.PendingAsyncConst, Expr.Literal(0)))
                  : callCmd.Ins[0];
              var assignCmd = CmdHelper.AssignCmd(PAs(pendingAsyncType),
                ExprHelper.FunctionCall(pendingAsync.PendingAsyncAdd, Expr.Ident(PAs(pendingAsyncType)),
                  pendingAsyncMultiset));
              assignCmd.Typecheck(tc);
              newCmds.Add(assignCmd);
              continue;
            }
            if (callCmd.Proc is ActionDecl actionDecl)
            {
              newCmds.Add(callCmd);
              actionDecl.Creates.Iter(actionDeclRef =>
              {
                var pendingAsync = actionDeclRef.ActionDecl;
                var pendingAsyncType = pendingAsync.PendingAsyncType;
                callCmd.Outs.Add(Expr.Ident(LocalPAs(pendingAsyncType)));
                var assignCmd = CmdHelper.AssignCmd(PAs(pendingAsyncType),
                  ExprHelper.FunctionCall(pendingAsync.PendingAsyncAdd, Expr.Ident(PAs(pendingAsyncType)),
                    Expr.Ident(LocalPAs(pendingAsyncType))));
                newCmds.Add(assignCmd);
              });
              continue;
            }
          }
          newCmds.Add(cmd);
        }
        block.Cmds = newCmds;
      });
    }
    
    /*
     * HoistAsserts computes the weakest liberal precondition (wlp) of the body
     * of impl as a collection of AssertCmd's. As a side effect, all AssertCmd's
     * in any block of impl are removed.
     *
     * HoistAsserts assumes that the body of impl does not contain any loops or
     * calls. The blocks in impl are sorted from entry to exit and processed in
     * reverse order, thus ensuring that a block is processed only once the wlp
     * of all its successors has been computed.
     */
    private List<AssertCmd> HoistAsserts(Implementation impl, ConcurrencyOptions options)
    {
      Dictionary<Block, List<AssertCmd>> wlps = new Dictionary<Block, List<AssertCmd>>();
      Graph<Block> dag = Program.GraphFromBlocks(impl.Blocks, false);
      foreach (var block in dag.TopologicalSort())
      {
        if (block.TransferCmd is ReturnCmd)
        {
          var wlp = HoistAsserts(block.Cmds, new List<AssertCmd>(), options);
          wlps.Add(block, wlp);
        }
        else if (block.TransferCmd is GotoCmd gotoCmd)
        {
          var wlp =
            HoistAsserts(block.Cmds, gotoCmd.labelTargets.SelectMany(b => wlps[b]).ToList(), options);
          wlps.Add(block, wlp);
        }
        else
        {
          throw new cce.UnreachableException();
        }
      }
      return wlps[impl.Blocks[0]].Select(assertCmd => Forall(impl.LocVars.Union(impl.OutParams), assertCmd)).ToList();
    }

    private List<AssertCmd> HoistAsserts(List<Cmd> cmds, List<AssertCmd> postconditions, ConcurrencyOptions options)
    {
      for (int i = cmds.Count - 1; i >= 0; i--)
      {
        var cmd = cmds[i];
        if (cmd is AssertCmd assertCmd)
        {
          postconditions.Add(assertCmd);
        } 
        else if (cmd is AssumeCmd assumeCmd)
        {
          postconditions = postconditions
            .Select(assertCmd => new AssertCmd(assertCmd.tok, Expr.Imp(assumeCmd.Expr, assertCmd.Expr))).ToList();
        }
        else if (cmd is AssignCmd assignCmd)
        {
          var varToExpr = new Dictionary<Variable, Expr>();
          var simpleAssignCmd = assignCmd.AsSimpleAssignCmd;
          for (var j = 0; j < simpleAssignCmd.Lhss.Count; j++)
          {
            var lhs = simpleAssignCmd.Lhss[j];
            var rhs = simpleAssignCmd.Rhss[j];
            varToExpr.Add(lhs.DeepAssignedVariable, rhs);
          }
          postconditions = postconditions.Select(assertCmd =>
            new AssertCmd(assertCmd.tok, SubstitutionHelper.Apply(varToExpr, assertCmd.Expr))).ToList();
        }
        else if (cmd is HavocCmd havocCmd)
        {
          postconditions = postconditions.Select(assertCmd => Forall(havocCmd.Vars.Select(ie => ie.Decl), assertCmd))
            .ToList();
        }
        else if (cmd is UnpackCmd unpackCmd)
        {
          var desugaredCmd = (StateCmd) unpackCmd.GetDesugaring(options);
          postconditions = HoistAsserts(desugaredCmd.Cmds, postconditions, options); // removes precondition assert from desugaredCmd.Cmds
        }
        else
        {
          throw new cce.UnreachableException();
        }
      }
      cmds.RemoveAll(cmd => cmd is AssertCmd);
      return postconditions;
    }
    
    private static AssertCmd Forall(IEnumerable<Variable> vars, AssertCmd assertCmd)
    {
      var freeObjects = new GSet<object>();
      assertCmd.Expr.ComputeFreeVariables(freeObjects);
      var quantifiedVars = freeObjects.OfType<Variable>().Intersect(vars);
      if (quantifiedVars.Count() == 0)
      {
        return assertCmd;
      }
      var varMapping = quantifiedVars.ToDictionary(v => v,
        v => (Variable) VarHelper.BoundVariable(v.Name, v.TypedIdent.Type));
      return new AssertCmd(assertCmd.tok,
        ExprHelper.ForallExpr(varMapping.Values.ToList(), SubstitutionHelper.Apply(varMapping, assertCmd.Expr)));
    }
  }

  public class AtomicAction : Action
  {
    public AtomicAction RefinedAction;

    public List<AssertCmd> FirstGate;
    public Implementation FirstImpl;
    public List<AssertCmd> SecondGate;
    public Implementation SecondImpl;
    
    public Dictionary<Variable, Function> TriggerFunctions;

    public AtomicAction(Implementation impl, AtomicAction refinedAction, CivlTypeChecker civlTypeChecker) : base(impl, civlTypeChecker)
    {
      this.RefinedAction = refinedAction;
    }

    public override void CompleteInitialization(CivlTypeChecker civlTypeChecker, bool initializeInputOutputRelation = false)
    {
      base.CompleteInitialization(civlTypeChecker, initializeInputOutputRelation);

      AtomicActionDuplicator.SetupCopy(this, ref FirstGate, ref FirstImpl, "first_");
      AtomicActionDuplicator.SetupCopy(this, ref SecondGate, ref SecondImpl, "second_");
      DeclareTriggerFunctions();
    }

    public bool IsRightMover => ActionDecl.MoverType == MoverType.Right || ActionDecl.MoverType == MoverType.Both;

    public bool IsLeftMover => ActionDecl.MoverType == MoverType.Left || ActionDecl.MoverType == MoverType.Both;

    public bool TriviallyCommutesWith(AtomicAction other)
    {
      return !this.ModifiedGlobalVars.Intersect(other.UsedGlobalVarsInAction).Any() &&
             !this.UsedGlobalVarsInAction.Intersect(other.ModifiedGlobalVars).Any();
    }

    private void DeclareTriggerFunctions()
    {
      TriggerFunctions = new Dictionary<Variable, Function>();
      foreach (var v in Impl.LocVars)
      {
        List<Variable> args = new List<Variable> {VarHelper.Formal(v.Name, v.TypedIdent.Type, true)};
        Variable result = VarHelper.Formal("r", Type.Bool, false);
        TriggerFunctions[v] = new Function(Token.NoToken, $"Trigger_{Impl.Name}_{v.Name}", args, result);
      }

      for (int i = 0; i < Impl.LocVars.Count; i++)
      {
        TriggerFunctions[FirstImpl.LocVars[i]] = TriggerFunctions[Impl.LocVars[i]];
        TriggerFunctions[SecondImpl.LocVars[i]] = TriggerFunctions[Impl.LocVars[i]];
      }
    }

    /*
     * This method adds triggers for each local variable at the beginning of the atomic
     * action and after every havoc of the variable.
     * As an optimization, the injection of the trigger is performed only if the variable
     * is live at the point of injection.
     */
    public void AddTriggerAssumes(Program program, ConcurrencyOptions options)
    {
      var liveVariableAnalysis = new AtomicActionLiveVariableAnalysis(Impl, options);
      liveVariableAnalysis.Compute();
      foreach (Variable v in Impl.LocVars)
      {
        var f = TriggerFunctions[v];
        program.AddTopLevelDeclaration(f);
        if (liveVariableAnalysis.IsLiveBefore(v, Impl.Blocks[0]))
        {
          var assume = CmdHelper.AssumeCmd(ExprHelper.FunctionCall(f, Expr.Ident(v)));
          Impl.Blocks[0].Cmds.Insert(0, assume);
        }
      }
      Impl.Blocks.Iter(block =>
      {
        block.Cmds = block.Cmds.SelectMany(cmd =>
        {
          var newCmds = new List<Cmd> { cmd };
          if (cmd is HavocCmd havocCmd)
          {
            var liveHavocVars = new HashSet<Variable>(havocCmd.Vars.Select(x => x.Decl)
              .Where(v => liveVariableAnalysis.IsLiveAfter(v, havocCmd)));
            Impl.LocVars.Intersect(liveHavocVars).Iter(v =>
            {
              newCmds.Add(CmdHelper.AssumeCmd(ExprHelper.FunctionCall(TriggerFunctions[v], Expr.Ident(v))));
            });
          }
          return newCmds;
        }).ToList();
      });
    }
  }

  public class InvariantAction : Action
  {
    public DatatypeTypeCtorDecl ChoiceDatatypeTypeCtorDecl;

    public InvariantAction(Implementation impl, CivlTypeChecker civlTypeChecker) : base(impl, civlTypeChecker)
    {
      var choiceDatatypeName = $"Choice_{impl.Name}";
      ChoiceDatatypeTypeCtorDecl =
        new DatatypeTypeCtorDecl(Token.NoToken, choiceDatatypeName, new List<TypeVariable>(), null);
      PendingAsyncs.Iter(elim =>
      {
        var field = new TypedIdent(Token.NoToken, elim.Name, elim.PendingAsyncType);
        ChoiceDatatypeTypeCtorDecl.AddConstructor(Token.NoToken, $"{choiceDatatypeName}_{elim.Name}",
          new List<TypedIdent>() { field });
      });
      civlTypeChecker.program.AddTopLevelDeclaration(ChoiceDatatypeTypeCtorDecl);
      var choice = VarHelper.Formal("choice", TypeHelper.CtorType(ChoiceDatatypeTypeCtorDecl), false);
      impl.OutParams.Add(choice);
      ActionDecl.OutParams.Add(choice);
      DesugarSetChoice(civlTypeChecker, choice);
    }

    public DatatypeConstructor ChoiceConstructor(CtorType pendingAsyncType)
    {
      return ChoiceDatatypeTypeCtorDecl.Constructors.First(x => x.InParams[0].TypedIdent.Type.Equals(pendingAsyncType));
    }
    
    private void DesugarSetChoice(CivlTypeChecker civlTypeChecker, Variable choice)
    {
      Impl.Blocks.Iter(block =>
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd)
          {
            var originalProc = (Procedure)civlTypeChecker.program.monomorphizer.GetOriginalDecl(callCmd.Proc);
            if (originalProc.Name == "set_choice")
            {
              var pendingAsyncType = (CtorType)civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
              var pendingAsync = PendingAsyncs.First(decl => decl.PendingAsyncType.Equals(pendingAsyncType));
              var tc = new TypecheckingContext(null, civlTypeChecker.Options);
              var emptyExpr = Expr.Eq(Expr.Ident(PAs(pendingAsyncType)),
                ExprHelper.FunctionCall(pendingAsync.PendingAsyncConst, Expr.Literal(0)));
              var memberExpr = Expr.Gt(Expr.Select(Expr.Ident(PAs(pendingAsyncType)), callCmd.Ins[0]),
                Expr.Literal(0));
              var assertCmd = CmdHelper.AssertCmd(cmd.tok, Expr.Or(emptyExpr, memberExpr),
                "Choice is not a created pending async");
              assertCmd.Typecheck(tc);
              newCmds.Add(assertCmd);
              var assignCmd = CmdHelper.AssignCmd(CmdHelper.FieldAssignLhs(Expr.Ident(choice), pendingAsyncType.Decl.Name), callCmd.Ins[0]);
              assignCmd.Typecheck(tc);
              newCmds.Add(assignCmd);
              continue;
            }
          }
          newCmds.Add(cmd);
        }
        block.Cmds = newCmds;
      });
    }
  }

  public class YieldingLoop
  {
    public int Layer;
    public List<CallCmd> YieldInvariants;

    public YieldingLoop(int layer, List<CallCmd> yieldInvariants)
    {
      this.Layer = layer;
      this.YieldInvariants = yieldInvariants;
    }
  }

  public abstract class YieldingProc
  {
    public YieldProcedureDecl Proc;

    public YieldingProc(YieldProcedureDecl proc)
    {
      this.Proc = proc;
    }

    public int Layer => Proc.Layer;
    
    public abstract MoverType MoverType { get; }

    public bool IsRightMover => MoverType == MoverType.Right || MoverType == MoverType.Both;

    public bool IsLeftMover => MoverType == MoverType.Left || MoverType == MoverType.Both;
  }

  public class MoverProc : YieldingProc
  {
    public MoverProc(YieldProcedureDecl proc) : base(proc)
    {
    }

    public override MoverType MoverType => Proc.MoverType;
    
    public IEnumerable<Variable> ModifiedVars => Proc.ModifiedVars;
  }

  public class ActionProc : YieldingProc
  {
    public AtomicAction RefinedAction;

    public ActionProc(YieldProcedureDecl proc, AtomicAction refinedAction) : base(proc)
    {
      this.RefinedAction = refinedAction;
    }

    public HashSet<Variable> HiddenFormals => Proc.HiddenFormals;

    public override MoverType MoverType => RefinedAction.ActionDecl.MoverType;
  }

  /// <summary>
  /// Creates first/second copies of atomic actions used in commutativity checks
  /// (i.e., all non-global variables are prefixed with first_ resp. second_).
  /// Note that we also rename bound variables.
  /// </summary>
  class AtomicActionDuplicator : Duplicator
  {
    private readonly string prefix;
    private Dictionary<Variable, Expr> subst;
    private Dictionary<Variable, Expr> bound;
    private List<Variable> inParamsCopy;
    private List<Variable> outParamsCopy;
    private List<Variable> localsCopy;

    public static void SetupCopy(AtomicAction action, ref List<AssertCmd> gateCopy, ref Implementation implCopy,
      string prefix)
    {
      var aad = new AtomicActionDuplicator(prefix, action);

      gateCopy = new List<AssertCmd>();
      foreach (AssertCmd assertCmd in action.Gate)
      {
        gateCopy.Add((AssertCmd) aad.Visit(assertCmd));
      }

      implCopy = aad.VisitImplementation(action.Impl);
    }

    private AtomicActionDuplicator(string prefix, AtomicAction action)
    {
      this.prefix = prefix;
      subst = new Dictionary<Variable, Expr>();
      bound = new Dictionary<Variable, Expr>();

      inParamsCopy = new List<Variable>();
      outParamsCopy = new List<Variable>();
      localsCopy = new List<Variable>();


      foreach (Variable x in action.Impl.InParams)
      {
        Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          true, x.Attributes);
        inParamsCopy.Add(xCopy);
        subst[x] = Expr.Ident(xCopy);
      }

      foreach (Variable x in action.Impl.OutParams)
      {
        Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          false, x.Attributes);
        outParamsCopy.Add(xCopy);
        subst[x] = Expr.Ident(xCopy);
      }

      foreach (Variable x in action.Impl.LocVars)
      {
        Variable xCopy = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), x.Attributes);
        subst[x] = Expr.Ident(xCopy);
        localsCopy.Add(xCopy);
      }
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      node = base.VisitImplementation(node);
      node.InParams = inParamsCopy;
      node.OutParams = outParamsCopy;
      node.LocVars = localsCopy;
      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (subst.ContainsKey(node.Decl))
      {
        return subst[node.Decl];
      }
      else if (bound.ContainsKey(node.Decl))
      {
        return bound[node.Decl];
      }

      return base.VisitIdentifierExpr(node);
    }

    public override BinderExpr VisitBinderExpr(BinderExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          x.Attributes));

      foreach (var x in node.Dummies)
      {
        bound.Add(x, Expr.Ident(oldToNew[x]));
      }

      var expr = (BinderExpr)base.VisitBinderExpr(node);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();

      // We process triggers of quantifier expressions here, because otherwise the
      // substitutions for bound variables have to be leaked outside this procedure.
      if (node is QuantifierExpr quantifierExpr)
      {
        if (quantifierExpr.Triggers != null)
        {
          ((QuantifierExpr) expr).Triggers = this.VisitTrigger(quantifierExpr.Triggers);
        }
      }

      foreach (var x in node.Dummies)
      {
        bound.Remove(x);
      }

      return expr;
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      // Don't remove this implementation! Triggers should be duplicated in VisitBinderExpr.
      return (QuantifierExpr) this.VisitBinderExpr(node);
    }
  }
}