using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public enum InductiveSequentializationRule
  {
    ISL,
    ISR
  }

  public abstract class Sequentialization
  {
    protected CivlTypeChecker civlTypeChecker;
    protected Action targetAction;
    protected HashSet<Action> eliminatedActions;

    public InductiveSequentializationRule rule;

    protected Sequentialization(CivlTypeChecker civlTypeChecker, Action targetAction)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.targetAction = targetAction;
      this.eliminatedActions = new HashSet<Action>(EliminatedActionDecls.Select(x => civlTypeChecker.Action(x)));
      if (targetAction.ActionDecl.RefinedAction.HasAttribute(CivlAttributes.IS_RIGHT))
      {
        rule = InductiveSequentializationRule.ISR;
      }
      else
      {
        rule = InductiveSequentializationRule.ISL;
      }
    }

    public IEnumerable<ActionDecl> EliminatedActionDecls => targetAction.ActionDecl.EliminatedActionDecls();

    public IEnumerable<Action> EliminatedActions => eliminatedActions;

    public int Layer => targetAction.LayerRange.UpperLayer;
    public Action TargetAction => targetAction;
    protected virtual List<Declaration> GenerateCheckers()
    {
      var decls = new List<Declaration>();
      if (rule == InductiveSequentializationRule.ISR)
      {
        decls.AddRange(GeneratePartitionChecker(targetAction));
        foreach (var elim in eliminatedActions)
        {
          if (elim == targetAction)
          {
            continue;
          }
          decls.AddRange(GeneratePartitionChecker(elim));
        }
      }
      return decls;
    }

    public virtual IEnumerable<Expr> GenerateMoverCheckAssumptions(Action action, List<Variable> actionArgs, Action leftMover,
      List<Variable> leftMoverArgs)
    {
      return new List<Expr>();
    }

    public IEnumerable<AssertCmd> Preconditions(Action pendingAsync, Substitution subst)
    {
      var cmds = new List<AssertCmd>();
      pendingAsync.ActionDecl.Requires.Where(req => req.Layers.Contains(Layer)).ForEach(req =>
      {
        cmds.Add(CmdHelper.AssertCmd(req.tok, Substituter.Apply(subst, req.Condition), ""));
      });
      foreach (var callCmd in pendingAsync.ActionDecl.YieldRequires)
      {
        var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
        if (Layer == yieldInvariant.Layer)
        {
          Substitution callFormalsToActuals = Substituter.SubstitutionFromDictionary(yieldInvariant.InParams
              .Zip(callCmd.Ins)
              .ToDictionary(x => x.Item1, x => x.Item2));
          yieldInvariant.Requires.ForEach(req =>
            cmds.Add(CmdHelper.AssertCmd(req.tok,
                  Substituter.Apply(subst, Substituter.Apply(callFormalsToActuals, req.Condition)), "")));
        }
      }
      return cmds;
    }

    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      foreach (var x in civlTypeChecker.Sequentializations)
      {
        decls.AddRange(x.GenerateCheckers());
      }
    }

    protected AssertCmd GetCheck(IToken tok, Expr expr, string msg)
    {
      expr.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
      return CmdHelper.AssertCmd(tok, expr, msg);
    }

    protected List<Declaration> GeneratePartitionChecker(Action action)
    {
      var eliminatedActionDecls = EliminatedActionDecls.ToHashSet();
      var lhsExprs = new List<Expr>();
      var rhsExprs = new List<Expr>();
      foreach (var pendingAsync in action.PendingAsyncs)
      {
        var pendingAsyncExpr = Expr.Ident(action.PAs(pendingAsync.PendingAsyncType));
        var emptyExpr = ExprHelper.FunctionCall(pendingAsync.PendingAsyncConst, Expr.Literal(0));
        if (eliminatedActionDecls.Contains(pendingAsync))
        {
          lhsExprs.Add(Expr.Neq(pendingAsyncExpr, emptyExpr));
        }
        else
        {
          rhsExprs.Add(Expr.Eq(pendingAsyncExpr, emptyExpr));
        }
      }
      var cmds = new List<Cmd>() {
        CmdHelper.CallCmd(action.Impl.Proc, action.Impl.InParams, action.Impl.OutParams),
        GetCheck(action.tok, Expr.Imp(Expr.Or(lhsExprs), Expr.And(rhsExprs)), "Partition checker failed")
      };

      List<Block> checkerBlocks = new List<Block>();
      var locals = new List<Variable>();
      foreach (var pendingAsync in action.PendingAsyncs.Intersect(eliminatedActionDecls))
      {
        var pendingAsyncType = pendingAsync.PendingAsyncType;
        var pendingAsyncCtor = pendingAsync.PendingAsyncCtor;
        var pendingAsyncVar = action.PAs(pendingAsyncType);
        var pendingAsyncExpr = Expr.Ident(pendingAsyncVar);
        var pendingAsyncAction = civlTypeChecker.Action(pendingAsync);

        var paLocal = civlTypeChecker.LocalVariable($"local_{pendingAsyncVar.Name}", pendingAsyncType);
        locals.Add(paLocal);

        List<Cmd> blockCmds = new List<Cmd>
        {
          CmdHelper.AssumeCmd(Expr.Ge(Expr.Select(pendingAsyncExpr, Expr.Ident(paLocal)), Expr.Literal(1)))
        };

        var substMap = new Dictionary<Variable, Expr>();
        for (int i = 0; i < pendingAsyncAction.Impl.InParams.Count; i++)
        {
          substMap[pendingAsyncAction.Impl.InParams[i]] = ExprHelper.FieldAccess(Expr.Ident(paLocal), pendingAsyncCtor.InParams[i].Name);
        }
        blockCmds.AddRange(pendingAsyncAction.GetGateAsserts(
          Substituter.SubstitutionFromDictionary(substMap),
          $"Gate of {pendingAsyncAction.Name} in partition checker failed"));

        var block = BlockHelper.Block($"label_{pendingAsyncVar.Name}", blockCmds);
        CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, block, ResolutionContext.State.Two);
        checkerBlocks.Add(block);
      }

      string checkerName = civlTypeChecker.AddNamePrefix($"PartitionChecker_{action.Name}");
      List<Block> blocks = new List<Block>(checkerBlocks.Count + 1)
      {
        BlockHelper.Block(checkerName, cmds, checkerBlocks)
      };
      blocks.AddRange(checkerBlocks);

      Procedure proc = DeclHelper.Procedure(
        checkerName,
        action.Impl.InParams,
        action.Impl.OutParams,
        new List<Requires>(),
        action.ModifiedGlobalVars.Select(Expr.Ident).ToList(),
        new List<Ensures>());
      Implementation impl = DeclHelper.Implementation(
        proc,
        proc.InParams,
        proc.OutParams,
        locals,
        blocks);

      return new List<Declaration>(new Declaration[] { proc, impl });
    }
  }

  public class InlineSequentialization : Sequentialization
  {
    private Implementation inlinedImpl;

    public InlineSequentialization(CivlTypeChecker civlTypeChecker, Action targetAction)
      : base(civlTypeChecker, targetAction)
    {
      inlinedImpl = CreateInlinedImplementation();
      var refinedAction = targetAction.RefinedAction;
      if (refinedAction.HasPendingAsyncs)
      {
        Action.DesugarCreateAsyncs(civlTypeChecker, inlinedImpl, refinedAction.ActionDecl);
      }
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      for (int i = 0; i < refinedAction.Impl.InParams.Count; i++)
      {
        map[refinedAction.Impl.InParams[i]] = Expr.Ident(inlinedImpl.Proc.InParams[i]);
      }
      for (int i = 0; i < refinedAction.Impl.OutParams.Count; i++)
      {
        map[refinedAction.Impl.OutParams[i]] = Expr.Ident(inlinedImpl.Proc.OutParams[i]);
      }
      var subst = Substituter.SubstitutionFromDictionary(map);
      inlinedImpl.Proc.Requires = refinedAction.Gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr))).ToList();
      var frame = new HashSet<Variable>(civlTypeChecker.GlobalVariablesAtLayer(targetAction.LayerRange.UpperLayer));
      inlinedImpl.Proc.Ensures = new List<Ensures>(new[]
      {
        new Ensures(false, Substituter.Apply(subst, refinedAction.GetTransitionRelation(civlTypeChecker, frame)))
          { Description = new FailureOnlyDescription($"Refinement check of {targetAction.Name} failed") }
      });
    }

    protected override List<Declaration> GenerateCheckers()
    {
      var decls = base.GenerateCheckers();
      decls.AddRange(new List<Declaration>(new Declaration[] { inlinedImpl, inlinedImpl.Proc }));
      return decls;
    }

    private Implementation CreateInlinedImplementation()
    {
      var graph = new Graph<ActionDecl>();
      EliminatedActionDecls.ForEach(actionDecl =>
      {
        graph.AddSource(actionDecl);
        CollectionExtensions.ForEach(actionDecl.CreateActionDecls.Intersect(EliminatedActionDecls), x => graph.AddEdge(x, actionDecl));
      });
      var eliminatedPendingAsyncs = new Dictionary<CtorType, Implementation>();
      var decls = new List<Declaration>();
      graph.TopologicalSort().ForEach(actionDecl =>
      {
        var impl = Action.CreateDuplicateImplementation(actionDecl.Impl,
          $"{actionDecl.Name}_RefinementCheck");
        eliminatedPendingAsyncs[actionDecl.PendingAsyncType] = impl;
        decls.Add(impl);
        decls.Add(impl.Proc);
      });
      var inlinedImpl = Action.CreateDuplicateImplementation(targetAction.ActionDecl.Impl,
        $"{targetAction.ActionDecl.Name}_RefinementCheck");
      CivlAttributes.RemoveAttributes(inlinedImpl.Proc, new HashSet<string> { "inline" });
      decls.Add(inlinedImpl);
      decls.Add(inlinedImpl.Proc);
      decls.OfType<Implementation>().ForEach(impl =>
      {
        var modifies = impl.Proc.Modifies.Select(ie => ie.Decl).ToHashSet();
        impl.Blocks.ForEach(block =>
        {
          for (int i = 0; i < block.Cmds.Count; i++)
          {
            block.Cmds[i] = Transform(eliminatedPendingAsyncs, block.Cmds[i], modifies);
          }
        });
        impl.Proc.Modifies = modifies.Select(v => Expr.Ident(v)).ToList();
      });
      var oldTopLevelDeclarations = new List<Declaration>(civlTypeChecker.program.TopLevelDeclarations);
      civlTypeChecker.program.AddTopLevelDeclarations(decls);
      decls.OfType<Implementation>().ForEach(impl =>
      {
        impl.OriginalBlocks = impl.Blocks;
        impl.OriginalLocVars = impl.LocVars;
      });
      Inliner.ProcessImplementation(civlTypeChecker.Options, civlTypeChecker.program, inlinedImpl);
      civlTypeChecker.program.TopLevelDeclarations = oldTopLevelDeclarations;
      decls.OfType<Implementation>().ForEach(impl =>
      {
        impl.OriginalBlocks = null;
        impl.OriginalLocVars = null;
      });
      return inlinedImpl;
    }

    private Cmd Transform(Dictionary<CtorType, Implementation> eliminatedPendingAsyncs, Cmd cmd, HashSet<Variable> modifies)
    {
      if (cmd is CallCmd callCmd && callCmd.Proc.OriginalDeclWithFormals is { Name: "create_async" })
      {
        var pendingAsyncType = (CtorType)civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
        var datatypeTypeCtorDecl = (DatatypeTypeCtorDecl)pendingAsyncType.Decl;
        if (eliminatedPendingAsyncs.ContainsKey(pendingAsyncType))
        {
          var newCallee = eliminatedPendingAsyncs[pendingAsyncType].Proc;
          var newIns = datatypeTypeCtorDecl.Constructors[0].InParams
            .Select(x => (Expr)ExprHelper.FieldAccess(callCmd.Ins[0], x.Name)).ToList();
          var newCallCmd = new CallCmd(callCmd.tok, newCallee.Name, newIns, new List<IdentifierExpr>())
          {
            Proc = newCallee
          };
          modifies.UnionWith(newCallee.Modifies.Select(ie => ie.Decl));
          return newCallCmd;
        }
      }
      return cmd;
    }
  }

  public class InductiveSequentialization : Sequentialization
  {
    private Action invariantAction;
    private IdentifierExpr choice;
    private Dictionary<CtorType, Variable> newPAs;

    // private class LinearityCheck
    // {
    //   public LinearDomain domain;
    //   public Expr assume;
    //   public Expr assert;
    //   public string message;
    //   public string checkName;

    //   public LinearityCheck(LinearDomain domain, Expr assume, Expr assert, string message, string checkName)
    //   {
    //     this.domain = domain;
    //     this.assume = assume;
    //     this.assert = assert;
    //     this.message = message;
    //     this.checkName = checkName;
    //   }
    // }

    public InductiveSequentialization(CivlTypeChecker civlTypeChecker, Action targetAction, Action invariantAction)
    : base(civlTypeChecker, targetAction)
    {
      // The type checker ensures that the set of modified variables of an invariant is a superset of
      // - the modified set of each of each eliminated and abstract action associated with this invariant.
      // - the target and refined action of every application of inductive sequentialization that refers to this invariant.
      this.invariantAction = invariantAction;
      choice = Expr.Ident(invariantAction.ImplWithChoice.OutParams.Last());
      newPAs = invariantAction.PendingAsyncs.ToDictionary(decl => decl.PendingAsyncType,
        decl => (Variable)civlTypeChecker.LocalVariable($"newPAs_{decl.Name}", decl.PendingAsyncMultisetType));
    }

    private IEnumerable<Expr> InputDisjointnessExprs()
    {
      return civlTypeChecker.linearTypeChecker.DisjointnessExprForEachDomain(
        invariantAction.Impl.InParams.Union(invariantAction.UsedGlobalVars)
        .Where(x => LinearTypeChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(x))));
    }

    private List<Declaration> GenerateBaseCaseChecker()
    {
      var inputDisjointnessExprs = InputDisjointnessExprs();
      var requires = invariantAction.Gate.Select(g => new Requires(false, g.Expr))
        .Concat(inputDisjointnessExprs.Select(expr => new Requires(false, expr))).ToList();

      var subst = targetAction.GetSubstitution(invariantAction);
      var cmds = targetAction.GetGateAsserts(subst,
        $"Gate of {targetAction.Name} fails in {rule} base check against invariant {invariantAction.Name}").ToList<Cmd>();

      // Construct call to targetAction
      var pendingAsyncTypeToOutputParamIndex = invariantAction.PendingAsyncs.Select(x => x.PendingAsyncType)
          .Zip(Enumerable.Range(invariantAction.PendingAsyncStartIndex, invariantAction.PendingAsyncs.Count()))
          .ToDictionary(tuple => tuple.Item1, tuple => tuple.Item2);
      var outputVars = new List<Variable>(invariantAction.Impl.OutParams.Take(invariantAction.PendingAsyncStartIndex));
      outputVars.AddRange(targetAction.PendingAsyncs.Select(action =>
        invariantAction.Impl.OutParams[pendingAsyncTypeToOutputParamIndex[action.PendingAsyncType]]));
      cmds.Add(CmdHelper.CallCmd(targetAction.Impl.Proc, invariantAction.Impl.InParams, outputVars));

      // Assign empty multiset to the rest
      var remainderPendingAsyncs = invariantAction.PendingAsyncs.Except(targetAction.PendingAsyncs);
      if (remainderPendingAsyncs.Any())
      {
        var lhss = remainderPendingAsyncs.Select(decl =>
            Expr.Ident(invariantAction.Impl.OutParams[pendingAsyncTypeToOutputParamIndex[decl.PendingAsyncType]]))
          .ToList();
        var rhss = remainderPendingAsyncs.Select(decl =>
          ExprHelper.FunctionCall(decl.PendingAsyncConst, Expr.Literal(0))).ToList<Expr>();
        cmds.Add(CmdHelper.AssignCmd(lhss, rhss));
      }

      var frame = new HashSet<Variable>(invariantAction.ModifiedGlobalVars);
      cmds.Add(GetCheck(targetAction.tok, invariantAction.GetTransitionRelation(civlTypeChecker, frame),
        $"{rule} base of {targetAction.Name} failed"));

      return GetCheckerTuple($"{rule}_base_{targetAction.Name}", requires, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams, new List<Variable>(), cmds);
    }

    private List<Declaration> GenerateConclusionChecker()
    {
      var inputDisjointnessExprs = InputDisjointnessExprs();
      var refinedAction = targetAction.RefinedAction;
      var subst = refinedAction.GetSubstitution(invariantAction);
      var requires = refinedAction.Gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr)))
        .Concat(inputDisjointnessExprs.Select(expr => new Requires(false, expr))).ToList();

      var cmds = invariantAction.GetGateAsserts(null,
        $"Gate of {invariantAction.Name} fails in {rule} conclusion check against {refinedAction.Name}").ToList<Cmd>();
      cmds.Add(CmdHelper.CallCmd(invariantAction.Impl.Proc, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams));
      cmds.Add(CmdHelper.AssumeCmd(NoPendingAsyncs));
      var frame = new HashSet<Variable>(civlTypeChecker.GlobalVariablesAtLayer(targetAction.LayerRange.UpperLayer));
      cmds.Add(GetCheck(targetAction.tok, Substituter.Apply(subst, refinedAction.GetTransitionRelation(civlTypeChecker, frame)),
        $"{rule} conclusion of {targetAction.Name} failed"));

      return GetCheckerTuple($"{rule}_conclusion_{targetAction.Name}", requires, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams, new List<Variable>(), cmds);
    }

    private List<Declaration> GenerateStepChecker(Action pendingAsync)
    {
      var inputDisjointnessExprs = InputDisjointnessExprs();
      var pendingAsyncType = pendingAsync.ActionDecl.PendingAsyncType;
      var pendingAsyncCtor = pendingAsync.ActionDecl.PendingAsyncCtor;
      var requires = invariantAction.Gate.Select(g => new Requires(false, g.Expr))
        .Concat(inputDisjointnessExprs.Select(expr => new Requires(false, expr))).ToList();
      var locals = new List<Variable>();
      List<Cmd> cmds = new List<Cmd>
      {
        CmdHelper.CallCmd(invariantAction.ImplWithChoice.Proc, invariantAction.ImplWithChoice.InParams,
        invariantAction.ImplWithChoice.OutParams),
        CmdHelper.AssumeCmd(ChoiceTest(pendingAsyncType)),
        CmdHelper.AssumeCmd(Expr.Gt(Expr.Select(PAs(pendingAsyncType), Choice(pendingAsyncType)),
        Expr.Literal(0))),
        RemoveChoice(pendingAsyncType)
      };

      List<Expr> inputExprs = new List<Expr>();
      for (int i = 0; i < pendingAsync.Impl.InParams.Count; i++)
      {
        inputExprs.Add(ExprHelper.FieldAccess(Choice(pendingAsyncType), pendingAsyncCtor.InParams[i].Name));
      }
      cmds.AddRange(pendingAsync.GetGateAsserts(Substituter.SubstitutionFromDictionary(pendingAsync.Impl.InParams.Zip(inputExprs).ToDictionary(x => x.Item1, x => x.Item2)),
        $"Gate of {pendingAsync.Name} fails in {rule} induction step for invariant {invariantAction.Name}"));
      cmds.AddRange(Preconditions(pendingAsync, Substituter.SubstitutionFromDictionary(pendingAsync.ActionDecl.InParams.Zip(inputExprs).ToDictionary(x => x.Item1, x => x.Item2))));

      List<IdentifierExpr> outputExprs = new List<IdentifierExpr>();
      if (pendingAsync.HasPendingAsyncs)
      {
        pendingAsync.PendingAsyncs.ForEach(decl =>
        {
          var ie = NewPAs(decl.PendingAsyncType);
          locals.Add(ie.Decl);
          outputExprs.Add(ie);
        });
      }
      cmds.Add(CmdHelper.CallCmd(pendingAsync.Impl.Proc, inputExprs, outputExprs));
      if (pendingAsync.HasPendingAsyncs)
      {
        var lhss = pendingAsync.PendingAsyncs.Select(decl => new SimpleAssignLhs(Token.NoToken, PAs(decl.PendingAsyncType)))
          .ToList<AssignLhs>();
        var rhss = pendingAsync.PendingAsyncs.Select(decl => ExprHelper.FunctionCall(decl.PendingAsyncAdd,
          PAs(decl.PendingAsyncType), NewPAs(decl.PendingAsyncType))).ToList<Expr>();
        cmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
      }

      var frame = new HashSet<Variable>(invariantAction.ModifiedGlobalVars);
      cmds.Add(GetCheck(invariantAction.tok, invariantAction.GetTransitionRelation(civlTypeChecker, frame),
        $"{rule} step of {invariantAction.Name} with {pendingAsync.Name} failed"));

      return GetCheckerTuple($"{rule}_step_{invariantAction.Name}_{pendingAsync.Name}", requires,
        invariantAction.ImplWithChoice.InParams, invariantAction.ImplWithChoice.OutParams, locals, cmds);
    }

    protected List<Declaration> GenerateSideConditionChecker(Action act)
    {
      var ltc = civlTypeChecker.linearTypeChecker;
      var inputs = act.Impl.InParams;
      var outputs = act.Impl.OutParams;
    
      var inputDisjointnessExpr = ltc.DisjointnessExprForEachDomain(
        inputs.Union(act.ModifiedGlobalVars)
        .Where(x => LinearityChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(x))));

      List<Requires> requires = act.Gate.Select(a => new Requires(false, a.Expr))
          .Concat(inputDisjointnessExpr.Select(expr => new Requires(false, expr)))
          .ToList();

      List<LinearityCheck> linearityChecks = new List<LinearityCheck>();
      foreach (var domain in ltc.LinearDomains)
      {
       var existingExpr = Expr.True;
       var inVars = new List<Variable>().Union(act.ModifiedGlobalVars)
        .Where(x => LinearityChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(x))).Select(Expr.Ident).ToList();
       var outVars = new List<Variable>().Union(act.ModifiedGlobalVars)
        .Where(x => LinearityChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(x))).Select(Expr.Ident).ToList();
       var inPermissionSet = ExprHelper.Old(ltc.UnionExprForPermissions(domain, ltc.PermissionExprs(domain, inVars)));
       var outPermissionSet = ltc.UnionExprForPermissions(domain, ltc.PermissionExprs(domain, outVars));
       var outSubsetInExpr = ltc.SubsetExprForPermissions(domain, inPermissionSet, outPermissionSet);
       linearityChecks.Add(new LinearityCheck(
          domain,
          existingExpr,
          outSubsetInExpr,
          $"Only put permissions of type {domain.permissionType}",
          $"only_put_perm_{act.Name}"));
      }   
      
      List<Block> checkerBlocks = new List<Block>(linearityChecks.Count);
      foreach (var lc in linearityChecks)
      {
        List<Cmd> cmds = new List<Cmd>(2);
        if (lc.assume != null)
        {
          cmds.Add(CmdHelper.AssumeCmd(lc.assume));
        }
        cmds.Add(CmdHelper.AssertCmd(act.tok, lc.assert, lc.message));
        var block = BlockHelper.Block($"{lc.domain.permissionType}_{lc.checkName}", cmds);
        CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, block, ResolutionContext.State.Two);
        checkerBlocks.Add(block);
      }
      
      // Create init blocks
      List<Block> blocks = new List<Block>(linearityChecks.Count + 1);
      blocks.Add(
        BlockHelper.Block(
          "init",
          new List<Cmd>() { CmdHelper.CallCmd(act.Impl.Proc, inputs, outputs) },
          checkerBlocks));
      blocks.AddRange(checkerBlocks);

      // Create the whole check procedure
      string checkerName = civlTypeChecker.AddNamePrefix($"{rule}_SideCondition_{act.Name}");
      Procedure linCheckerProc = DeclHelper.Procedure(checkerName,
        inputs, outputs, requires, act.Impl.Proc.Modifies, new List<Ensures>());
      Implementation linCheckImpl = DeclHelper.Implementation(linCheckerProc,
        inputs, outputs,  new List<Variable>(), blocks);
      return new List<Declaration>(new Declaration[] { linCheckerProc, linCheckImpl });
    }

    
    private List<Declaration> DescendantCheckerFull(){
      //I need to get the elim action, and I get the alpha_elim action, now I check that 
      //Get expression gate_S(elim), gate_S(alpha_elim), then expression for X would be gate_S(elim) - gate_S(alpha_elim)
      var dec =  new List<Declaration>();
      //note: you are checking twice E1, E2 and E2, E1 which may not be necessary
      foreach (var E1 in eliminatedActions){
        foreach (var E2 in eliminatedActions){
              dec.AddRange(GenerateInconsistencyChecker(E1, E2)); 
        }
      }
      return dec;
    }

     private List<Declaration> GenerateInconsistencyChecker(Action E1, Action E2){
      
      var gate_E1 = (Expr)Expr.True;
      foreach(var g in E1.Gate){
        gate_E1 = Expr.And(gate_E1, g.Expr);
      }
      var gate_E2 = (Expr)Expr.True;
      foreach(var g in E2.Gate){
        gate_E2 = Expr.And(gate_E2, g.Expr);
      }
      var gate_M = (Expr)Expr.True;
      foreach(var g in targetAction.Gate){
        gate_M = Expr.And(gate_M, g.Expr);
      }

      var local_E1 = civlTypeChecker.LocalVariable($"E1_{E1.Name}", E1.ActionDecl.PendingAsyncType);
      var local_E2 = civlTypeChecker.LocalVariable($"E2_{E2.Name}", E2.ActionDecl.PendingAsyncType);
      var local_M = civlTypeChecker.LocalVariable($"M_{targetAction.Name}", targetAction.ActionDecl.PendingAsyncType);// This means M is an async.

      
      var locals = new List<Variable>();
      var locals_g = new List<Variable>();
      // locals.Add(local_M);
  

      foreach(var g in civlTypeChecker.GlobalVariables){
        locals_g.Add(civlTypeChecker.LocalVariable($"temp_{g.Name}", g.TypedIdent.Type));
      }

      List<Expr> inputExprs_M = new List<Expr>();
      List<Expr> inputExprs_E1 = new List<Expr>();
      List<Expr> inputExprs_E2 = new List<Expr>();
      List<Expr> globalExprs  = new List<Expr>();
      for (int i = 0; i < targetAction.Impl.InParams.Count; i++)
      {
        inputExprs_M.Add(ExprHelper.FieldAccess(Expr.Ident(local_M), targetAction.ActionDecl.PendingAsyncCtor.InParams[i].Name));
      }
      for (int i = 0; i < E1.Impl.InParams.Count; i++)
      {
        inputExprs_E1.Add(ExprHelper.FieldAccess(Expr.Ident(local_E1), E1.ActionDecl.PendingAsyncCtor.InParams[i].Name));
      }
      for (int i = 0; i < E2.Impl.InParams.Count; i++)
      {
        inputExprs_E2.Add(ExprHelper.FieldAccess(Expr.Ident(local_E2), E2.ActionDecl.PendingAsyncCtor.InParams[i].Name));
      }
      foreach(var g in locals_g)
      {
        globalExprs.Add(Expr.Ident(g));
      }
    
      locals.Add(local_E1);
      locals.Add(local_E2);
      locals.AddRange(locals_g);
      //create substitutions

      Substitution subst_l_M = Substituter.SubstitutionFromDictionary(
        targetAction.Impl.InParams.Zip(inputExprs_M).ToDictionary(x => x.Item1, x => x.Item2));
      
      Substitution subst_E1 = Substituter.SubstitutionFromDictionary(
        E1.Impl.InParams.Zip(inputExprs_E1).ToDictionary(x => x.Item1, x => x.Item2));

      Substitution subst_E2 = Substituter.SubstitutionFromDictionary(
        E2.Impl.InParams.Zip(inputExprs_E2).ToDictionary(x => x.Item1, x => x.Item2));

      Substitution subst_g0 = Substituter.SubstitutionFromDictionary(
        civlTypeChecker.GlobalVariables.Zip(globalExprs).ToDictionary(x => x.Item1, x => x.Item2));

      var ltc = civlTypeChecker.linearTypeChecker;
      Dictionary < LinearDomain, Expr > disjointnessExpr = new Dictionary < LinearDomain, Expr > ();
      Dictionary < LinearDomain, Expr > subsetExpr = new Dictionary < LinearDomain, Expr > ();

      foreach(var domain in ltc.LinearDomains){
      var collect_expr_g = ltc.UnionExprForPermissions(domain, ltc.PermissionExprs(domain, civlTypeChecker.GlobalVariables.Where(v => LinearityChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(v)))));// maybe filter out the ones that linear only

      var pendingAsyncLinearParams_M = targetAction.ActionDecl.InParams
     .Where(v => LinearityChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(v)))
     .Select(v => ExprHelper.FieldAccess(Expr.Ident(local_M), v.Name)).ToList<Expr>();

     CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, pendingAsyncLinearParams_M);

     var collect_expr_l = ltc.UnionExprForPermissions(domain, ltc.PermissionExprs(domain, pendingAsyncLinearParams_M));

     var pendingAsyncLinearParams_E1 = E1.ActionDecl.InParams
     .Where(v => LinearityChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(v)))
     .Select(v => ExprHelper.FieldAccess(Expr.Ident(local_E1), v.Name)).ToList<Expr>();

     CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, pendingAsyncLinearParams_E1);
      
      var collect_expr_l1 = ltc.UnionExprForPermissions(domain, ltc.PermissionExprs(domain, pendingAsyncLinearParams_E1));

      var pendingAsyncLinearParams_E2 = E2.ActionDecl.InParams
     .Where(v => LinearityChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(v)))
     .Select(v => ExprHelper.FieldAccess(Expr.Ident(local_E2), v.Name)).ToList<Expr>();

     CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, pendingAsyncLinearParams_E2);

      var collect_expr_l2 = ltc.UnionExprForPermissions(domain, ltc.PermissionExprs(domain, pendingAsyncLinearParams_E2));

      //What about disjoint check with collect_expr_l?
      var noDuplicationExpr1 = Expr.Eq(
        ExprHelper.FunctionCall(domain.mapAnd, collect_expr_g, collect_expr_l1),
        ExprHelper.FunctionCall(domain.mapConstBool, Expr.False));
      var noDuplicationExpr2 =  Expr.Eq(
        ExprHelper.FunctionCall(domain.mapAnd, collect_expr_g, collect_expr_l2),
        ExprHelper.FunctionCall(domain.mapConstBool, Expr.False));
      var noDuplicationExpr3 =  Expr.Eq(
        ExprHelper.FunctionCall(domain.mapAnd, collect_expr_l1, collect_expr_l2),
        ExprHelper.FunctionCall(domain.mapConstBool, Expr.False));

      disjointnessExpr[domain] = Expr.And(Expr.And(noDuplicationExpr1, noDuplicationExpr2), noDuplicationExpr3);

      subsetExpr[domain] = Expr.And(ltc.SubsetExprForPermissions(domain,collect_expr_l1 , collect_expr_l), ltc.SubsetExprForPermissions(domain,collect_expr_l1 , collect_expr_l)); // I check subset with l alone, because I don't know how to compute what the root took from globals. So I assume root also doesn't take anything from globals.
      
      }
      var cmds = new List<Cmd>();

      var disjointnessExprTotal = Expr.And(disjointnessExpr.Values);
      cmds.Add(CmdHelper.AssumeCmd(disjointnessExprTotal));

      var gate_S_M = Expr.And(GetNonBlockExpression(targetAction), Substituter.Apply(subst_g0, Substituter.Apply(subst_l_M, gate_M)));
      cmds.Add(CmdHelper.AssumeCmd(gate_S_M));
      
      var subsetExprTotal = Expr.And(subsetExpr.Values);
      cmds.Add(CmdHelper.AssumeCmd(subsetExprTotal));

     
      Expr X_E2 = Expr.True;
      var E2_Action = civlTypeChecker.AtomicActions.Single(s => s.Name == E2.Name);
      var assumeCmds = E2_Action.Impl.Blocks[0].Cmds.OfType<AssumeCmd>();
      foreach (var c in assumeCmds) 
      {
         var ex = QKeyValue.FindAttribute(c.Attributes, x => (x.Key == "exit_condition"));
        if(ex != null){
          X_E2 = (Expr)ex.Params[0];
        }
      } 

      cmds.Add(CmdHelper.AssertCmd(targetAction.tok, Expr.Not(Expr.And(Substituter.Apply(subst_E1, gate_E1), Substituter.Apply(subst_E2, X_E2))) , $"Inconsistency check failed for {targetAction.Name}, {E1.Name}, {E2.Name}"));

      return GetCheckerTuple($"InconsistencyChecker_{targetAction.Name}_{E1.Name}_{E2.Name}", new List<Requires>(),
        new List<Variable>(), new List<Variable>(), locals,  cmds);
    }
    
    private Expr GetNonBlockExpression(Action A)
    {
      Implementation impl = A.Impl;
      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(A.UsedGlobalVarsInGate);
      frame.UnionWith(A.UsedGlobalVarsInAction);
      return TransitionRelationComputation.Cooperation(civlTypeChecker, A, frame);
    }

    /*
     * This method generates the extra assumption for the left-mover check of the abstraction of an eliminated action.
     * The arguments leftMover and leftMoverArgs pertain to the action being moved left.
     * The arguments action and actionArgs pertain to the action across which leftMover is being moved.
     *
     * A key concept used in the generation of this extra assumption is the input-output transition relation of an action.
     * This relation is obtained by taking the conjunction of the gate and transition relation of the action and
     * existentially quantifying globals in the pre and the post state.
     *
     * There are two parts to the assumption, one for leftMover and the other for action.
     * Both parts are stated in the context of the input-output relation of the invariant action.
     * - The invocation of leftMover is identical to the choice made by the invariant.
     * - If action is being eliminated, then the invocation of action is such that either:
     *   (1) the permissions in the invocation are disjoint from the permissions in the invariant invocation, or
     *   (2) the permissions in the invocation is contained in the permissions of one of the pending asyncs created by the invariant invocation.
     */
    public override IEnumerable<Expr> GenerateMoverCheckAssumptions(Action action, List<Variable> actionArgs, Action leftMover,
      List<Variable> leftMoverArgs)
    {
      var invariantFormalMap =
        invariantAction.ImplWithChoice.InParams.Concat(invariantAction.ImplWithChoice.OutParams).ToDictionary(v => v,
          v => (Expr)Expr.Ident(civlTypeChecker.BoundVariable($"{invariantAction.Name}_{v.Name}",
            v.TypedIdent.Type)));
      var invariantFormalSubst = Substituter.SubstitutionFromDictionary(invariantFormalMap);
      var invariantTransitionRelationExpr = ExprHelper.FunctionCall(invariantAction.InputOutputRelationWithChoice,
        invariantAction.ImplWithChoice.InParams.Concat(invariantAction.ImplWithChoice.OutParams)
          .Select(v => invariantFormalMap[v]).ToList());

      Substitution subst = Substituter.SubstitutionFromDictionary(
        leftMover.ActionDecl.InParams.Zip(leftMoverArgs.Select(x => (Expr)Expr.Ident(x))).ToDictionary(x => x.Item1, x => x.Item2));

      return new List<Expr>(Preconditions(leftMover, subst).Select(assertCmd => assertCmd.Expr))
      {
        ExprHelper.ExistsExpr(
        invariantFormalMap.Values.OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList(),
        Expr.And(new[]
        {
          invariantTransitionRelationExpr, ActionExpr(action, actionArgs, invariantFormalSubst),
          LeftMoverExpr(leftMover, leftMoverArgs, invariantFormalSubst)
        }))
      };
    }

    private Expr ActionExpr(Action action, List<Variable> actionArgs, Substitution invariantFormalSubst)
    {
      if (!eliminatedActions.Contains(action))
      {
        return Expr.True;
      }
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      var disjointnessExpr =
        Expr.And(linearTypeChecker.LinearDomains.Select(
          domain =>
            linearTypeChecker.DisjointnessExprForPermissions(domain,
              linearTypeChecker.PermissionExprs(domain, invariantAction.Impl.InParams).Concat(linearTypeChecker.PermissionExprs(domain, actionArgs)))
        ).ToList());
      var pendingAsyncExprs = invariantAction.PendingAsyncs.Select(pendingAsync =>
      {
        var pendingAsyncAction = civlTypeChecker.Action(pendingAsync);
        var pendingAsyncActionParams = pendingAsyncAction.Impl.Proc.InParams
          .Concat(pendingAsyncAction.Impl.Proc.OutParams).ToList();
        var pendingAsyncFormalMap = pendingAsyncActionParams.ToDictionary(v => v,
          v => (Expr)Expr.Ident(civlTypeChecker.BoundVariable($"{pendingAsync.Name}_{v.Name}", v.TypedIdent.Type)));
        var subst = Substituter.SubstitutionFromDictionary(pendingAsyncFormalMap);
        var conjuncts = linearTypeChecker.LinearDomains.Select(domain =>
        {
          var lhs = linearTypeChecker.UnionExprForPermissions(domain, linearTypeChecker.PermissionExprs(domain, actionArgs));
          var rhs = linearTypeChecker.UnionExprForPermissions(domain,
            linearTypeChecker.PermissionExprs(domain, pendingAsync.InParams).Select(expr => Substituter.Apply(subst, expr)));
          return linearTypeChecker.SubsetExprForPermissions(domain, lhs, rhs);
        });
        var pendingAsyncTransitionRelationExpr = ExprHelper.FunctionCall(pendingAsyncAction.InputOutputRelation,
          pendingAsyncActionParams.Select(v => pendingAsyncFormalMap[v]).ToList());
        var membershipExpr =
          Expr.Gt(
            Expr.Select(PAs(pendingAsync.PendingAsyncType),
              ExprHelper.FunctionCall(pendingAsync.PendingAsyncCtor,
                pendingAsync.InParams.Select(v => pendingAsyncFormalMap[v]).ToList())), Expr.Literal(0));
        return ExprHelper.ExistsExpr(
          pendingAsyncFormalMap.Values.OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList(),
          Expr.And(conjuncts.Concat(new[] { membershipExpr, pendingAsyncTransitionRelationExpr })));
      });
      var actionExpr = Expr.Or(pendingAsyncExprs.Append(disjointnessExpr));
      actionExpr = Substituter.Apply(invariantFormalSubst, actionExpr);
      return actionExpr;
    }

    private Expr LeftMoverExpr(Action leftMover, List<Variable> leftMoverArgs, Substitution invariantFormalSubst)
    {
      var leftMoverPendingAsyncCtor = leftMover.ActionDecl.PendingAsyncCtor;
      var leftMoverPA =
        ExprHelper.FunctionCall(leftMoverPendingAsyncCtor, leftMoverArgs.Select(v => Expr.Ident(v)).ToArray());
      var leftMoverExpr = Expr.And(new[]
      {
        ChoiceTest(leftMover.ActionDecl.PendingAsyncType),
        Expr.Gt(
          Expr.Select(PAs(leftMover.ActionDecl.PendingAsyncType),
            Choice(leftMover.ActionDecl.PendingAsyncType)), Expr.Literal(0)),
        Expr.Eq(Choice(leftMover.ActionDecl.PendingAsyncType), leftMoverPA)
      });
      leftMoverExpr = Substituter.Apply(invariantFormalSubst, leftMoverExpr);
      return leftMoverExpr;
    }

    private List<Declaration> GetCheckerTuple(string checkerName, List<Requires> requires, List<Variable> inParams,
      List<Variable> outParams, List<Variable> locals, List<Cmd> cmds)
    {
      var proc = DeclHelper.Procedure(
        civlTypeChecker.AddNamePrefix(checkerName),
        inParams,
        outParams,
        requires,
        invariantAction.ModifiedGlobalVars.Select(Expr.Ident).ToList(),
        new List<Ensures>());
      var impl = DeclHelper.Implementation(
        proc,
        proc.InParams,
        proc.OutParams,
        locals,
        new List<Block> { BlockHelper.Block(checkerName, cmds) });
      return new List<Declaration>(new Declaration[] { proc, impl });
    }

    private IdentifierExpr PAs(CtorType pendingAsyncType)
    {
      return Expr.Ident(invariantAction.PAs(pendingAsyncType));
    }

    private IdentifierExpr NewPAs(CtorType pendingAsyncType)
    {
      return Expr.Ident(newPAs[pendingAsyncType]);
    }

    private Expr Choice(CtorType pendingAsyncType)
    {
      return ExprHelper.FieldAccess(choice, pendingAsyncType.Decl.Name);
    }

    private Expr ChoiceTest(CtorType pendingAsyncType)
    {
      return ExprHelper.IsConstructor(choice, invariantAction.ChoiceConstructor(pendingAsyncType).Name);
    }

    private Expr NoPendingAsyncs
    {
      get
      {
        var expr = Expr.And(eliminatedActions.Select(action => Expr.Eq(PAs(action.ActionDecl.PendingAsyncType),
          ExprHelper.FunctionCall(action.ActionDecl.PendingAsyncConst, Expr.Literal(0)))));
        expr.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
        return expr;
      }
    }

    private AssignCmd RemoveChoice(CtorType pendingAsyncType)
    {
      var rhs = Expr.Sub(Expr.Select(PAs(pendingAsyncType), Choice(pendingAsyncType)), Expr.Literal(1));
      return AssignCmd.MapAssign(Token.NoToken, PAs(pendingAsyncType), new List<Expr> { Choice(pendingAsyncType) }, rhs);
    }

    protected override List<Declaration> GenerateCheckers()
    {
      var decls = base.GenerateCheckers();
      decls.AddRange(GenerateBaseCaseChecker());
      decls.AddRange(GenerateConclusionChecker());
      if (rule == InductiveSequentializationRule.ISR){
         decls.AddRange(GenerateSideConditionChecker(targetAction));
      }
      foreach (var elim in eliminatedActions)
      {
        decls.AddRange(GenerateStepChecker(elim));
        if (rule == InductiveSequentializationRule.ISR){
          if (elim == targetAction){
            continue;
          }
          decls.AddRange(GenerateSideConditionChecker(elim));
        }
      }



      // foreach(var action in civlTypeChecker.AtomicActions){
      //    if (rule == InductiveSequentializationRule.ISR){
      //     decls.AddRange(GenerateSideConditionChecker(action));
      //   }
      // }
      if (rule == InductiveSequentializationRule.ISR){
      decls.AddRange(DescendantCheckerFull());
      }
      return decls;
    }
  }
}