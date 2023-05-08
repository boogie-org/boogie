using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public abstract class Sequentialization
  {
    protected CivlTypeChecker civlTypeChecker;
    protected Action targetAction;
    protected Dictionary<Action, Action> elim;

    protected Sequentialization(CivlTypeChecker civlTypeChecker, Action targetAction)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.targetAction = targetAction;
      this.elim = new Dictionary<Action, Action>(targetAction.ActionDecl.EliminationMap().Select(x =>
        KeyValuePair.Create(civlTypeChecker.Action(x.Key), civlTypeChecker.Action(x.Value))));
    }

    public IEnumerable<Action> Abstractions => elim.Values;

    public IEnumerable<Tuple<Action, Action>> AbstractionChecks =>
      elim.Where(kv => kv.Key != kv.Value).Select(kv => Tuple.Create(kv.Key, kv.Value));

    public int Layer => targetAction.LayerRange.UpperLayer;

    public abstract List<Declaration> GenerateCheckers();

    public virtual Expr GenerateMoverCheckAssumption(Action action, List<Variable> actionArgs, Action leftMover,
      List<Variable> leftMoverArgs)
    {
      return Expr.True;
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
      var subst = refinedAction.GetSubstitution(targetAction);
      inlinedImpl.Proc.Requires = refinedAction.Gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr))).ToList();
      inlinedImpl.Proc.Ensures = new List<Ensures>(new[]
      {
        new Ensures(false, Substituter.Apply(subst, refinedAction.GetTransitionRelation(civlTypeChecker, inlinedImpl.Proc.ModifiedVars.ToHashSet())),
          $"Refinement check of {targetAction.Name} failed")
      });
    }

    public override List<Declaration> GenerateCheckers()
    {
      return new List<Declaration>(new Declaration[] { inlinedImpl, inlinedImpl.Proc });
    }

    private Implementation CreateInlinedImplementation()
    {
      var eliminatedActionDecls = targetAction.ActionDecl.EliminationMap().Keys.ToHashSet();
      var graph = new Graph<ActionDecl>();
      eliminatedActionDecls.Iter(actionDecl =>
      {
        graph.AddSource(actionDecl);
        actionDecl.CreateActionDecls.Intersect(eliminatedActionDecls).Iter(x => graph.AddEdge(x,actionDecl));
      });
      var eliminatedPendingAsyncs = new Dictionary<CtorType, Implementation>();
      var decls = new List<Declaration>();
      graph.TopologicalSort().Iter(actionDecl =>
      {
        var impl = Action.CreateDuplicateImplementation(actionDecl.Impl, $"{actionDecl.Name}_RefinementCheck");
        eliminatedPendingAsyncs[actionDecl.PendingAsyncType] = impl;
        decls.Add(impl);
        decls.Add(impl.Proc);
      });
      var inlinedImpl = Action.CreateDuplicateImplementation(targetAction.ActionDecl.Impl,
        $"{targetAction.ActionDecl.Name}_RefinementCheck");
      CivlAttributes.RemoveAttributes(inlinedImpl.Proc, new HashSet<string> { "inline" });
      decls.Add(inlinedImpl);
      decls.Add(inlinedImpl.Proc);
      decls.OfType<Implementation>().Iter(impl =>
      {
        var modifies = impl.Proc.Modifies.Select(ie => ie.Decl).ToHashSet();
        impl.Blocks.Iter(block =>
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
      decls.OfType<Implementation>().Iter(impl =>
      {
        impl.OriginalBlocks = impl.Blocks;
        impl.OriginalLocVars = impl.LocVars;
      });
      Inliner.ProcessImplementation(civlTypeChecker.Options, civlTypeChecker.program, inlinedImpl);
      civlTypeChecker.program.TopLevelDeclarations = oldTopLevelDeclarations;
      decls.OfType<Implementation>().Iter(impl =>
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
        var pendingAsyncType =
          (CtorType)civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
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
    private HashSet<Variable> frame;
    private IdentifierExpr choice;
    private Dictionary<CtorType, Variable> newPAs;

    public InductiveSequentialization(CivlTypeChecker civlTypeChecker, Action targetAction, Action invariantAction)
    : base(civlTypeChecker, targetAction)
    {
      // The type checker ensures that the set of modified variables of an invariant is a superset of
      // - the modified set of each of each eliminated and abstract action associated with this invariant.
      // - the target and refined action of every application of inductive sequentialization that refers to this invariant.
      this.invariantAction = invariantAction;
      frame = new HashSet<Variable>(invariantAction.ModifiedGlobalVars);
      choice = Expr.Ident(invariantAction.ImplWithChoice.OutParams.Last());
      newPAs = invariantAction.PendingAsyncs.ToDictionary(decl => decl.PendingAsyncType,
        decl => (Variable)civlTypeChecker.LocalVariable($"newPAs_{decl.Name}", decl.PendingAsyncMultisetType));
    }

    private List<Declaration> GenerateBaseCaseChecker()
    {
      var requires = invariantAction.Gate.Select(g => new Requires(false, g.Expr)).ToList();
      
      var subst = targetAction.GetSubstitution(invariantAction);
      var cmds = targetAction.GetGateAsserts(subst,
        $"Gate of {targetAction.Name} fails in IS base check against invariant {invariantAction.Name}").ToList<Cmd>();

      // Construct call to inputAction
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

      cmds.Add(GetCheck(targetAction.tok, invariantAction.GetTransitionRelation(civlTypeChecker, frame),
        $"IS base of {targetAction.Name} failed"));

      return GetCheckerTuple($"IS_base_{targetAction.Name}", requires, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams, new List<Variable>(), cmds);
    }

    private List<Declaration> GenerateConclusionChecker()
    {
      var refinedAction = targetAction.RefinedAction;
      var subst = refinedAction.GetSubstitution(invariantAction);
      var requires = refinedAction.Gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr))).ToList();

      var cmds = invariantAction.GetGateAsserts(null,
        $"Gate of {invariantAction.Name} fails in IS conclusion check against {refinedAction.Name}").ToList<Cmd>();
      cmds.Add(CmdHelper.CallCmd(invariantAction.Impl.Proc, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams));
      cmds.Add(CmdHelper.AssumeCmd(NoPendingAsyncs));
      cmds.Add(GetCheck(targetAction.tok, Substituter.Apply(subst, refinedAction.GetTransitionRelation(civlTypeChecker, frame)),
        $"IS conclusion of {targetAction.Name} failed"));

      return GetCheckerTuple($"IS_conclusion_{targetAction.Name}", requires, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams, new List<Variable>(), cmds);
    }

    private List<Declaration> GenerateStepChecker(Action pendingAsync)
    {
      var pendingAsyncType = pendingAsync.ActionDecl.PendingAsyncType;
      var pendingAsyncCtor = pendingAsync.ActionDecl.PendingAsyncCtor;
      var requires = invariantAction.Gate.Select(g => new Requires(false, g.Expr)).ToList();
      var locals = new List<Variable>();
      List<Cmd> cmds = new List<Cmd>();
      cmds.Add(CmdHelper.CallCmd(invariantAction.ImplWithChoice.Proc, invariantAction.ImplWithChoice.InParams,
        invariantAction.ImplWithChoice.OutParams));
      cmds.Add(CmdHelper.AssumeCmd(ChoiceTest(pendingAsyncType)));
      cmds.Add(CmdHelper.AssumeCmd(Expr.Gt(Expr.Select(PAs(pendingAsyncType), Choice(pendingAsyncType)),
        Expr.Literal(0))));
      cmds.Add(RemoveChoice(pendingAsyncType));

      Action abs = elim[pendingAsync];
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      List<Expr> inputExprs = new List<Expr>();
      for (int i = 0; i < abs.Impl.InParams.Count; i++)
      {
        var pendingAsyncParam = ExprHelper.FieldAccess(Choice(pendingAsyncType), pendingAsyncCtor.InParams[i].Name);
        map[abs.Impl.InParams[i]] = pendingAsyncParam;
        inputExprs.Add(pendingAsyncParam);
      }
      var subst = Substituter.SubstitutionFromDictionary(map);
      cmds.AddRange(abs.GetGateAsserts(subst,
        $"Gate of {abs.Name} fails in IS induction step for invariant {invariantAction.Name}"));

      List<IdentifierExpr> outputExprs = new List<IdentifierExpr>();
      if (abs.HasPendingAsyncs)
      {
        abs.PendingAsyncs.Iter(decl =>
        {
          var ie = NewPAs(decl.PendingAsyncType);
          locals.Add(ie.Decl);
          outputExprs.Add(ie);
        });
      }
      cmds.Add(CmdHelper.CallCmd(abs.Impl.Proc, inputExprs, outputExprs));
      if (abs.HasPendingAsyncs)
      {
        var lhss = abs.PendingAsyncs.Select(decl => new SimpleAssignLhs(Token.NoToken, PAs(decl.PendingAsyncType)))
          .ToList<AssignLhs>();
        var rhss = abs.PendingAsyncs.Select(decl => ExprHelper.FunctionCall(decl.PendingAsyncAdd,
          PAs(decl.PendingAsyncType), NewPAs(decl.PendingAsyncType))).ToList<Expr>();
        cmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
      }

      cmds.Add(GetCheck(invariantAction.tok, invariantAction.GetTransitionRelation(civlTypeChecker, frame),
        $"IS step of {invariantAction.Name} with {abs.Name} failed"));

      return GetCheckerTuple($"IS_step_{invariantAction.Name}_{abs.Name}", requires,
        invariantAction.ImplWithChoice.InParams, invariantAction.ImplWithChoice.OutParams, locals, cmds);
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
    public override Expr GenerateMoverCheckAssumption(Action action, List<Variable> actionArgs, Action leftMover,
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
      return ExprHelper.ExistsExpr(
        invariantFormalMap.Values.OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList(),
        Expr.And(new[]
        {
          invariantTransitionRelationExpr, ActionExpr(action, actionArgs, invariantFormalSubst),
          LeftMoverExpr(leftMover, leftMoverArgs, invariantFormalSubst)
        }));
    }

    private Expr ActionExpr(Action action, List<Variable> actionArgs, Substitution invariantFormalSubst)
    {
      if (!elim.ContainsKey(action))
      {
        return Expr.True;
      }
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      var domainToPermissionExprsForInvariant = linearTypeChecker.PermissionExprs(invariantAction.Impl.InParams);
      var domainToPermissionExprsForAction = linearTypeChecker.PermissionExprs(actionArgs);
      var disjointnessExpr =
        Expr.And(domainToPermissionExprsForInvariant.Keys.Intersect(domainToPermissionExprsForAction.Keys).Select(
          domain =>
            linearTypeChecker.DisjointnessExprForPermissions(domain,
              domainToPermissionExprsForInvariant[domain].Concat(domainToPermissionExprsForAction[domain]))
        ).ToList());
      var pendingAsyncExprs = invariantAction.PendingAsyncs.Select(pendingAsync =>
      {
        var pendingAsyncAction = civlTypeChecker.Action(pendingAsync);
        var pendingAsyncActionParams = pendingAsyncAction.Impl.Proc.InParams
          .Concat(pendingAsyncAction.Impl.Proc.OutParams).ToList();
        var pendingAsyncFormalMap = pendingAsyncActionParams.ToDictionary(v => v,
          v => (Expr)Expr.Ident(civlTypeChecker.BoundVariable($"{pendingAsync.Name}_{v.Name}", v.TypedIdent.Type)));
        var subst = Substituter.SubstitutionFromDictionary(pendingAsyncFormalMap);
        var domainToPermissionExprsForPendingAsyncAction =
          linearTypeChecker.PermissionExprs(pendingAsync.InParams).ToDictionary(
            kv => kv.Key,
            kv => kv.Value.Select(expr => Substituter.Apply(subst, expr)));
        var conjuncts = domainToPermissionExprsForAction.Keys.Select(domain =>
        {
          var lhs = linearTypeChecker.UnionExprForPermissions(domain, domainToPermissionExprsForAction[domain]);
          var rhs = linearTypeChecker.UnionExprForPermissions(domain,
            domainToPermissionExprsForPendingAsyncAction.ContainsKey(domain)
              ? domainToPermissionExprsForPendingAsyncAction[domain]
              : new List<Expr>());
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
      var asyncLeftMover = elim.First(x => x.Value == leftMover).Key;
      var leftMoverPendingAsyncCtor = asyncLeftMover.ActionDecl.PendingAsyncCtor;
      var leftMoverPA =
        ExprHelper.FunctionCall(leftMoverPendingAsyncCtor, leftMoverArgs.Select(v => Expr.Ident(v)).ToArray());
      var leftMoverExpr = Expr.And(new[]
      {
        ChoiceTest(asyncLeftMover.ActionDecl.PendingAsyncType),
        Expr.Gt(
          Expr.Select(PAs(asyncLeftMover.ActionDecl.PendingAsyncType),
            Choice(asyncLeftMover.ActionDecl.PendingAsyncType)), Expr.Literal(0)),
        Expr.Eq(Choice(asyncLeftMover.ActionDecl.PendingAsyncType), leftMoverPA)
      });
      leftMoverExpr = Substituter.Apply(invariantFormalSubst, leftMoverExpr);
      return leftMoverExpr;
    }

    private AssertCmd GetCheck(IToken tok, Expr expr, string msg)
    {
      expr.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
      return CmdHelper.AssertCmd(tok, expr, msg);
    }

    private List<Declaration> GetCheckerTuple(string checkerName, List<Requires> requires, List<Variable> inParams,
      List<Variable> outParams, List<Variable> locals, List<Cmd> cmds)
    {
      var proc = DeclHelper.Procedure(
        civlTypeChecker.AddNamePrefix(checkerName),
        inParams,
        outParams,
        requires,
        frame.Select(Expr.Ident).ToList(),
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
        var expr = Expr.And(elim.Keys.Select(action => Expr.Eq(PAs(action.ActionDecl.PendingAsyncType),
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

    public override List<Declaration> GenerateCheckers()
    {
      var decls = new List<Declaration>();
      decls.AddRange(GenerateBaseCaseChecker());
      decls.AddRange(GenerateConclusionChecker());
      foreach (var elim in elim.Keys)
      {
        decls.AddRange(GenerateStepChecker(elim));
      }
      return decls;
    }
  }

  public static class InductiveSequentializationChecker
  {
    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      foreach (var x in civlTypeChecker.Sequentializations)
      {
        decls.AddRange(x.GenerateCheckers());
      }
      foreach (var tuple in civlTypeChecker.Sequentializations.SelectMany(x => x.AbstractionChecks).Distinct())
      {
        decls.AddRange(GenerateAbstractionChecker(civlTypeChecker, tuple.Item1, tuple.Item2));
      }
    }

    private static List<Declaration> GenerateAbstractionChecker(CivlTypeChecker civlTypeChecker, Action action, Action abs)
    {
      var requires = abs.Gate.Select(g => new Requires(false, g.Expr)).ToList();
      // The type checker ensures that the modified set of abs is a subset of the modified set of action.
      var frame = new HashSet<Variable>(action.ModifiedGlobalVars);

      var subst = action.GetSubstitution(abs);
      var cmds = action.GetGateAsserts(subst, $"Abstraction {abs.Name} fails gate of {action.Name}").ToList<Cmd>();
      cmds.Add(CmdHelper.CallCmd(action.Impl.Proc, abs.Impl.InParams, abs.Impl.OutParams));
      cmds.Add(CmdHelper.AssertCmd(abs.tok, abs.GetTransitionRelation(civlTypeChecker, frame),
        $"Abstraction {abs.Name} does not summarize {action.Name}"));

      var blocks = new List<Block> { BlockHelper.Block("init", cmds) };
      var proc = DeclHelper.Procedure(civlTypeChecker.AddNamePrefix($"AbstractionCheck_{action.Name}_{abs.Name}"),
        abs.Impl.InParams, abs.Impl.OutParams, requires, action.Impl.Proc.Modifies, new List<Ensures>());
      var impl = DeclHelper.Implementation(proc, proc.InParams, proc.OutParams, new List<Variable>(), blocks);
      return new List<Declaration>(new Declaration[] { proc, impl });
    }
  }
}
