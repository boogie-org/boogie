using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
  public class InductiveSequentialization
  {
    public CivlTypeChecker civlTypeChecker;
    public Action targetAction;
    public Action invariantAction;
    public Dictionary<Action, Action> elim;

    private HashSet<Variable> frame;
    private IdentifierExpr choice;
    private Dictionary<CtorType, Variable> newPAs;

    public InductiveSequentialization(CivlTypeChecker civlTypeChecker, Action targetAction,
      Action invariantAction, Dictionary<Action, Action> elim)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.targetAction = targetAction;
      this.invariantAction = invariantAction;
      this.elim = elim;

      // The type checker ensures that the set of modified variables of an invariant is a superset of
      // - the modified set of each of each eliminated and abstract action associated with this invariant.
      // - the target and refined action of every application of inductive sequentialization that refers to this invariant.
      frame = new HashSet<Variable>(invariantAction.ModifiedGlobalVars);
      choice = Expr.Ident(invariantAction.ImplWithChoice.OutParams.Last());
      newPAs = invariantAction.PendingAsyncs.ToDictionary(decl => decl.PendingAsyncType,
        decl => (Variable)civlTypeChecker.LocalVariable($"newPAs_{decl.Name}", decl.PendingAsyncMultisetType));
    }

    public Tuple<Procedure, Implementation> GenerateBaseCaseChecker(Action inputAction)
    {
      var requires = invariantAction.Gate.Select(g => new Requires(false, g.Expr)).ToList();
      
      var subst = GetSubstitution(inputAction, invariantAction);
      List<Cmd> cmds = GetGateAsserts(inputAction, subst,
          $"Gate of {inputAction.Name} fails in IS base check against invariant {invariantAction.Name}")
        .ToList<Cmd>();

      // Construct call to inputAction
      var pendingAsyncTypeToOutputParamIndex = invariantAction.PendingAsyncs.Select((action, i) => (action, i))
        .ToDictionary(tuple => tuple.action.PendingAsyncType, tuple => tuple.action.PendingAsyncStartIndex + tuple.i);
      var outputVars = new List<Variable>(invariantAction.Impl.OutParams.Take(invariantAction.ActionDecl.PendingAsyncStartIndex));
      outputVars.AddRange(inputAction.PendingAsyncs.Select(action =>
        invariantAction.Impl.OutParams[pendingAsyncTypeToOutputParamIndex[action.PendingAsyncType]]));
      cmds.Add(CmdHelper.CallCmd(inputAction.Impl.Proc, invariantAction.Impl.InParams, outputVars));
      
      // Assign empty multiset to the rest
      var remainderPendingAsyncs = invariantAction.PendingAsyncs.Except(inputAction.PendingAsyncs);
      if (remainderPendingAsyncs.Any())
      {
        var lhss = remainderPendingAsyncs.Select(decl =>
            Expr.Ident(invariantAction.Impl.OutParams[pendingAsyncTypeToOutputParamIndex[decl.PendingAsyncType]]))
          .ToList();
        var rhss = remainderPendingAsyncs.Select(decl =>
          ExprHelper.FunctionCall(decl.PendingAsyncConst, Expr.Literal(0))).ToList<Expr>();
        cmds.Add(CmdHelper.AssignCmd(lhss, rhss));
      }
      
      cmds.Add(GetCheck(inputAction.tok, GetTransitionRelation(invariantAction),
        $"IS base of {inputAction.Name} failed"));

      return GetCheckerTuple($"IS_base_{inputAction.Name}", requires, new List<Variable>(), cmds);
    }

    public Tuple<Procedure, Implementation> GenerateConclusionChecker(Action inputAction)
    {
      var outputAction = inputAction.RefinedAction;
      var subst = GetSubstitution(outputAction, invariantAction);
      var requires = outputAction.Gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr))).ToList();

      List<Cmd> cmds = GetGateAsserts(invariantAction, null,
          $"Gate of {invariantAction.Name} fails in IS conclusion check against {outputAction.Name}")
        .ToList<Cmd>();
      cmds.Add(CmdHelper.CallCmd(invariantAction.Impl.Proc, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams));
      cmds.Add(CmdHelper.AssumeCmd(NoPendingAsyncs));
      cmds.Add(GetCheck(inputAction.tok, Substituter.Apply(subst, GetTransitionRelation(outputAction)),
        $"IS conclusion of {inputAction.Name} failed"));

      return GetCheckerTuple($"IS_conclusion_{inputAction.Name}", requires, new List<Variable>(), cmds);
    }

    public Tuple<Procedure, Implementation> GenerateStepChecker(Action pendingAsync)
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
      cmds.AddRange(GetGateAsserts(abs, subst,
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

      cmds.Add(GetCheck(invariantAction.tok, GetTransitionRelation(invariantAction),
        $"IS step of {invariantAction.Name} with {abs.Name} failed"));
      
      return GetCheckerTuple($"IS_step_{invariantAction.Name}_{abs.Name}", requires, locals, cmds);
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
    public Expr GenerateMoverCheckAssumption(Action action, List<Variable> actionArgs, Action leftMover, List<Variable> leftMoverArgs)
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      Expr actionExpr = Expr.True;
      if (elim.ContainsKey(action))
      {
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
          var pendingAsyncFormalMap =
            pendingAsync.InParams.Concat(pendingAsync.OutParams).ToDictionary(v => v,
              v => (Expr)Expr.Ident(civlTypeChecker.BoundVariable($"{pendingAsync.Name}_{v.Name}",
                v.TypedIdent.Type)));
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
          var pendingAsyncTransitionRelationExpr = ExprHelper.FunctionCall(civlTypeChecker.procToAtomicAction[pendingAsync].InputOutputRelation,
            pendingAsync.InParams.Concat(pendingAsync.OutParams).Select(v => pendingAsyncFormalMap[v])
              .ToList());
          var membershipExpr =
            Expr.Gt(
              Expr.Select(PAs(pendingAsync.PendingAsyncType),
                ExprHelper.FunctionCall(pendingAsync.PendingAsyncCtor,
                  pendingAsync.InParams.Select(v => pendingAsyncFormalMap[v]).ToList())), Expr.Literal(0));
          return ExprHelper.ExistsExpr(
            pendingAsyncFormalMap.Values.OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList(),
            Expr.And(conjuncts.Concat(new[] { membershipExpr, pendingAsyncTransitionRelationExpr })));
        });
        actionExpr = Expr.Or(pendingAsyncExprs.Append(disjointnessExpr));
      }

      var asyncLeftMover = elim.First(x => x.Value == leftMover).Key;
      var leftMoverPendingAsyncCtor = asyncLeftMover.ActionDecl.PendingAsyncCtor;
      var leftMoverPA =
        ExprHelper.FunctionCall(leftMoverPendingAsyncCtor, leftMoverArgs.Select(v => Expr.Ident(v)).ToArray());
      var leftMoverExpr = Expr.And(new[]
      {
        ChoiceTest(asyncLeftMover.ActionDecl.PendingAsyncType),
        Expr.Gt(Expr.Select(PAs(asyncLeftMover.ActionDecl.PendingAsyncType), Choice(asyncLeftMover.ActionDecl.PendingAsyncType)), Expr.Literal(0)),
        Expr.Eq(Choice(asyncLeftMover.ActionDecl.PendingAsyncType), leftMoverPA)
      });

      var invariantFormalMap =
        invariantAction.Impl.InParams.Concat(invariantAction.Impl.OutParams).ToDictionary(v => v,
          v => (Expr)Expr.Ident(civlTypeChecker.BoundVariable($"{invariantAction.Name}_{v.Name}",
            v.TypedIdent.Type)));
      var invariantFormalSubst = Substituter.SubstitutionFromDictionary(invariantFormalMap);
      actionExpr = Substituter.Apply(invariantFormalSubst, actionExpr);
      leftMoverExpr = Substituter.Apply(invariantFormalSubst, leftMoverExpr);
      var invariantTransitionRelationExpr = Substituter.Apply(invariantFormalSubst,
        TransitionRelationComputation.Refinement(civlTypeChecker, invariantAction.ImplWithChoice, frame));
      return ExprHelper.ExistsExpr(
        invariantFormalMap.Values.OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList(),
        Expr.And(new[] { invariantTransitionRelationExpr, actionExpr, leftMoverExpr }));
    }

    private AssertCmd GetCheck(IToken tok, Expr expr, string msg)
    {
      expr.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
      return CmdHelper.AssertCmd(tok, expr, msg);
    }

    public static IEnumerable<AssertCmd> GetGateAsserts(Action action, Substitution subst, string msg)
    {
      foreach (var gate in action.Gate)
      {
        AssertCmd cmd =
            subst != null
          ? (AssertCmd) Substituter.Apply(subst, gate)
          : new AssertCmd(gate.tok, gate.Expr);
        cmd.Description = new FailureOnlyDescription(msg);
        yield return cmd;
      }
    }

    private Tuple<Procedure, Implementation> GetCheckerTuple(string checkerName,
      List<Requires> requires, List<Variable> locals, List<Cmd> cmds)
    {
      var proc = DeclHelper.Procedure(
        civlTypeChecker.AddNamePrefix(checkerName),
        invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams,
        requires,
        frame.Select(Expr.Ident).ToList(),
        new List<Ensures>());
      var impl = DeclHelper.Implementation(
        proc,
        proc.InParams,
        proc.OutParams,
        locals,
        new List<Block> { BlockHelper.Block(checkerName, cmds) });
      return Tuple.Create(proc, impl);
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

    public static Substitution GetSubstitution(Action from, Action to)
    {
      Debug.Assert(from.ActionDecl.PendingAsyncStartIndex == to.ActionDecl.PendingAsyncStartIndex);
      Debug.Assert(from.Impl.InParams.Count == to.Impl.InParams.Count);
      Debug.Assert(from.Impl.OutParams.Count <= to.Impl.OutParams.Count);
      
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      for (int i = 0; i < from.Impl.InParams.Count; i++)
      {
        map[from.Impl.InParams[i]] = Expr.Ident(to.Impl.InParams[i]);
      }
      for (int i = 0; i < from.ActionDecl.PendingAsyncStartIndex; i++)
      {
        map[from.Impl.OutParams[i]] = Expr.Ident(to.Impl.OutParams[i]);
      }
      for (int i = from.ActionDecl.PendingAsyncStartIndex; i < from.Impl.OutParams.Count; i++)
      {
        var formal = from.Impl.OutParams[i];
        var pendingAsyncType = (CtorType)((MapType)formal.TypedIdent.Type).Arguments[0];
        map[formal] = Expr.Ident(to.PAs(pendingAsyncType));
      }
      return Substituter.SubstitutionFromDictionary(map);
    }

    private Expr GetTransitionRelation(Action action)
    {
      return TransitionRelationComputation.Refinement(civlTypeChecker, action.Impl, frame);
    }

    // TODO: Check that choice only occurs as one side of a positive equality.
    private class ChoiceEraser : Duplicator
    {
      private Variable choice;

      public ChoiceEraser(Variable choice)
      {
        this.choice = choice;
      }

      public override Expr VisitExpr(Expr node)
      {
        if (node is NAryExpr nary &&
            nary.Fun is BinaryOperator op &&
            op.Op == BinaryOperator.Opcode.Eq &&
            VariableCollector.Collect(node).Contains(choice))
        {
          return Expr.True;
        }

        return base.VisitExpr(node);
      }
    }
  }

  public static class InductiveSequentializationChecker
  {
    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      foreach (var x in civlTypeChecker.inductiveSequentializations)
      {
        AddCheck(x.GenerateBaseCaseChecker(x.targetAction), decls);
        AddCheck(x.GenerateConclusionChecker(x.targetAction), decls);
        foreach (var elim in x.elim.Keys)
        {
          AddCheck(x.GenerateStepChecker(elim), decls);
        }
      }

      var absChecks = civlTypeChecker.inductiveSequentializations
        .SelectMany(x => x.elim)
        .Where(kv => kv.Key != kv.Value)
        .Distinct();
      
      foreach (var absCheck in absChecks)
      {
        AddCheck(GenerateAbstractionChecker(civlTypeChecker, absCheck.Key, absCheck.Value), decls);
      }
    }

    private static Tuple<Procedure, Implementation> GenerateAbstractionChecker(CivlTypeChecker civlTypeChecker, Action action, Action abs)
    {
      var requires = abs.Gate.Select(g => new Requires(false, g.Expr)).ToList();
      // The type checker ensures that the modified set of abs is a subset of the modified set of action.
      var frame = new HashSet<Variable>(action.ModifiedGlobalVars);

      var subst = InductiveSequentialization.GetSubstitution(action, abs);
      List<Cmd> cmds = InductiveSequentialization.GetGateAsserts(action, subst,
        $"Abstraction {abs.Name} fails gate of {action.Name}").ToList<Cmd>();
      cmds.Add(
        CmdHelper.CallCmd(
          action.Impl.Proc,
          abs.Impl.InParams,
          abs.Impl.OutParams
        ));
      cmds.Add(
        CmdHelper.AssertCmd(
          abs.tok,
          TransitionRelationComputation.Refinement(civlTypeChecker, abs.Impl, frame),
          $"Abstraction {abs.Name} does not summarize {action.Name}"
        ));

      var blocks = new List<Block> { BlockHelper.Block("init", cmds) };

      var proc = DeclHelper.Procedure(
        civlTypeChecker.AddNamePrefix($"AbstractionCheck_{action.Name}_{abs.Name}"),
        abs.Impl.InParams,
        abs.Impl.OutParams,
        requires,
        action.Impl.Proc.Modifies,
        new List<Ensures>());
      var impl = DeclHelper.Implementation(
        proc,
        proc.InParams,
        proc.OutParams,
        new List<Variable>(),
        blocks);
      return Tuple.Create(proc, impl);
    }

    private static void AddCheck(Tuple<Procedure, Implementation> t, List<Declaration> decls)
    {
      decls.Add(t.Item1);
      decls.Add(t.Item2);
    }
  }
}
