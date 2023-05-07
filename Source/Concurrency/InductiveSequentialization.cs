using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class InductiveSequentialization
  {
    public CivlTypeChecker civlTypeChecker;
    public Action targetAction;
    public Dictionary<Action, Action> elim;
    public Action invariantAction;
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

    private void GenerateBaseCaseChecker(List<Declaration> decls)
    {
      var requires = invariantAction.Gate.Select(g => new Requires(false, g.Expr)).ToList();
      
      var subst = targetAction.GetSubstitution(invariantAction);
      var cmds = targetAction.GetGateAsserts(subst,
        $"Gate of {targetAction.Name} fails in IS base check against invariant {invariantAction.Name}").ToList<Cmd>();

      // Construct call to inputAction
      var pendingAsyncTypeToOutputParamIndex = invariantAction.PendingAsyncs.Select(x => x.PendingAsyncType)
          .Zip(Enumerable.Range(invariantAction.PendingAsyncStartIndex, invariantAction.PendingAsyncs.Count))
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

      GetCheckerTuple($"IS_base_{targetAction.Name}", requires, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams, new List<Variable>(), cmds, decls);
    }

    private void GenerateConclusionChecker(List<Declaration> decls)
    {
      var outputAction = targetAction.RefinedAction;
      var subst = outputAction.GetSubstitution(invariantAction);
      var requires = outputAction.Gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr))).ToList();

      var cmds = invariantAction.GetGateAsserts(null,
        $"Gate of {invariantAction.Name} fails in IS conclusion check against {outputAction.Name}").ToList<Cmd>();
      cmds.Add(CmdHelper.CallCmd(invariantAction.Impl.Proc, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams));
      cmds.Add(CmdHelper.AssumeCmd(NoPendingAsyncs));
      cmds.Add(GetCheck(targetAction.tok, Substituter.Apply(subst, outputAction.GetTransitionRelation(civlTypeChecker, frame)),
        $"IS conclusion of {targetAction.Name} failed"));

      GetCheckerTuple($"IS_conclusion_{targetAction.Name}", requires, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams, new List<Variable>(), cmds, decls);
    }

    private void GenerateStepChecker(Action pendingAsync, List<Declaration> decls)
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

      GetCheckerTuple($"IS_step_{invariantAction.Name}_{abs.Name}", requires,
        invariantAction.ImplWithChoice.InParams, invariantAction.ImplWithChoice.OutParams, locals, cmds, decls);
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
          var pendingAsyncAction = civlTypeChecker.Action(pendingAsync);
          var pendingAsyncActionParams = pendingAsyncAction.Impl.Proc.InParams.Concat(pendingAsyncAction.Impl.Proc.OutParams).ToList();
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
        invariantAction.ImplWithChoice.InParams.Concat(invariantAction.ImplWithChoice.OutParams).ToDictionary(v => v,
          v => (Expr)Expr.Ident(civlTypeChecker.BoundVariable($"{invariantAction.Name}_{v.Name}",
            v.TypedIdent.Type)));
      var invariantFormalSubst = Substituter.SubstitutionFromDictionary(invariantFormalMap);
      actionExpr = Substituter.Apply(invariantFormalSubst, actionExpr);
      leftMoverExpr = Substituter.Apply(invariantFormalSubst, leftMoverExpr);
      var invariantTransitionRelationExpr = ExprHelper.FunctionCall(invariantAction.InputOutputRelationWithChoice,
        invariantAction.ImplWithChoice.InParams.Concat(invariantAction.ImplWithChoice.OutParams).Select(v => invariantFormalMap[v]).ToList());
      return ExprHelper.ExistsExpr(
        invariantFormalMap.Values.OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList(),
        Expr.And(new[] { invariantTransitionRelationExpr, actionExpr, leftMoverExpr }));
    }

    private AssertCmd GetCheck(IToken tok, Expr expr, string msg)
    {
      expr.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
      return CmdHelper.AssertCmd(tok, expr, msg);
    }

    private void GetCheckerTuple(string checkerName, List<Requires> requires, List<Variable> inParams,
      List<Variable> outParams, List<Variable> locals, List<Cmd> cmds, List<Declaration> decls)
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
      decls.Add(proc);
      decls.Add(impl);
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

    public void AddCheckers(List<Declaration> decls)
    {
      GenerateBaseCaseChecker(decls);
      GenerateConclusionChecker(decls);
      foreach (var elim in elim.Keys)
      {
        GenerateStepChecker(elim, decls);
      }
    }
  }

  public static class InductiveSequentializationChecker
  {
    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      foreach (var x in civlTypeChecker.InductiveSequentializations)
      {
        x.AddCheckers(decls);
      }
      foreach (var absCheck in civlTypeChecker.InductiveSequentializations.SelectMany(x => x.elim)
                 .Where(kv => kv.Key != kv.Value).Distinct())
      {
        GenerateAbstractionChecker(civlTypeChecker, absCheck.Key, absCheck.Value, decls);
      }
    }

    private static void GenerateAbstractionChecker(CivlTypeChecker civlTypeChecker, Action action, Action abs,
      List<Declaration> decls)
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
      decls.Add(proc);
      decls.Add(impl);
    }
  }
}
