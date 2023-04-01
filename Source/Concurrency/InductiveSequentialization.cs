using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
  public class InductiveSequentialization
  {
    public CivlTypeChecker civlTypeChecker;
    public AtomicAction targetAction;
    public InvariantAction invariantAction;
    public Dictionary<AsyncAction, AtomicAction> elim;

    private HashSet<Variable> frame;
    private IdentifierExpr choice;
    private Dictionary<CtorType, Variable> newPAs;

    private ConcurrencyOptions Options => civlTypeChecker.Options;

    public InductiveSequentialization(CivlTypeChecker civlTypeChecker, AtomicAction targetAction,
      InvariantAction invariantAction, Dictionary<AsyncAction, AtomicAction> elim)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.targetAction = targetAction;
      this.invariantAction = invariantAction;
      this.elim = elim;

      // The type checker ensures that the set of modified variables of an invariant is a superset of
      // - the modified set of each of each eliminated and abstract action associated with this invariant.
      // - the target and refined action of every application of inductive sequentialization that refers to this invariant.
      frame = new HashSet<Variable>(invariantAction.modifiedGlobalVars);
      choice = Expr.Ident(invariantAction.impl.OutParams.Last());
      newPAs = invariantAction.pendingAsyncs.ToDictionary(action => action.pendingAsyncType,
        action => (Variable)civlTypeChecker.LocalVariable($"newPAs_{action.impl.Name}",
          action.pendingAsyncMultisetType));
    }

    public Tuple<Procedure, Implementation> GenerateBaseCaseChecker(AtomicAction inputAction)
    {
      var requires = invariantAction.gate.Select(g => new Requires(false, g.Expr)).ToList();
      
      var subst = GetSubstitution(inputAction, invariantAction);
      List<Cmd> cmds = GetGateAsserts(inputAction, subst,
          $"Gate of {inputAction.proc.Name} fails in IS base check against invariant {invariantAction.proc.Name}")
        .ToList<Cmd>();

      // Construct call to inputAction
      var pendingAsyncTypeToOutputParamIndex = invariantAction.pendingAsyncs.Select((action, i) => (action, i))
        .ToDictionary(tuple => tuple.action.pendingAsyncType, tuple => tuple.action.PendingAsyncStartIndex + tuple.i);
      var outputVars = new List<Variable>(invariantAction.impl.OutParams.Take(invariantAction.PendingAsyncStartIndex));
      outputVars.AddRange(inputAction.pendingAsyncs.Select(action =>
        invariantAction.impl.OutParams[pendingAsyncTypeToOutputParamIndex[action.pendingAsyncType]]));
      cmds.Add(CmdHelper.CallCmd(inputAction.proc, invariantAction.impl.InParams, outputVars));
      
      // Assign empty multiset to the rest
      var remainderPendingAsyncs = invariantAction.pendingAsyncs.Except(inputAction.pendingAsyncs);
      if (remainderPendingAsyncs.Count() > 0)
      {
        var lhss = remainderPendingAsyncs.Select(action =>
            Expr.Ident(invariantAction.impl.OutParams[pendingAsyncTypeToOutputParamIndex[action.pendingAsyncType]]))
          .ToList();
        var rhss = remainderPendingAsyncs.Select(action =>
          ExprHelper.FunctionCall(action.pendingAsyncConst, Expr.Literal(0))).ToList<Expr>();
        cmds.Add(CmdHelper.AssignCmd(lhss, rhss));
      }
      
      cmds.Add(GetCheck(inputAction.proc.tok, GetTransitionRelation(invariantAction),
        $"IS base of {inputAction.proc.Name} failed"));

      return GetCheckerTuple($"IS_base_{inputAction.proc.Name}", requires, new List<Variable>(), cmds);
    }

    public Tuple<Procedure, Implementation> GenerateConclusionChecker(AtomicAction inputAction)
    {
      var outputAction = inputAction.refinedAction;
      var subst = GetSubstitution(outputAction, invariantAction);
      var requires = outputAction.gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr))).ToList();

      List<Cmd> cmds = GetGateAsserts(invariantAction, null,
          $"Gate of {invariantAction.proc.Name} fails in IS conclusion check against {outputAction.proc.Name}")
        .ToList<Cmd>();
      cmds.Add(GetCallCmd(invariantAction));
      cmds.Add(CmdHelper.AssumeCmd(NoPendingAsyncs));
      cmds.Add(GetCheck(inputAction.proc.tok, Substituter.Apply(subst, GetTransitionRelation(outputAction)),
        $"IS conclusion of {inputAction.proc.Name} failed"));

      return GetCheckerTuple($"IS_conclusion_{inputAction.proc.Name}", requires, new List<Variable>(), cmds);
    }

    public Tuple<Procedure, Implementation> GenerateStepChecker(AsyncAction pendingAsync)
    {
      var pendingAsyncType = pendingAsync.pendingAsyncType;
      var pendingAsyncCtor = pendingAsync.pendingAsyncCtor;
      var requires = invariantAction.gate.Select(g => new Requires(false, g.Expr)).ToList();
      var locals = new List<Variable>();
      List<Cmd> cmds = new List<Cmd>();
      cmds.Add(GetCallCmd(invariantAction));
      cmds.Add(CmdHelper.AssumeCmd(ChoiceTest(pendingAsyncType)));
      cmds.Add(CmdHelper.AssumeCmd(Expr.Gt(Expr.Select(PAs(pendingAsyncType), Choice(pendingAsyncType)),
        Expr.Literal(0))));
      cmds.Add(RemoveChoice(pendingAsyncType));

      AtomicAction abs = elim[pendingAsync];
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      List<Expr> inputExprs = new List<Expr>();
      for (int i = 0; i < abs.impl.InParams.Count; i++)
      {
        var pendingAsyncParam = ExprHelper.FieldAccess(Choice(pendingAsyncType), pendingAsyncCtor.InParams[i].Name);
        map[abs.impl.InParams[i]] = pendingAsyncParam;
        inputExprs.Add(pendingAsyncParam);
      }
      var subst = Substituter.SubstitutionFromDictionary(map);
      cmds.AddRange(GetGateAsserts(abs, subst,
        $"Gate of {abs.proc.Name} fails in IS induction step for invariant {invariantAction.proc.Name}"));

      List<IdentifierExpr> outputExprs = new List<IdentifierExpr>();
      if (abs.HasPendingAsyncs)
      {
        abs.pendingAsyncs.Iter(action =>
        {
          var ie = NewPAs(action.pendingAsyncType);
          locals.Add(ie.Decl);
          outputExprs.Add(ie);
        });
      }
      cmds.Add(CmdHelper.CallCmd(abs.proc, inputExprs, outputExprs));
      if (abs.HasPendingAsyncs)
      {
        var lhss = abs.pendingAsyncs.Select(action => new SimpleAssignLhs(Token.NoToken, PAs(action.pendingAsyncType)))
          .ToList<AssignLhs>();
        var rhss = abs.pendingAsyncs.Select(action => ExprHelper.FunctionCall(action.pendingAsyncAdd,
          PAs(action.pendingAsyncType), NewPAs(action.pendingAsyncType))).ToList<Expr>();
        cmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
      }

      cmds.Add(GetCheck(invariantAction.proc.tok, GetTransitionRelation(invariantAction),
        $"IS step of {invariantAction.proc.Name} with {abs.proc.Name} failed"));
      
      return GetCheckerTuple($"IS_step_{invariantAction.proc.Name}_{abs.proc.Name}", requires, locals, cmds);
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
     * - The invocation of action is such that either:
     *   (1) the permissions in the invocation are disjoint from the permissions in the invariant invocation, or
     *   (2) the invocation is one of the pending asyncs created by the invariant invocation, or
     *   (3) the permissions in the invocation is contained in the permissions of one of the pending asyncs created by the invariant invocation.
     */
    public Expr GenerateMoverCheckAssumption(AtomicAction action, List<Variable> actionArgs, AtomicAction leftMover, List<Variable> leftMoverArgs)
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      Expr actionExpr = Expr.True;
      if (action is AsyncAction asyncAtomicAction && elim.ContainsKey(asyncAtomicAction))
      {
        var domainToPermissionExprsForInvariant = linearTypeChecker.PermissionExprs(invariantAction.impl.InParams);
        var domainToPermissionExprsForAction = linearTypeChecker.PermissionExprs(actionArgs);
        var disjointnessExpr =
          Expr.And(domainToPermissionExprsForInvariant.Keys.Intersect(domainToPermissionExprsForAction.Keys).Select(
            domain =>
              linearTypeChecker.DisjointnessExprForPermissions(domain,
                domainToPermissionExprsForInvariant[domain].Concat(domainToPermissionExprsForAction[domain]))
          ).ToList());
        var actionPA =
          ExprHelper.FunctionCall(asyncAtomicAction.pendingAsyncCtor, actionArgs.Select(v => Expr.Ident(v)).ToArray());
        var pendingAsyncExprs = invariantAction.pendingAsyncs.Select(pendingAsync =>
        {
          var pendingAsyncFormalMap =
            pendingAsync.impl.InParams.Concat(pendingAsync.impl.OutParams).ToDictionary(v => v,
              v => (Expr)Expr.Ident(civlTypeChecker.BoundVariable($"{pendingAsync.proc.Name}_{v.Name}",
                v.TypedIdent.Type)));
          var subst = Substituter.SubstitutionFromDictionary(pendingAsyncFormalMap);
          var domainToPermissionExprsForPendingAsyncAction =
            linearTypeChecker.PermissionExprs(pendingAsync.impl.InParams).ToDictionary(
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
          var pendingAsyncTransitionRelationExpr = ExprHelper.FunctionCall(pendingAsync.inputOutputRelation,
            pendingAsync.impl.InParams.Concat(pendingAsync.impl.OutParams).Select(v => pendingAsyncFormalMap[v])
              .ToList());
          var membershipExpr =
            Expr.Gt(
              Expr.Select(PAs(pendingAsync.pendingAsyncType),
                ExprHelper.FunctionCall(pendingAsync.pendingAsyncCtor,
                  pendingAsync.impl.InParams.Select(v => pendingAsyncFormalMap[v]).ToList())), Expr.Literal(0));
          return ExprHelper.ExistsExpr(
            pendingAsyncFormalMap.Values.OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList(),
            Expr.And(conjuncts.Concat(new[] { membershipExpr, pendingAsyncTransitionRelationExpr })));
        });
        actionExpr = Expr.Or(new[]
          {
            disjointnessExpr, Expr.Gt(Expr.Select(PAs(asyncAtomicAction.pendingAsyncType), actionPA), Expr.Literal(0))
          }
          .Concat(pendingAsyncExprs));
      }

      var asyncLeftMover = elim.First(x => x.Value == leftMover).Key;
      var leftMoverPendingAsyncCtor = asyncLeftMover.pendingAsyncCtor;
      var leftMoverPA =
        ExprHelper.FunctionCall(leftMoverPendingAsyncCtor, leftMoverArgs.Select(v => Expr.Ident(v)).ToArray());
      var leftMoverExpr = Expr.And(new[]
      {
        ChoiceTest(asyncLeftMover.pendingAsyncType),
        Expr.Gt(Expr.Select(PAs(asyncLeftMover.pendingAsyncType), Choice(asyncLeftMover.pendingAsyncType)), Expr.Literal(0)),
        Expr.Eq(Choice(asyncLeftMover.pendingAsyncType), leftMoverPA)
      });

      var invariantFormalMap =
        invariantAction.impl.InParams.Concat(invariantAction.impl.OutParams).ToDictionary(v => v,
          v => (Expr)Expr.Ident(civlTypeChecker.BoundVariable($"{invariantAction.proc.Name}_{v.Name}",
            v.TypedIdent.Type)));
      var invariantFormalSubst = Substituter.SubstitutionFromDictionary(invariantFormalMap);
      actionExpr = Substituter.Apply(invariantFormalSubst, actionExpr);
      leftMoverExpr = Substituter.Apply(invariantFormalSubst, leftMoverExpr);
      var invariantTransitionRelationExpr = ExprHelper.FunctionCall(invariantAction.inputOutputRelation,
        invariantAction.impl.InParams.Concat(invariantAction.impl.OutParams).Select(v => invariantFormalMap[v]).ToList());
      return ExprHelper.ExistsExpr(
        invariantFormalMap.Values.OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList(),
        Expr.And(new[] { invariantTransitionRelationExpr, actionExpr, leftMoverExpr }));
    }

    private CallCmd GetCallCmd(Action callee)
    {
      return CmdHelper.CallCmd(
        callee.proc,
        invariantAction.impl.InParams,
        invariantAction.impl.OutParams.GetRange(0, callee.impl.OutParams.Count)
      );
    }

    private AssertCmd GetCheck(IToken tok, Expr expr, string msg)
    {
      expr.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
      return CmdHelper.AssertCmd(tok, expr, msg);
    }

    public static IEnumerable<AssertCmd> GetGateAsserts(Action action, Substitution subst, string msg)
    {
      foreach (var gate in action.gate)
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
        invariantAction.impl.InParams,
        invariantAction.impl.OutParams,
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
        var expr = Expr.And(elim.Keys.Select(action => Expr.Eq(PAs(action.pendingAsyncType),
          ExprHelper.FunctionCall(action.pendingAsyncConst, Expr.Literal(0)))));
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
      Debug.Assert(from.PendingAsyncStartIndex == to.PendingAsyncStartIndex);
      Debug.Assert(from.impl.InParams.Count == to.impl.InParams.Count);
      Debug.Assert(from.impl.OutParams.Count <= to.impl.OutParams.Count);
      
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      for (int i = 0; i < from.impl.InParams.Count; i++)
      {
        map[from.impl.InParams[i]] = Expr.Ident(to.impl.InParams[i]);
      }
      for (int i = 0; i < from.PendingAsyncStartIndex; i++)
      {
        map[from.impl.OutParams[i]] = Expr.Ident(to.impl.OutParams[i]);
      }
      for (int i = from.PendingAsyncStartIndex; i < from.impl.OutParams.Count; i++)
      {
        var formal = from.impl.OutParams[i];
        var pendingAsyncType = (CtorType)((MapType)formal.TypedIdent.Type).Arguments[0];
        map[formal] = Expr.Ident(to.PAs(pendingAsyncType));
      }
      return Substituter.SubstitutionFromDictionary(map);
    }

    private Expr GetInvariantTransitionRelationWithChoice()
    {
      return TransitionRelationComputation.Refinement(civlTypeChecker, invariantAction, frame);
    }

    private Expr GetTransitionRelation(Action action)
    {
      var tr = TransitionRelationComputation.Refinement(civlTypeChecker, action, frame);
      if (action == invariantAction)
      {
        return new ChoiceEraser(invariantAction.impl.OutParams.Last()).VisitExpr(tr);
      }
      return tr;
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

    private static Tuple<Procedure, Implementation> GenerateAbstractionChecker(CivlTypeChecker civlTypeChecker, AtomicAction action, AtomicAction abs)
    {
      var requires = abs.gate.Select(g => new Requires(false, g.Expr)).ToList();
      // The type checker ensures that the modified set of abs is a subset of the modified set of action.
      var frame = new HashSet<Variable>(action.modifiedGlobalVars);

      var subst = InductiveSequentialization.GetSubstitution(action, abs);
      List<Cmd> cmds = InductiveSequentialization.GetGateAsserts(action, subst,
        $"Abstraction {abs.proc.Name} fails gate of {action.proc.Name}").ToList<Cmd>();
      cmds.Add(
        CmdHelper.CallCmd(
          action.proc,
          abs.impl.InParams,
          abs.impl.OutParams
        ));
      cmds.Add(
        CmdHelper.AssertCmd(
          abs.proc.tok,
          TransitionRelationComputation.Refinement(civlTypeChecker, abs, frame),
          $"Abstraction {abs.proc.Name} does not summarize {action.proc.Name}"
        ));

      var blocks = new List<Block> { BlockHelper.Block("init", cmds) };

      var proc = DeclHelper.Procedure(
        civlTypeChecker.AddNamePrefix($"AbstractionCheck_{action.proc.Name}_{abs.proc.Name}"),
        abs.impl.InParams,
        abs.impl.OutParams,
        requires,
        action.proc.Modifies,
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
