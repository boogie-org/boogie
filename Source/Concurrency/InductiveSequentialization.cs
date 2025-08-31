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
    protected HashSet<Action> eliminatedActions;

    protected Sequentialization(CivlTypeChecker civlTypeChecker, Action targetAction)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.targetAction = targetAction;
      this.eliminatedActions = new HashSet<Action>(EliminatedActionDecls.Select(x => civlTypeChecker.Action(x)));
    }

    public IEnumerable<ActionDecl> EliminatedActionDecls => targetAction.ActionDecl.EliminatedActionDecls();

    public IEnumerable<Action> EliminatedActions => eliminatedActions;

    public int Layer => targetAction.LayerRange.UpperLayer;

    protected virtual List<Declaration> GenerateCheckers()
    {
      return new List<Declaration>();
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
      if (cmd is CallCmd callCmd && callCmd.IsAsync)
      {
        var actionDecl = (ActionDecl)callCmd.Proc;
        var pendingAsyncType = actionDecl.PendingAsyncType;
        if (eliminatedPendingAsyncs.ContainsKey(pendingAsyncType))
        {
          var newCallee = eliminatedPendingAsyncs[pendingAsyncType].Proc;
          var newCallCmd = new CallCmd(callCmd.tok, newCallee.Name, callCmd.Ins, new List<IdentifierExpr>())
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

    private IEnumerable<Expr> InputMapWellFormedExprs()
    {
      var scope = invariantAction.Impl.InParams.Union(invariantAction.UsedGlobalVars);
      return civlTypeChecker.linearTypeChecker.MapWellFormedExpressions(scope);
    }

    private IEnumerable<Expr> InputDisjointnessExprs()
    {
      var scope = invariantAction.Impl.InParams.Union(invariantAction.UsedGlobalVars);
      var linearScope = scope.Where(x => LinearTypeChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(x)));
      return civlTypeChecker.linearTypeChecker.MapWellFormedExpressions(scope)
        .Union(civlTypeChecker.linearTypeChecker.DisjointnessExprForEachDomain(linearScope));
    }

    private List<Declaration> GenerateBaseCaseChecker()
    {
      var inputDisjointnessExprs = InputDisjointnessExprs();
      var mapWellFormedExprs = InputMapWellFormedExprs();
      var requires = invariantAction.Gate.Select(g => new Requires(false, g.Expr))
        .Concat(inputDisjointnessExprs.Concat(mapWellFormedExprs).Select(expr => new Requires(false, expr)))
        .ToList();

      var subst = targetAction.GetSubstitution(invariantAction);
      var cmds = targetAction.GetGateAsserts(subst,
        $"Gate of {targetAction.Name} fails in base check against invariant {invariantAction.Name}").ToList<Cmd>();

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
        $"base of {targetAction.Name} failed"));

      return GetCheckerTuple($"Base_{targetAction.Name}", requires, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams, new List<Variable>(), cmds);
    }

    private List<Declaration> GenerateConclusionChecker()
    {
      var inputDisjointnessExprs = InputDisjointnessExprs();
      var mapWellFormedExprs = InputMapWellFormedExprs();
      var refinedAction = targetAction.RefinedAction;
      var subst = refinedAction.GetSubstitution(invariantAction);
      var requires = refinedAction.Gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr)))
        .Concat(inputDisjointnessExprs.Concat(mapWellFormedExprs).Select(expr => new Requires(false, expr)))
        .ToList();

      var cmds = invariantAction.GetGateAsserts(null,
        $"Gate of {invariantAction.Name} fails in conclusion check against {refinedAction.Name}").ToList<Cmd>();
      cmds.Add(CmdHelper.CallCmd(invariantAction.Impl.Proc, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams));
      cmds.Add(CmdHelper.AssumeCmd(NoPendingAsyncs));
      var frame = new HashSet<Variable>(civlTypeChecker.GlobalVariablesAtLayer(targetAction.LayerRange.UpperLayer));
      cmds.Add(GetCheck(targetAction.tok, Substituter.Apply(subst, refinedAction.GetTransitionRelation(civlTypeChecker, frame)),
        $"conclusion of {targetAction.Name} failed"));

      return GetCheckerTuple($"Conclusion_{targetAction.Name}", requires, invariantAction.Impl.InParams,
        invariantAction.Impl.OutParams, new List<Variable>(), cmds);
    }

    private List<Declaration> GenerateStepChecker(Action pendingAsync)
    {
      var inputDisjointnessExprs = InputDisjointnessExprs();
      var mapWellFormedExprs = InputMapWellFormedExprs();
      var pendingAsyncType = pendingAsync.ActionDecl.PendingAsyncType;
      var pendingAsyncCtor = pendingAsync.ActionDecl.PendingAsyncCtor;
      var requires = invariantAction.Gate.Select(g => new Requires(false, g.Expr))
        .Concat(inputDisjointnessExprs.Concat(mapWellFormedExprs).Select(expr => new Requires(false, expr)))
        .ToList();
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

      var inputExprs = new List<Expr>();
      for (int i = 0; i < pendingAsync.Impl.InParams.Count; i++)
      {
        inputExprs.Add(ExprHelper.FieldAccess(Choice(pendingAsyncType), pendingAsyncCtor.InParams[i].Name));
      }
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, inputExprs);
      cmds.AddRange(pendingAsync.GetGateAsserts(
        Substituter.SubstitutionFromDictionary(pendingAsync.Impl.InParams.Zip(inputExprs).ToDictionary(x => x.Item1, x => x.Item2)),
        $"Gate of {pendingAsync.Name} fails in induction step for invariant {invariantAction.Name}"));
      cmds.AddRange(pendingAsync.Preconditions(Layer,
        Substituter.SubstitutionFromDictionary(pendingAsync.ActionDecl.InParams.Zip(inputExprs).ToDictionary(x => x.Item1, x => x.Item2))));

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
        $"step of {invariantAction.Name} with {pendingAsync.Name} failed"));

      return GetCheckerTuple($"Step_{invariantAction.Name}_{pendingAsync.Name}", requires,
        invariantAction.ImplWithChoice.InParams, invariantAction.ImplWithChoice.OutParams, locals, cmds);
    }

    private List<Declaration> GetCheckerTuple(string checkerName, List<Requires> requires, List<Variable> inParams,
      List<Variable> outParams, List<Variable> locals, List<Cmd> cmds)
    {
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, cmds, ResolutionContext.State.Two);
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
      foreach (var elim in eliminatedActions)
      {
        decls.AddRange(GenerateStepChecker(elim));
      }
      return decls;
    }
  }
}