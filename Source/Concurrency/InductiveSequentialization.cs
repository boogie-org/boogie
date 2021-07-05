using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class InductiveSequentialization
  {
    public CivlTypeChecker civlTypeChecker;
    public AtomicAction inputAction;
    public AtomicAction outputAction;
    public AtomicAction invariantAction;
    public Dictionary<AtomicAction, AtomicAction> elim;

    private HashSet<Variable> frame;
    private List<IdentifierExpr> modifies;
    private IdentifierExpr choice;
    private IdentifierExpr newPAs;
    private string checkName;

    public InductiveSequentialization(CivlTypeChecker civlTypeChecker, AtomicAction inputAction, AtomicAction outputAction,
      AtomicAction invariantAction, Dictionary<AtomicAction, AtomicAction> elim)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.inputAction = inputAction;
      this.outputAction = outputAction;
      this.invariantAction = invariantAction;
      this.elim = elim;

      // TODO: check frame computation
      // We could compute a tighter frame per check. For example, base/conclusion checkers
      // don't have to take the eliminated actions into account.
      var frameVars = new List<AtomicAction> { invariantAction, outputAction, inputAction }
        .Union(elim.Select(kv => kv.Value))
        .SelectMany(a => a.gateUsedGlobalVars.Union(a.modifiedGlobalVars)).Distinct();
      this.frame = new HashSet<Variable>(frameVars);
      this.modifies = frame.Select(Expr.Ident).ToList();

      newPAs = Expr.Ident(civlTypeChecker.LocalVariable("newPAs", civlTypeChecker.pendingAsyncMultisetType));
      if (HasChoice)
      {
        choice = Expr.Ident(invariantAction.impl.OutParams.Last());
      }
      else
      {
        choice = Expr.Ident(civlTypeChecker.LocalVariable("choice", civlTypeChecker.pendingAsyncType));
      }
    }

    public Tuple<Procedure, Implementation> GenerateBaseCaseChecker()
    {
      this.checkName = "base";
      var requires = invariantAction.gate.Select(g => new Requires(false, g.Expr)).ToList();
      
      var subst = GetSubstitution(inputAction, invariantAction);
      List<Cmd> cmds = GetGateAsserts(inputAction, subst).ToList<Cmd>();
      cmds.Add(GetCallCmd(inputAction));
      cmds.Add(GetCheck(GetTransitionRelation(invariantAction)));

      return GetCheckerTuple(requires, new List<Variable>(), cmds);
    }

    public Tuple<Procedure, Implementation> GenerateConclusionChecker()
    {
      this.checkName = "conclusion";
      var subst = GetSubstitution(outputAction, invariantAction);
      var requires = outputAction.gate.Select(g => new Requires(false, Substituter.Apply(subst, g.Expr))).ToList();
      
      List<Cmd> cmds = GetGateAsserts(invariantAction, null).ToList<Cmd>();
      cmds.Add(GetCallCmd(invariantAction));
      cmds.Add(CmdHelper.AssumeCmd(PendingAsyncsEliminatedExpr));
      cmds.Add(GetCheck(Substituter.Apply(subst, GetTransitionRelation(outputAction))));
      if (!outputAction.HasPendingAsyncs)
      {
        cmds.Add(CmdHelper.AssertCmd(
          inputAction.proc.tok,
          NoPendingAsyncs,
          $"IS leaves pending asyncs not summarized by ${outputAction.proc.Name}"));
      }

      return GetCheckerTuple(requires, new List<Variable>(), cmds);
    }

    public Tuple<Procedure, Implementation> GenerateChoiceChecker()
    {
      this.checkName = "choice";
      var requires = invariantAction.gate.Select(g => new Requires(false, g.Expr)).ToList();

      List<Cmd> cmds = new List<Cmd>();
      cmds.Add(GetCallCmd(invariantAction));
      cmds.Add(CmdHelper.AssumeCmd(ExistsElimPendingAsyncExpr));
      cmds.Add(CmdHelper.AssertCmd(
        invariantAction.proc.tok,
        ElimPendingAsyncExpr(choice),
        $"Failed to validate choice in IS of {inputAction.proc.Name}"));

      return GetCheckerTuple(requires, new List<Variable>(), cmds);
    }

    public Tuple<Procedure, Implementation> GenerateStepChecker(AtomicAction pendingAsync, Function pendingAsyncAdd)
    {
      this.checkName = "step";
      var requires = invariantAction.gate.Select(g => new Requires(false, g.Expr)).ToList();
      var locals = new List<Variable>();

      if (!HasChoice)
      {
        locals.Add(choice.Decl);
      }

      List<Cmd> cmds = new List<Cmd>();
      cmds.Add(GetCallCmd(invariantAction));
      cmds.Add(CmdHelper.AssumeCmd(ExprHelper.FunctionCall(pendingAsync.pendingAsyncCtor.membership, choice)));
      cmds.Add(CmdHelper.AssumeCmd(Expr.Gt(Expr.Select(PAs, choice), Expr.Literal(0))));
      cmds.Add(RemoveChoice);

      AtomicAction abs = elim[pendingAsync];
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      List<Expr> inputExprs = new List<Expr>();
      for (int i = 0; i < abs.impl.InParams.Count; i++)
      {
        var pendingAsyncParam = ExprHelper.FunctionCall(pendingAsync.pendingAsyncCtor.selectors[i], choice);
        map[abs.impl.InParams[i]] = pendingAsyncParam;
        inputExprs.Add(pendingAsyncParam);
      }
      var subst = Substituter.SubstitutionFromDictionary(map);
      cmds.AddRange(GetGateAsserts(abs, subst));

      List<IdentifierExpr> outputVars = new List<IdentifierExpr>();
      if (abs.HasPendingAsyncs)
      {
        locals.Add(newPAs.Decl);
        outputVars.Add(newPAs);
      }
      cmds.Add(CmdHelper.CallCmd(abs.proc, inputExprs, outputVars));
      if (abs.HasPendingAsyncs)
      {
        cmds.Add(AddNewPAs(pendingAsyncAdd));
      }

      cmds.Add(GetCheck(GetTransitionRelation(invariantAction)));

      return GetCheckerTuple(requires, locals, cmds, "_" + abs.proc.Name);
    }

    private CallCmd GetCallCmd(AtomicAction callee)
    {
      return CmdHelper.CallCmd(
        callee.proc,
        invariantAction.impl.InParams,
        invariantAction.impl.OutParams.GetRange(0, callee.impl.OutParams.Count)
      );
    }

    private AssertCmd GetCheck(Expr expr)
    {
      expr.Typecheck(new TypecheckingContext(null));
      return CmdHelper.AssertCmd(
        inputAction.proc.tok,
        expr,
        $"IS {checkName} of {inputAction.proc.Name} failed");
    }

    public static IEnumerable<AssertCmd> GetGateAsserts(AtomicAction action, Substitution subst, string msg)
    {
      foreach (var gate in action.gate)
      {
        AssertCmd cmd =
            subst != null
          ? (AssertCmd) Substituter.Apply(subst, gate)
          : new AssertCmd(gate.tok, gate.Expr);
        cmd.ErrorData = msg;
        yield return cmd;
      }
    }

    private IEnumerable<AssertCmd> GetGateAsserts(AtomicAction action, Substitution subst)
    {
      return GetGateAsserts(action, subst,
        $"Gate of {action.proc.Name} fails in IS {checkName} of {inputAction.proc.Name}");
    }

    private Tuple<Procedure, Implementation> GetCheckerTuple(
      List<Requires> requires, List<Variable> locals, List<Cmd> cmds, string suffix = "")
    {
      var proc = DeclHelper.Procedure(
        civlTypeChecker.AddNamePrefix($"IS_{checkName}_{inputAction.proc.Name}{suffix}"),
        invariantAction.impl.InParams,
        invariantAction.impl.OutParams,
        requires,
        modifies,
        new List<Ensures>());
      var impl = DeclHelper.Implementation(
        proc,
        proc.InParams,
        proc.OutParams,
        locals,
        new List<Block> { BlockHelper.Block(checkName, cmds) });
      return Tuple.Create(proc, impl);
    }

    public bool HasChoice => invariantAction.hasChoice;

    private IdentifierExpr PAs => Expr.Ident(HasChoice
      ? invariantAction.impl.OutParams[invariantAction.impl.OutParams.Count - 2]
      : invariantAction.impl.OutParams.Last());

    private Expr NoPendingAsyncs
    {
      get
      {
        var paBound = civlTypeChecker.BoundVariable("pa", civlTypeChecker.pendingAsyncType);
        var pa = Expr.Ident(paBound);
        var expr = Expr.Eq(Expr.Select(PAs, pa), Expr.Literal(0));
        expr.Typecheck(new TypecheckingContext(null));
        return ExprHelper.ForallExpr(new List<Variable> { paBound }, expr);
      }
    }

    private Expr PendingAsyncsEliminatedExpr
    {
      get
      {
        var paBound = civlTypeChecker.BoundVariable("pa", civlTypeChecker.pendingAsyncType);
        var pa = Expr.Ident(paBound);
        var expr = Expr.Imp(
          Expr.Gt(Expr.Select(PAs, pa), Expr.Literal(0)),
          Expr.And(elim.Keys.Select(a => Expr.Not(ExprHelper.FunctionCall(a.pendingAsyncCtor.membership, pa)))));
        expr.Typecheck(new TypecheckingContext(null));
        return ExprHelper.ForallExpr(new List<Variable> { paBound }, expr);
      }
    }

    private Expr ExistsElimPendingAsyncExpr
    {
      get
      {
        var paBound = civlTypeChecker.BoundVariable("pa", civlTypeChecker.pendingAsyncType);
        var pa = Expr.Ident(paBound);
        return ExprHelper.ExistsExpr(new List<Variable> { paBound }, ElimPendingAsyncExpr(pa));
      }
    }

    private Expr ElimPendingAsyncExpr(IdentifierExpr pa)
    {
      return Expr.And(
        Expr.Or(elim.Keys.Select(a => ExprHelper.FunctionCall(a.pendingAsyncCtor.membership, pa))),
        Expr.Gt(Expr.Select(PAs, pa), Expr.Literal(0))
      );
    }

    private AssignCmd RemoveChoice
    {
      get
      {
        var rhs = Expr.Sub(Expr.Select(PAs, choice), Expr.Literal(1));
        return AssignCmd.MapAssign(Token.NoToken, PAs, new List<Expr> { choice }, rhs);
      }
    }

    private AssignCmd AddNewPAs(Function pendingAsyncAdd)
    {
      return AssignCmd.SimpleAssign(Token.NoToken,
        PAs,
        ExprHelper.FunctionCall(pendingAsyncAdd, PAs, newPAs));
    }


    public static Substitution GetSubstitution(AtomicAction from, AtomicAction to)
    {
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      for (int i = 0; i < from.impl.InParams.Count; i++)
      {
        map[from.impl.InParams[i]] = Expr.Ident(to.impl.InParams[i]);
      }
      for (int i = 0; i < Math.Min(from.impl.OutParams.Count, to.impl.OutParams.Count); i++)
      {
        map[from.impl.OutParams[i]] = Expr.Ident(to.impl.OutParams[i]);
      }
      return Substituter.SubstitutionFromDictionary(map);
    }

    private Expr GetTransitionRelation(AtomicAction action)
    {
      var tr = TransitionRelationComputation.Refinement(civlTypeChecker, action, frame);
      if (action == invariantAction && HasChoice)
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
    public static void AddCheckers(CivlTypeChecker civlTypeChecker)
    {
      foreach (var x in civlTypeChecker.inductiveSequentializations)
      {
        AddCheck(civlTypeChecker, x.GenerateBaseCaseChecker());
        AddCheck(civlTypeChecker, x.GenerateConclusionChecker());
        if (x.HasChoice)
        {
          AddCheck(civlTypeChecker, x.GenerateChoiceChecker());
        }
        foreach (var elim in x.elim.Keys)
        {
          AddCheck(civlTypeChecker, x.GenerateStepChecker(elim, civlTypeChecker.pendingAsyncAdd));
        }
      }

      var absChecks = civlTypeChecker.inductiveSequentializations
        .SelectMany(x => x.elim)
        .Where(kv => kv.Key != kv.Value)
        .Distinct();
      
      foreach (var absCheck in absChecks)
      {
        AddCheck(civlTypeChecker, GenerateAbstractionChecker(civlTypeChecker, absCheck.Key, absCheck.Value));
      }
    }

    private static Tuple<Procedure, Implementation> GenerateAbstractionChecker(CivlTypeChecker civlTypeChecker, AtomicAction action, AtomicAction abs)
    {
      var requires = abs.gate.Select(g => new Requires(false, g.Expr)).ToList();
      // TODO: check frame computation
      var frame = new HashSet<Variable>(
        action.modifiedGlobalVars
        .Union(action.gateUsedGlobalVars)
        .Union(abs.modifiedGlobalVars)
        .Union(abs.gateUsedGlobalVars));

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

    private static void AddCheck(CivlTypeChecker civlTypeChecker, Tuple<Procedure, Implementation> t)
    {
      civlTypeChecker.program.AddTopLevelDeclaration(t.Item1);
      civlTypeChecker.program.AddTopLevelDeclaration(t.Item2);
    }
  }
}
