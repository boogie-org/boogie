using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class MoverCheck
  {
    CivlTypeChecker civlTypeChecker;
    List<Declaration> decls;

    HashSet<Tuple<AtomicAction, AtomicAction>> commutativityCheckerCache;
    HashSet<Tuple<AtomicAction, AtomicAction>> gatePreservationCheckerCache;
    HashSet<Tuple<AtomicAction, AtomicAction>> failurePreservationCheckerCache;

    private MoverCheck(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.decls = decls;
      this.commutativityCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
      this.gatePreservationCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
      this.failurePreservationCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
    }

    private ConcurrencyOptions Options => civlTypeChecker.Options;

    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      MoverCheck moverChecking = new MoverCheck(civlTypeChecker, decls);

      // TODO: make enumeration of mover checks more efficient / elegant

      var regularMoverChecks =
        from first in civlTypeChecker.procToAtomicAction.Values
        from second in civlTypeChecker.procToAtomicAction.Values
        where first.layerRange.OverlapsWith(second.layerRange)
        where first.IsRightMover || second.IsLeftMover
        select new {first, second};

      foreach (var moverCheck in regularMoverChecks)
      {
        if (moverCheck.first.IsRightMover)
        {
          moverChecking.CreateRightMoverCheckers(moverCheck.first, moverCheck.second);
        }

        if (moverCheck.second.IsLeftMover)
        {
          moverChecking.CreateLeftMoverCheckers(moverCheck.first, moverCheck.second);
        }
      }

      var inductiveSequentializationMoverChecks =
        from IS in civlTypeChecker.inductiveSequentializations
        from leftMover in IS.elim.Values
        from action in civlTypeChecker.procToAtomicAction.Values
        where action.layerRange.Contains(IS.inputAction.layerRange.upperLayerNum)
        select new {action, leftMover};

      foreach (var moverCheck in inductiveSequentializationMoverChecks)
      {
        moverChecking.CreateLeftMoverCheckers(moverCheck.action, moverCheck.leftMover);
      }

      // Here we include IS abstractions
      foreach (var atomicAction in civlTypeChecker.AllAtomicActions.Where(a => a.IsLeftMover))
      {
        moverChecking.CreateCooperationChecker(atomicAction);
      }

      // IS abstractions are marked left movers, so here we select regular atomic actions
      // that are not marked left mover but used as abstraction in IS.
      foreach (var atomicAction in civlTypeChecker.inductiveSequentializations.SelectMany(IS => IS.elim.Values)
        .Where(a => !a.IsLeftMover).Distinct())
      {
        moverChecking.CreateCooperationChecker(atomicAction);
      }

      foreach (var introductionAction in civlTypeChecker.procToIntroductionAction.Values)
      {
        moverChecking.CreateCooperationChecker(introductionAction);
      }
    }

    private IEnumerable<Requires> DisjointnessAndWellFormedRequires(IEnumerable<Variable> paramVars, HashSet<Variable> frame)
    {
      var availableVars = paramVars.Union(frame);
      return civlTypeChecker.linearTypeChecker.DisjointnessExprForEachDomain(availableVars)
        .Union(civlTypeChecker.linearTypeChecker.LmapWellFormedExpressions(availableVars))
        .Select(expr => new Requires(false, expr));
    }

    private void AddChecker(string checkerName, List<Variable> inputs, List<Variable> outputs, List<Variable> locals,
      List<Requires> requires, List<Cmd> cmds)
    {
      checkerName = civlTypeChecker.AddNamePrefix(checkerName);
      var blocks = new List<Block> { BlockHelper.Block("init", cmds) };
      Procedure proc = DeclHelper.Procedure(checkerName, inputs, outputs, requires,
        civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList(), new List<Ensures>());
      Implementation impl = DeclHelper.Implementation(proc, inputs, outputs, locals, blocks);
      this.decls.Add(impl);
      this.decls.Add(proc);
    }

    private void CreateRightMoverCheckers(AtomicAction rightMover, AtomicAction action)
    {
      CreateCommutativityChecker(rightMover, action);
      CreateGatePreservationChecker(action, rightMover);
    }

    private void CreateLeftMoverCheckers(AtomicAction action, AtomicAction leftMover)
    {
      CreateCommutativityChecker(action, leftMover);
      CreateGatePreservationChecker(leftMover, action);
      CreateFailurePreservationChecker(action, leftMover);
    }

    private CallCmd ActionCallCmd(AtomicAction action, DeclWithFormals paramProvider)
    {
      return CmdHelper.CallCmd(action.proc, paramProvider.InParams, paramProvider.OutParams);
    }

    private void CreateCommutativityChecker(AtomicAction first, AtomicAction second)
    {
      if (first == second && first.firstImpl.InParams.Count == 0 && first.firstImpl.OutParams.Count == 0)
      {
        return;
      }

      if (first.TriviallyCommutesWith(second))
      {
        return;
      }

      if (!commutativityCheckerCache.Add(Tuple.Create(first, second)))
      {
        return;
      }

      string checkerName = $"CommutativityChecker_{first.proc.Name}_{second.proc.Name}";

      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(first.gateUsedGlobalVars);
      frame.UnionWith(first.actionUsedGlobalVars);
      frame.UnionWith(second.gateUsedGlobalVars);
      frame.UnionWith(second.actionUsedGlobalVars);

      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      List<Requires> requires =
        DisjointnessAndWellFormedRequires(
          first.firstImpl.InParams.Union(second.secondImpl.InParams)
            .Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame).ToList();
      foreach (AssertCmd assertCmd in Enumerable.Union(first.firstGate, second.secondGate))
      {
        requires.Add(new Requires(false, assertCmd.Expr));
      }

      var transitionRelation = TransitionRelationComputation.Commutativity(civlTypeChecker, second, first, frame);

      var secondInParamsFiltered =
        second.secondImpl.InParams.Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.LINEAR_IN);
      IEnumerable<Expr> linearityAssumes = Enumerable.Union(
        linearTypeChecker.DisjointnessExprForEachDomain(first.firstImpl.OutParams.Union(secondInParamsFiltered)
          .Union(frame)),
        linearTypeChecker.DisjointnessExprForEachDomain(first.firstImpl.OutParams.Union(second.secondImpl.OutParams)
          .Union(frame)));
      // TODO: add further disjointness expressions?
      AssertCmd commutativityCheck = CmdHelper.AssertCmd(
        first.proc.tok,
        Expr.Imp(Expr.And(linearityAssumes), transitionRelation),
        $"Commutativity check between {first.proc.Name} and {second.proc.Name} failed");

      List<Cmd> cmds = new List<Cmd>
      {
        ActionCallCmd(first, first.firstImpl),
        ActionCallCmd(second, second.secondImpl)
      };
      cmds.Add(commutativityCheck);

      List<Variable> inputs = Enumerable.Union(first.firstImpl.InParams, second.secondImpl.InParams).ToList();
      List<Variable> outputs = Enumerable.Union(first.firstImpl.OutParams, second.secondImpl.OutParams).ToList();

      AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, cmds);
    }

    private void CreateGatePreservationChecker(AtomicAction first, AtomicAction second)
    {
      if (!first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Any())
      {
        return;
      }

      if (!gatePreservationCheckerCache.Add(Tuple.Create(first, second)))
      {
        return;
      }

      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(first.gateUsedGlobalVars);
      frame.UnionWith(second.gateUsedGlobalVars);
      frame.UnionWith(second.actionUsedGlobalVars);

      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      List<Requires> requires = 
        DisjointnessAndWellFormedRequires(
          first.firstImpl.InParams.Union(second.secondImpl.InParams)
            .Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame).ToList();
      foreach (AssertCmd assertCmd in first.firstGate.Union(second.secondGate))
      {
        requires.Add(new Requires(false, assertCmd.Expr));
      }

      string checkerName = $"GatePreservationChecker_{first.proc.Name}_{second.proc.Name}";

      List<Variable> inputs = Enumerable.Union(first.firstImpl.InParams, second.secondImpl.InParams).ToList();
      List<Variable> outputs = Enumerable.Union(first.firstImpl.OutParams, second.secondImpl.OutParams).ToList();

      List<Cmd> cmds = new List<Cmd> { ActionCallCmd(second, second.secondImpl) };

      IEnumerable<Expr> linearityAssumes =
        linearTypeChecker.DisjointnessExprForEachDomain(first.firstImpl.InParams.Union(second.secondImpl.OutParams)
          .Union(frame));
      foreach (AssertCmd assertCmd in first.firstGate)
      {
        cmds.Add(
          CmdHelper.AssertCmd(
            assertCmd.tok,
            Expr.Imp(Expr.And(linearityAssumes), assertCmd.Expr),
            $"Gate of {first.proc.Name} not preserved by {second.proc.Name}"
          )
        );
      }

      AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, cmds);
    }

    private void CreateFailurePreservationChecker(AtomicAction first, AtomicAction second)
    {
      if (!first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Any())
      {
        return;
      }

      if (!failurePreservationCheckerCache.Add(Tuple.Create(first, second)))
      {
        return;
      }

      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(first.gateUsedGlobalVars);
      frame.UnionWith(second.gateUsedGlobalVars);
      frame.UnionWith(second.actionUsedGlobalVars);

      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      List<Requires> requires = 
        DisjointnessAndWellFormedRequires(
          first.firstImpl.InParams.Union(second.secondImpl.InParams)
            .Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame).ToList();
      Expr firstNegatedGate = Expr.Not(Expr.And(first.firstGate.Select(a => a.Expr)));
      firstNegatedGate.Type = Type.Bool; // necessary?
      requires.Add(new Requires(false, firstNegatedGate));
      foreach (AssertCmd assertCmd in second.secondGate)
      {
        requires.Add(new Requires(false, assertCmd.Expr));
      }

      IEnumerable<Expr> linearityAssumes =
        linearTypeChecker.DisjointnessExprForEachDomain(first.firstImpl.InParams.Union(second.secondImpl.OutParams)
          .Union(frame));
      AssertCmd gateFailureCheck = CmdHelper.AssertCmd(
        first.proc.tok,
        Expr.Imp(Expr.And(linearityAssumes), firstNegatedGate),
        $"Gate failure of {first.proc.Name} not preserved by {second.proc.Name}");

      string checkerName = $"FailurePreservationChecker_{first.proc.Name}_{second.proc.Name}";

      List<Variable> inputs = Enumerable.Union(first.firstImpl.InParams, second.secondImpl.InParams).ToList();
      List<Variable> outputs = Enumerable.Union(first.firstImpl.OutParams, second.secondImpl.OutParams).ToList();
      var cmds = new List<Cmd>
      {
        ActionCallCmd(second, second.secondImpl),
        gateFailureCheck
      };

      AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, cmds);
    }

    private void CreateCooperationChecker(Action action)
    {
      if (!action.HasAssumeCmd)
      {
        return;
      }

      string checkerName = $"CooperationChecker_{action.proc.Name}";

      Implementation impl = action.impl;
      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(action.gateUsedGlobalVars);
      frame.UnionWith(action.actionUsedGlobalVars);

      List<Requires> requires =
        DisjointnessAndWellFormedRequires(impl.InParams.Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.LINEAR_OUT),
          frame).ToList();
      foreach (AssertCmd assertCmd in action.gate)
      {
        requires.Add(new Requires(false, assertCmd.Expr));
      }

      AssertCmd cooperationCheck = CmdHelper.AssertCmd(
        action.proc.tok,
        TransitionRelationComputation.Cooperation(civlTypeChecker, action, frame),
        $"Cooperation check for {action.proc.Name} failed");

      AddChecker(checkerName, new List<Variable>(impl.InParams), new List<Variable>(),
        new List<Variable>(), requires, new List<Cmd> { cooperationCheck });
    }
  }
}