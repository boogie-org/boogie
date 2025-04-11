using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class MoverCheck
  {
    private class MoverCheckContext
    {
      public int layer;
      public IEnumerable<Expr> extraAssumptions;
    }

    CivlTypeChecker civlTypeChecker;
    List<Declaration> decls;

    HashSet<Tuple<Action, Action>> commutativityCheckerCache;
    HashSet<Tuple<Action, Action>> gatePreservationCheckerCache;
    HashSet<Tuple<Action, Action>> failurePreservationCheckerCache;
    HashSet<Action> nonblockingCheckerCache;

    Dictionary<int, HashSet<Tuple<Action, Action>>> perLayerCommutativityCheckerCache;
    Dictionary<int, HashSet<Tuple<Action, Action>>> perLayerGatePreservationCheckerCache;
    Dictionary<int, HashSet<Tuple<Action, Action>>> perLayerFailurePreservationCheckerCache;
    Dictionary<int, HashSet<Action>> perLayerNonblockingCheckerCache;

    private MoverCheck(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.decls = decls;
      this.commutativityCheckerCache = new HashSet<Tuple<Action, Action>>();
      this.gatePreservationCheckerCache = new HashSet<Tuple<Action, Action>>();
      this.failurePreservationCheckerCache = new HashSet<Tuple<Action, Action>>();
      this.nonblockingCheckerCache = new HashSet<Action>();
      this.perLayerCommutativityCheckerCache = new Dictionary<int, HashSet<Tuple<Action, Action>>>();
      this.perLayerGatePreservationCheckerCache = new Dictionary<int, HashSet<Tuple<Action, Action>>>();
      this.perLayerFailurePreservationCheckerCache = new Dictionary<int, HashSet<Tuple<Action, Action>>>();
      this.perLayerNonblockingCheckerCache = new Dictionary<int, HashSet<Action>>();
    }

    private ConcurrencyOptions Options => civlTypeChecker.Options;

    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      MoverCheck moverChecking = new MoverCheck(civlTypeChecker, decls);

      var regularMoverChecks =
        from first in civlTypeChecker.MoverActions
        from second in civlTypeChecker.MoverActions
        where first.LayerRange.OverlapsWith(second.LayerRange)
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

      foreach (var action in civlTypeChecker.MoverActions.Where(a => a.IsLeftMover))
      {
        moverChecking.CreateNonblockingChecker(action);
      }

      /*
       * All the global caches of various mover checks have been populated now.
       * The global cache is checked before adding per-layer mover checks for sequentializations.
       * Therefore, it is important that the sequentialization mover checks are generated last.
       * Each sequentialization mover check is constrained by extra assumptions.
       * Therefore, presence in global cache of the corresponding unconstrained check
       * obviates the need to generate it.
       */

      foreach (var sequentialization in civlTypeChecker.Sequentializations)
      {
        foreach (var leftMover in sequentialization.EliminatedActions)
        {
          foreach (var action in civlTypeChecker.MoverActions.Where(x => x.LayerRange.Contains(sequentialization.Layer)))
          {
            var moverCheckContext1 = new MoverCheckContext
            {
              layer = sequentialization.Layer,
              extraAssumptions = sequentialization.GenerateLeftMoverCheckAssumptions(action, action.FirstImpl.InParams, leftMover, leftMover.SecondImpl.InParams)
            };
            var moverCheckContext2 = new MoverCheckContext
            {
              layer = sequentialization.Layer,
              extraAssumptions = sequentialization.GenerateLeftMoverCheckAssumptions(action, action.SecondImpl.InParams, leftMover, leftMover.FirstImpl.InParams)
            };
            moverChecking.CreateCommutativityChecker(action, leftMover, moverCheckContext1);
            moverChecking.CreateGatePreservationChecker(leftMover, action, moverCheckContext2);
            moverChecking.CreateFailurePreservationChecker(action, leftMover, moverCheckContext1);
          }
          if (!leftMover.IsLeftMover)
          {
            var subst = Substituter.SubstitutionFromDictionary(
              leftMover.ActionDecl.InParams.Zip(leftMover.Impl.InParams.Select(x => (Expr)Expr.Ident(x))).ToDictionary(x => x.Item1, x => x.Item2));
            var moverCheckContext = new MoverCheckContext
            {
              layer = sequentialization.Layer,
              extraAssumptions = sequentialization.Preconditions(leftMover, subst).Select(assertCmd => assertCmd.Expr)
            };
            moverChecking.CreateNonblockingChecker(leftMover, moverCheckContext);
          }
        }
      }
    }

    private IEnumerable<Requires> DisjointnessAndWellFormedRequires(IEnumerable<Variable> paramVars, HashSet<Variable> frame)
    {
      var availableVars = paramVars.Union(frame);
      return civlTypeChecker.linearTypeChecker.DisjointnessExprForEachDomain(availableVars)
        .Union(civlTypeChecker.linearTypeChecker.MapWellFormedExpressions(availableVars))
        .Select(expr => RequiresHelper.Requires(expr));
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

    private void CreateRightMoverCheckers(Action rightMover, Action action)
    {
      CreateCommutativityChecker(rightMover, action);
      CreateGatePreservationChecker(action, rightMover);
    }

    private void CreateLeftMoverCheckers(Action action, Action leftMover)
    {
      CreateCommutativityChecker(action, leftMover);
      CreateGatePreservationChecker(leftMover, action);
      CreateFailurePreservationChecker(action, leftMover);
    }

    private CallCmd ActionCallCmd(Action action, DeclWithFormals paramProvider)
    {
      return CmdHelper.CallCmd(action.Impl.Proc, paramProvider.InParams, paramProvider.OutParams);
    }

    private void CreateCommutativityChecker(Action first, Action second) => CreateCommutativityChecker(first, second, null);

    private void CreateCommutativityChecker(Action first, Action second, MoverCheckContext moverCheckContext)
    {
      if (first == second && first.FirstImpl.InParams.Count == 0 && first.FirstImpl.OutParams.Count == 0)
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

      if (moverCheckContext != null)
      {
        var layer = moverCheckContext.layer;
        if (!perLayerCommutativityCheckerCache.ContainsKey(layer))
        {
          perLayerCommutativityCheckerCache[layer] = new HashSet<Tuple<Action, Action>>();
        }
        if (!perLayerCommutativityCheckerCache[layer].Add(Tuple.Create(first, second)))
        {
          return;
        }
      }

      string checkerName = $"CommutativityChecker_{first.Name}_{second.Name}";

      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(first.UsedGlobalVarsInGate);
      frame.UnionWith(first.UsedGlobalVarsInAction);
      frame.UnionWith(second.UsedGlobalVarsInGate);
      frame.UnionWith(second.UsedGlobalVarsInAction);

      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      List<Requires> requires =
        DisjointnessAndWellFormedRequires(
          first.FirstImpl.InParams.Union(second.SecondImpl.InParams)
            .Where(v => LinearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame).ToList();
      requires.AddRange(first.FirstGate.Union(second.SecondGate).Select(assertCmd => RequiresHelper.Requires(assertCmd.Expr, assertCmd.Attributes)));
      if (moverCheckContext != null)
      {
        checkerName = $"CommutativityChecker_{first.Name}_{second.Name}_{moverCheckContext.layer}";
        requires.AddRange(moverCheckContext.extraAssumptions.Select(expr => RequiresHelper.Requires(expr)));
      }

      var transitionRelation = TransitionRelationComputation.Commutativity(civlTypeChecker, second, first, frame);

      var secondInParamsFiltered =
        second.SecondImpl.InParams.Where(v => LinearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_IN);
      IEnumerable<Expr> linearityAssumes = linearTypeChecker.DisjointnessExprForEachDomain(first.FirstImpl.OutParams.Union(secondInParamsFiltered)
        .Union(frame)).Union(linearTypeChecker.DisjointnessExprForEachDomain(first.FirstImpl.OutParams.Union(second.SecondImpl.OutParams)
          .Union(frame)));
      var commutativityCheck = CmdHelper.AssertCmd(
        first.tok,
        Expr.Imp(Expr.And(linearityAssumes), transitionRelation),
        $"Commutativity check between {first.Name} @ {Location(first.ActionDecl.tok)} and {second.Name} @ {Location(second.ActionDecl.tok)} failed");

      List<Cmd> cmds = new List<Cmd>
      {
        ActionCallCmd(first, first.FirstImpl),
        ActionCallCmd(second, second.SecondImpl),
        commutativityCheck
      };

      List<Variable> inputs = first.FirstImpl.InParams.Union(second.SecondImpl.InParams).ToList();
      List<Variable> outputs = first.FirstImpl.OutParams.Union(second.SecondImpl.OutParams).ToList();

      AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, cmds);
    }

    private void CreateGatePreservationChecker(Action first, Action second) => CreateGatePreservationChecker(first, second, null);

    private void CreateGatePreservationChecker(Action first, Action second, MoverCheckContext moverCheckContext)
    {
      if (!first.UsedGlobalVarsInGate.Intersect(second.ModifiedGlobalVars).Any())
      {
        return;
      }

      if (!gatePreservationCheckerCache.Add(Tuple.Create(first, second)))
      {
        return;
      }

      if (moverCheckContext != null)
      {
        var layer = moverCheckContext.layer;
        if (!perLayerGatePreservationCheckerCache.ContainsKey(layer))
        {
          perLayerGatePreservationCheckerCache[layer] = new HashSet<Tuple<Action, Action>>();
        }
        if (!perLayerGatePreservationCheckerCache[layer].Add(Tuple.Create(first, second)))
        {
          return;
        }
      }

      string checkerName = $"GatePreservationChecker_{first.Name}_{second.Name}";

      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(first.UsedGlobalVarsInGate);
      frame.UnionWith(second.UsedGlobalVarsInGate);
      frame.UnionWith(second.UsedGlobalVarsInAction);

      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      List<Requires> requires = 
        DisjointnessAndWellFormedRequires(
          first.FirstImpl.InParams.Union(second.SecondImpl.InParams)
            .Where(v => LinearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame).ToList();
      requires.AddRange(first.FirstGate.Union(second.SecondGate).Select(assertCmd => RequiresHelper.Requires(assertCmd.Expr, assertCmd.Attributes)));
      if (moverCheckContext != null)
      {
        checkerName = $"GatePreservationChecker_{first.Name}_{second.Name}_{moverCheckContext.layer}";
        requires.AddRange(moverCheckContext.extraAssumptions.Select(expr => RequiresHelper.Requires(expr)));
      }

      List<Variable> inputs = first.FirstImpl.InParams.Union(second.SecondImpl.InParams).ToList();
      List<Variable> outputs = first.FirstImpl.OutParams.Union(second.SecondImpl.OutParams).ToList();

      List<Cmd> cmds = new List<Cmd> { ActionCallCmd(second, second.SecondImpl) };

      IEnumerable<Expr> linearityAssumes =
        linearTypeChecker.DisjointnessExprForEachDomain(first.FirstImpl.InParams.Union(second.SecondImpl.OutParams)
          .Union(frame));
      cmds.AddRange(first.FirstGate.Select(assertCmd =>
        CmdHelper.AssertCmd(assertCmd.tok, Expr.Imp(Expr.And(linearityAssumes), assertCmd.Expr),
            $"Gate of {first.Name} @ {Location(first.ActionDecl.tok)} not preserved by {second.Name} @ {Location(second.ActionDecl.tok)}")));

      AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, cmds);
    }

    private void CreateFailurePreservationChecker(Action first, Action second) => CreateFailurePreservationChecker(first, second, null);

    private void CreateFailurePreservationChecker(Action first, Action second, MoverCheckContext moverCheckContext)
    {
      if (!first.UsedGlobalVarsInGate.Intersect(second.ModifiedGlobalVars).Any())
      {
        return;
      }

      if (!failurePreservationCheckerCache.Add(Tuple.Create(first, second)))
      {
        return;
      }

      if (moverCheckContext != null)
      {
        var layer = moverCheckContext.layer;
        if (!perLayerFailurePreservationCheckerCache.ContainsKey(layer))
        {
          perLayerFailurePreservationCheckerCache[layer] = new HashSet<Tuple<Action, Action>>();
        }
        if (!perLayerFailurePreservationCheckerCache[layer].Add(Tuple.Create(first, second)))
        {
          return;
        }
      }

      string checkerName = $"FailurePreservationChecker_{first.Name}_{second.Name}";

      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(first.UsedGlobalVarsInGate);
      frame.UnionWith(second.UsedGlobalVarsInGate);
      frame.UnionWith(second.UsedGlobalVarsInAction);

      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      List<Requires> requires = 
        DisjointnessAndWellFormedRequires(
          first.FirstImpl.InParams.Union(second.SecondImpl.InParams).Where(v => LinearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame).ToList();
      var wpreAssertCmds = Wlp.HoistAsserts(second.SecondImpl, first.FirstGate, Options);
      requires.AddRange(wpreAssertCmds.Select(assertCmd => RequiresHelper.Requires(assertCmd.Expr, assertCmd.Attributes)));
      requires.AddRange(second.SecondGate.Select(assertCmd => RequiresHelper.Requires(assertCmd.Expr, assertCmd.Attributes)));
      
      if (moverCheckContext != null)
      {
        checkerName = $"FailurePreservationChecker_{first.Name}_{second.Name}_{moverCheckContext.layer}";
        requires.AddRange(moverCheckContext.extraAssumptions.Select(expr => RequiresHelper.Requires(expr)));
      }

      var cmds = new List<Cmd>();
      IEnumerable<Expr> linearityAssumes =
        linearTypeChecker.DisjointnessExprForEachDomain(first.FirstImpl.InParams.Union(second.SecondImpl.OutParams).Union(frame));
      cmds.AddRange(linearityAssumes.Select(expr => new AssumeCmd(Token.NoToken, expr)));

      List<Variable> inputs = first.FirstImpl.InParams.Union(second.SecondImpl.InParams).ToList();
      List<Variable> outputs = first.FirstImpl.OutParams.Union(second.SecondImpl.OutParams).ToList();
      cmds.AddRange(first.FirstGate.Select(assertCmd =>
          CmdHelper.AssertCmd(assertCmd.tok, assertCmd.Expr,
            $"Gate failure of {first.Name} @ {Location(first.ActionDecl.tok)} not preserved by {second.Name} @ {Location(second.ActionDecl.tok)}")
      ));

      AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, cmds);
    }

    private void CreateNonblockingChecker(Action action) => CreateNonblockingChecker(action, null);

    private void CreateNonblockingChecker(Action action, MoverCheckContext moverCheckContext)
    {
      if (!action.HasAssumeCmd)
      {
        return;
      }

      if (!nonblockingCheckerCache.Add(action))
      {
        return;
      }

      if (moverCheckContext != null)
      {
        var layer = moverCheckContext.layer;
        if (!perLayerNonblockingCheckerCache.ContainsKey(layer))
        {
          perLayerNonblockingCheckerCache[layer] = new HashSet<Action>();
        }
        if (!perLayerNonblockingCheckerCache[layer].Add(action))
        {
          return;
        }
      }

      string checkerName = $"NonblockingChecker_{action.Name}";

      Implementation impl = action.Impl;
      HashSet<Variable> frame = new HashSet<Variable>();
      frame.UnionWith(action.UsedGlobalVarsInGate);
      frame.UnionWith(action.UsedGlobalVarsInAction);

      List<Requires> requires =
        DisjointnessAndWellFormedRequires(impl.InParams.Where(v => LinearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT),
          frame).ToList();
      requires.AddRange(action.Gate.Select(assertCmd => RequiresHelper.Requires(assertCmd.Expr, assertCmd.Attributes)));
      if (moverCheckContext != null)
      {
        checkerName = $"NonblockingChecker_{action.Name}_{moverCheckContext.layer}";
        requires.AddRange(moverCheckContext.extraAssumptions.Select(expr => RequiresHelper.Requires(expr)));
      }

      AssertCmd nonblockingCheck = CmdHelper.AssertCmd(
        action.tok,
        TransitionRelationComputation.Nonblocking(civlTypeChecker, action, frame),
        $"Nonblocking check for {action.Name} failed");

      AddChecker(checkerName, new List<Variable>(impl.InParams), new List<Variable>(impl.OutParams),
        new List<Variable>(), requires, new List<Cmd> { nonblockingCheck });
    }

    private static string Location(IToken tok) => string.Format("{0}({1},{2})", tok.filename, tok.line, tok.col);
  }
}