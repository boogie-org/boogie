using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using VCGeneration.Prune;

namespace VCGeneration;

public static class BlockTransformations {
  public static List<Block> Optimize(List<Block> blocks) {
    var copy = blocks; 
    PruneAssumptions(copy);
    OptimizeBlocks(copy);
    return copy;
  }

  public static void OptimizeBlocks(List<Block> blocks) {
    DeleteUselessBlocks(blocks);
    MergeOneToOneBlocks(blocks);
  }

  private static void DeleteUselessBlocks(List<Block> blocks) {
    var stack = new Stack<Block>();
    foreach (var block in blocks) {
      stack.Push(block);
    }
    while(stack.Any()) {
      var block = stack.Pop();
      if (block.Cmds.Any()) {
        continue;
      }

      var isBranchingBlock = block.TransferCmd is GotoCmd gotoCmd1 && gotoCmd1.labelTargets.Count > 1 && 
                             block.Predecessors.Count != 1;
      if (isBranchingBlock) {
        continue;
      }

      blocks.Remove(block);

      foreach (var predecessor in block.Predecessors) {
        var intoCmd = (GotoCmd)predecessor.TransferCmd;
        intoCmd.RemoveTarget(block);
        stack.Push(predecessor);
      }

      if (block.TransferCmd is not GotoCmd outGoto) {
        continue;
      }

      foreach (var outBlock in outGoto.labelTargets) {
        outBlock.Predecessors.Remove(block);
        stack.Push(outBlock);
      }

      foreach (var predecessor in block.Predecessors) {
        var intoCmd = (GotoCmd)predecessor.TransferCmd;
        foreach (var outBlock in outGoto.labelTargets) {
          outBlock.Predecessors.Remove(block);
          if (!outGoto.labelTargets.Contains(outBlock)) {
            intoCmd.AddTarget(outBlock);
            outBlock.Predecessors.Add(predecessor);
          }
        }
      }
    }
  }

  private static void MergeOneToOneBlocks(List<Block> blocks) {
    var stack = new Stack<Block>();
    foreach (var block in blocks) {
      if (!block.Predecessors.Any()) {
        stack.Push(block);
      }
    }
    while (stack.Any()) {
      var current = stack.Pop();
      if (current.TransferCmd is not GotoCmd gotoCmd) {
        continue;
      }

      if (gotoCmd.labelTargets.Count != 1) {
        foreach (var aNext in gotoCmd.labelTargets) {
          stack.Push(aNext);
        }
        continue;
      }

      var next = gotoCmd.labelTargets.Single();
      if (next.Predecessors.Count != 1) {
        stack.Push(next);
        continue;
      }

      blocks.Remove(next);
      current.Cmds.AddRange(next.Cmds);
      gotoCmd.RemoveTarget(next);
      if (next.TransferCmd is GotoCmd nextGotoCmd) {
        gotoCmd.AddTargets(nextGotoCmd.labelTargets);
        foreach (var nextTarget in nextGotoCmd.labelTargets) {
          nextTarget.Predecessors.Remove(next);
          nextTarget.Predecessors.Add(current);
        }
      }
      stack.Push(current);
    }
  }

  public static void PruneAssumptions(List<Block> blocks) {
    var commandsPartOfContradiction = new HashSet<Cmd>();
    var controlFlowGraph = Pruner.GetControlFlowGraph(blocks);
    var asserts = controlFlowGraph.Nodes.OfType<AssertCmd>().ToList();
    foreach (var assert in asserts) {
      if (assert.Expr.Equals(Expr.True)) {
        foreach (var reachable in controlFlowGraph.ComputeReachability(assert, false).OfType<AssumeCmd>()) {
          commandsPartOfContradiction.Add(reachable);
        }
      }
    }

    var liveAnalysis = new LiveVariablesAnalysis(asserts, 
      cmd => controlFlowGraph.Predecessors(cmd),
      cmd => controlFlowGraph.Successors(cmd));
    liveAnalysis.Run();
    
    foreach (var block in blocks) {
      block.Cmds = block.Cmds.Where(cmd => 
        cmd is not AssumeCmd assumeCmd || 
        commandsPartOfContradiction.Contains(assumeCmd) ||
        liveAnalysis.LiveCommands.Contains(assumeCmd)).ToList();
    }
  }
  
  
  public static List<Block> DeleteNoAssertionBlocks(List<Block> blocks)
  {

    blocks.ForEach(StopControlFlowAtAssumeFalse); // make blocks ending in assume false leaves of the CFG-DAG -- this is probably unnecessary, may have been done previously
    var todo = new Stack<Block>();
    var peeked = new HashSet<Block>();
    var interestingBlocks = new HashSet<Block>();
    todo.Push(blocks[0]);
    while(todo.Any())
    {
      /*
       * DFS traversal where each node is handled before and after its children were visited.
       * Pop == true means it's after the children.
       */
      var currentBlock = todo.Peek();
      var pop = peeked.Contains(currentBlock);
      peeked.Add(currentBlock);
      var interesting = false;
      if (currentBlock.TransferCmd is GotoCmd exit) {
        if (pop)
        {
          Contract.Assert(pop);
          var gtc = new GotoCmd(exit.tok, exit.labelTargets.Where(l => interestingBlocks.Contains(l)).ToList());
          currentBlock.TransferCmd = gtc;
          interesting = interesting || gtc.labelTargets.Count != 0;
        }
        else
        {
          exit.labelTargets.ForEach(b => todo.Push(b));
        }
      }
      if (pop)
      {
        interesting = interesting || ContainsAssert(currentBlock);
        if (interesting) {
          interestingBlocks.Add(currentBlock);
        }
        todo.Pop();
      }
    }
    interestingBlocks.Add(blocks[0]); // must not be empty
    return blocks.Where(b => interestingBlocks.Contains(b)).ToList(); // this is not the same as interestingBlocks.ToList() because the resulting lists will have different orders.
  }

  private static bool ContainsAssert(Block b)
  {
    bool IsNonTrivialAssert (Cmd c) { return c is AssertCmd ac && !(ac.Expr is LiteralExpr le && le.asBool); }
    return b.Cmds.Exists(IsNonTrivialAssert);
  }

  private static void StopControlFlowAtAssumeFalse(Block b)
  {
    var firstFalseIdx = b.Cmds.FindIndex(IsAssumeFalse);
    if (firstFalseIdx == -1)
    {
      return;
    }

    b.Cmds = b.Cmds.Take(firstFalseIdx + 1).ToList();
    b.TransferCmd = b.TransferCmd is GotoCmd ? new ReturnCmd(b.tok) : b.TransferCmd;
  }
  
  private static bool IsAssumeFalse (Cmd c) { return c is AssumeCmd { Expr: LiteralExpr { asBool: false } }; }
}

class LiveVariablesAnalysis : DataflowAnalysis<Absy, ImmutableHashSet<Variable>> {
  private readonly Dictionary<PredicateCmd, ISet<Variable>> commandVariables;
  public HashSet<Cmd> LiveCommands { get; } = new();

  public LiveVariablesAnalysis(IReadOnlyList<Absy> roots, 
    Func<Absy, IEnumerable<Absy>> getNext, 
    Func<Absy, IEnumerable<Absy>> getPrevious) : base(roots, getNext, getPrevious) {
    commandVariables = roots.OfType<PredicateCmd>().ToDictionary(cmd => cmd, cmd => {
      var set = new GSet<object>();
      cmd.Expr.ComputeFreeVariables(set);
      return (ISet<Variable>)set.OfType<Variable>().ToHashSet();
    });
  }

  protected override ImmutableHashSet<Variable> Empty => ImmutableHashSet<Variable>.Empty;
  
  protected override ImmutableHashSet<Variable> Merge(ImmutableHashSet<Variable> first, ImmutableHashSet<Variable> second) {
    return first.Union(second);
  }

  protected override bool StateEquals(ImmutableHashSet<Variable> first, ImmutableHashSet<Variable> second) {
    return first.SetEquals(second);
  }

  ISet<Variable> GetVariables(PredicateCmd cmd) {
    return commandVariables.GetOrCreate(cmd, () => {
      var set = new GSet<object>();
      cmd.Expr.ComputeFreeVariables(set);
      return (ISet<Variable>)set.OfType<Variable>().ToHashSet();
    });
  }

  protected override ImmutableHashSet<Variable> Update(Absy node, ImmutableHashSet<Variable> state) {
    if (node is PredicateCmd predicateCmd) {
      var isLive = false;
      if (node is AssertCmd) {
        isLive = true;
      } else if (node is AssumeCmd assumeCmd) {
        /*
         * A path that can not be taken is one whose control flow assumptions together, prove false.
         * By proving false, subsequent assertions are always provable, so the impossible path does not throw errors.
         * Because of this, we may not prune assumptions resulting from control flow paths.
         */
        var isControlFlowCommand = QKeyValue.FindBoolAttribute(assumeCmd.Attributes, "partition");
        if (isControlFlowCommand || GetVariables(assumeCmd).Intersect(state).Any()) {
          isLive = true;
        }
      }
      if (isLive) {
        LiveCommands.Add(predicateCmd);
        return GetVariables(predicateCmd).Aggregate(state, (set, variable) => set.Add(variable));
      }
    }
    return state;
  }
}