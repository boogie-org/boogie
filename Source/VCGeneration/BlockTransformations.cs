using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using VCGeneration.Prune;

namespace VCGeneration;

public static class BlockTransformations {
  
  public static void Optimize(List<Block> blocks) {
    foreach (var block in blocks)
    {
      // make blocks ending in assume false leaves of the CFG-DAG
      StopControlFlowAtAssumeFalse(block); 
    }

    DeleteBlocksNotLeadingToAssertions(blocks);
    DeleteStraightLineBlocksWithoutCommands(blocks);
    BlockCoalescer.CoalesceInPlace(blocks);
  }

  private static void StopControlFlowAtAssumeFalse(Block block)
  {
    var firstFalseIdx = block.Cmds.FindIndex(IsAssumeFalse);
    if (firstFalseIdx == -1)
    {
      return;
    }

    block.Cmds = block.Cmds.Take(firstFalseIdx + 1).ToList();
    if (block.TransferCmd is not GotoCmd gotoCmd)
    {
      return;
    }

    block.TransferCmd = new ReturnCmd(block.tok);
    foreach (var target in gotoCmd.LabelTargets) {
      target.Predecessors.Remove(block);
    }
  }
  
  private static bool IsAssumeFalse (Cmd c) { return c is AssumeCmd { Expr: LiteralExpr { asBool: false } }; }

  public static void DeleteBlocksNotLeadingToAssertions(List<Block> blocks)
  {
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
          var gtc = new GotoCmd(exit.tok, exit.LabelTargets.Where(l => interestingBlocks.Contains(l)).ToList());
          currentBlock.TransferCmd = gtc;
          interesting = gtc.LabelTargets.Count != 0;
        }
        else
        {
          exit.LabelTargets.ForEach(b => todo.Push(b));
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
    var result = blocks.Where(b => interestingBlocks.Contains(b)).ToList(); // this is not the same as interestingBlocks.ToList() because the resulting lists will have different orders.
    blocks.Clear();
    blocks.AddRange(result);
  }

  private static bool ContainsAssert(Block b)
  {
    return b.Cmds.Exists(IsNonTrivialAssert);
  }
  
  public static bool IsNonTrivialAssert (Cmd c) { return c is AssertCmd { Expr: not LiteralExpr { asBool: true } }; }

  public static void DeleteStraightLineBlocksWithoutCommands(List<Block> blocks) {
    var toVisit = new HashSet<Block>(blocks);
    var removed = new HashSet<Block>();
    while(toVisit.Count > 0) {
      var block = toVisit.First();
      toVisit.Remove(block);
      if (removed.Contains(block)) {
        continue;
      }
      if (block.Cmds.Any()) {
        continue;
      }

      var isBranchingBlock = block.TransferCmd is GotoCmd gotoCmd1 && gotoCmd1.LabelTargets.Count > 1 && 
                             block.Predecessors.Count != 1;
      if (isBranchingBlock) {
        continue;
      }

      removed.Add(block);
      blocks.Remove(block);

      var noPredecessors = !block.Predecessors.Any();
      var noSuccessors = block.TransferCmd is not GotoCmd outGoto2 || !outGoto2.LabelTargets.Any();
      foreach (var predecessor in block.Predecessors) {
        var intoCmd = (GotoCmd)predecessor.TransferCmd;
        intoCmd.RemoveTarget(block);
        if (noSuccessors) {
          toVisit.Add(predecessor);
        }
      }

      if (block.TransferCmd is not GotoCmd outGoto) {
        continue;
      }

      foreach (var outBlock in outGoto.LabelTargets) {
        outBlock.Predecessors.Remove(block);
        if (noPredecessors) {
          toVisit.Add(outBlock);
        }
      }

      foreach (var predecessor in block.Predecessors) {
        var intoCmd = (GotoCmd)predecessor.TransferCmd;
        foreach (var outBlock in outGoto.LabelTargets) {
          if (!intoCmd.LabelTargets.Contains(outBlock)) {
            intoCmd.AddTarget(outBlock);
            outBlock.Predecessors.Add(predecessor);
          }
        }
      }
    }
  }
}