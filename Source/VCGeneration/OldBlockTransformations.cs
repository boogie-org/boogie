using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace VCGeneration;

class OldBlockTransformations {
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

  public static void StopControlFlowAtAssumeFalse(Block block)
  {
    var firstFalseIdx = block.Cmds.FindIndex(IsAssumeFalse);
    if (firstFalseIdx == -1)
    {
      return;
    }

    block.Cmds = block.Cmds.Take(firstFalseIdx + 1).ToList();
    if (block.TransferCmd is GotoCmd gotoCmd) {
      block.TransferCmd = new ReturnCmd(block.tok);
      foreach (var target in gotoCmd.labelTargets) {
        target.Predecessors.Remove(block);
      }
    }
  }
  
  private static bool IsAssumeFalse (Cmd c) { return c is AssumeCmd { Expr: LiteralExpr { asBool: false } }; }
}