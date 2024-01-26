using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace VCGeneration;

public static class BlockTransformations
{
    public static List<Block> PostProcess(List<Block> blocks)
    {
      void DeleteFalseGotos (Block b)
      {
        var firstFalseIdx = b.Cmds.FindIndex(IsAssumeFalse);
        if (firstFalseIdx != -1)
        {
          b.Cmds = b.Cmds.Take(firstFalseIdx + 1).ToList();
          b.TransferCmd = (b.TransferCmd is GotoCmd) ? new ReturnCmd(b.tok) : b.TransferCmd;
        }

        return;

        bool IsAssumeFalse (Cmd c) { return c is AssumeCmd ac && ac.Expr is LiteralExpr le && !le.asBool; }
      }

      bool ContainsAssert(Block b)
      {
        return b.Cmds.Exists(IsNonTrivialAssert);
        bool IsNonTrivialAssert (Cmd c) { return c is AssertCmd ac && !(ac.Expr is LiteralExpr le && le.asBool); }
      }

      blocks.ForEach(DeleteFalseGotos); // make blocks ending in assume false leaves of the CFG-DAG -- this is probably unnecessary, may have been done previously
      var todo = new Stack<Block>();
      var peeked = new HashSet<Block>();
      var interestingBlocks = new HashSet<Block>();
      todo.Push(blocks[0]);
      while(todo.Any())
      {
        var currentBlock = todo.Peek();
        var pop = peeked.Contains(currentBlock);
        peeked.Add(currentBlock);
        var interesting = false;
        var exit = currentBlock.TransferCmd as GotoCmd;
        if (exit != null && !pop) {
          exit.labelTargets.ForEach(b => todo.Push(b));
        } else if (exit != null) {
          Contract.Assert(pop);
          var gtc = new GotoCmd(exit.tok, exit.labelTargets.Where(l => interestingBlocks.Contains(l)).ToList());
          currentBlock.TransferCmd = gtc;
          interesting = interesting || gtc.labelTargets.Count() != 0;
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
}