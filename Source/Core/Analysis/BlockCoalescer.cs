#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class BlockCoalescer : ReadOnlyVisitor
{
  public static void CoalesceBlocks(Program program)
  {
    var blockCoalescer = new BlockCoalescer();
    blockCoalescer.Visit(program);
  }

  private static HashSet<Block> ComputeMultiPredecessorBlocks(Block rootBlock)
  {
    Contract.Ensures(cce.NonNullElements(Contract.Result<HashSet<Block>>()));
    var visitedBlocks = new HashSet<Block /*!*/>();
    var result = new HashSet<Block>();
    var dfsStack = new Stack<Block>();
    dfsStack.Push(rootBlock);
    while (dfsStack.Count > 0)
    {
      var /*!*/ block = dfsStack.Pop();
      Contract.Assert(block != null);
      if (!visitedBlocks.Add(block))
      {
        result.Add(block);
        continue;
      }

      if (block.TransferCmd == null)
      {
        continue;
      }

      if (block.TransferCmd is ReturnCmd)
      {
        continue;
      }

      Contract.Assert(block.TransferCmd is GotoCmd);
      var gotoCmd = (GotoCmd) block.TransferCmd;
      if (gotoCmd.labelTargets == null)
      {
        continue;
      }

      foreach (var /*!*/ succ in gotoCmd.labelTargets)
      {
        Contract.Assert(succ != null);
        dfsStack.Push(succ);
      }
    }

    return result;
  }

  public override Implementation VisitImplementation(Implementation impl)
  {
    var newBlocks = CoalesceFromRootBlock(impl.Blocks);
    impl.Blocks = newBlocks;
    foreach (var block in impl.Blocks)
    {
      if (block.TransferCmd is ReturnCmd)
      {
        continue;
      }

      var gotoCmd = (GotoCmd)block.TransferCmd;
      gotoCmd.labelNames = new List<string>();
      foreach (var successor in gotoCmd.labelTargets)
      {
        gotoCmd.labelNames.Add(successor.Label);
      }
    }
    return impl;
  }

  public static List<Block> CoalesceFromRootBlock(List<Block> blocks)
  {
    var multiPredecessorBlocks = ComputeMultiPredecessorBlocks(blocks[0]);
    Contract.Assert(cce.NonNullElements(multiPredecessorBlocks));
    var visitedBlocks = new HashSet<Block>();
    var removedBlocks = new HashSet<Block>();
    var toVisit = new Stack<Block>();
    toVisit.Push(blocks[0]);
    while (toVisit.Count > 0)
    {
      var block = toVisit.Pop();
      Contract.Assert(block != null);
      if (!visitedBlocks.Add(block))
      {
        continue;
      }

      if (block.TransferCmd == null)
      {
        continue;
      }

      if (block.TransferCmd is ReturnCmd)
      {
        continue;
      }

      Contract.Assert(block.TransferCmd is GotoCmd);
      var gotoCmd = (GotoCmd) block.TransferCmd;
      if (gotoCmd.labelTargets == null)
      {
        continue;
      }

      if (gotoCmd.labelTargets.Count != 1)
      {
        foreach (var aSuccessor in gotoCmd.labelTargets)
        {
          Contract.Assert(aSuccessor != null);
          toVisit.Push(aSuccessor);
        }
        continue;
      }

      var successor = cce.NonNull(gotoCmd.labelTargets[0]);
      if (multiPredecessorBlocks.Contains(successor))
      {
        toVisit.Push(successor);
        continue;
      }

      block.Cmds.AddRange(successor.Cmds);
      block.TransferCmd = successor.TransferCmd;
      if (!block.tok.IsValid && successor.tok.IsValid)
      {
        block.tok = successor.tok;
        block.Label = successor.Label;
      }

      removedBlocks.Add(successor);
      toVisit.Push(block);
      visitedBlocks.Remove(block);
    }

    var newBlocks = new List<Block>();
    foreach (var block in blocks)
    {
      Contract.Assert(block != null);
      if (visitedBlocks.Contains(block) && !removedBlocks.Contains(block))
      {
        newBlocks.Add(block);
      }
    }
    return newBlocks;
  }
}