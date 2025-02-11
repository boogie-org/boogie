#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

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
    Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Block>>()));
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
      if (gotoCmd.LabelTargets == null)
      {
        continue;
      }

      foreach (var /*!*/ succ in gotoCmd.LabelTargets)
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
      gotoCmd.LabelNames = new List<string>();
      foreach (var successor in gotoCmd.LabelTargets)
      {
        gotoCmd.LabelNames.Add(successor.Label);
      }
    }
    return impl;
  }

  public static void CoalesceInPlace(IList<Block> blocks) {
    var coalesced = CoalesceFromRootBlock(blocks);
    blocks.Clear();
    blocks.AddRange(coalesced);
  }
  
  public static IList<Block> CoalesceFromRootBlock(IList<Block> blocks)
  {
    if (!blocks.Any())
    {
      return blocks;
    }
    var multiPredecessorBlocks = ComputeMultiPredecessorBlocks(blocks[0]);
    Contract.Assert(Cce.NonNullElements(multiPredecessorBlocks));
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
      if (gotoCmd.LabelTargets == null)
      {
        continue;
      }

      if (gotoCmd.LabelTargets.Count != 1)
      {
        foreach (var aSuccessor in gotoCmd.LabelTargets)
        {
          Contract.Assert(aSuccessor != null);
          toVisit.Push(aSuccessor);
        }
        continue;
      }

      var successor = Cce.NonNull(gotoCmd.LabelTargets[0]);
      if (multiPredecessorBlocks.Contains(successor))
      {
        toVisit.Push(successor);
        continue;
      }

      // Previously this was block.Cmds.AddRange,
      // command lists are reused between blocks
      // so that was buggy. Maybe Block.Cmds should be made immutable
      block.Cmds = block.Cmds.Concat(successor.Cmds).ToList();
      var originalTransferToken = block.TransferCmd.tok;
      block.TransferCmd = successor.TransferCmd;
      if (!block.TransferCmd.tok.IsValid) {
        block.TransferCmd = (TransferCmd)block.TransferCmd.Clone();
        block.TransferCmd.tok = originalTransferToken;
      }
      
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