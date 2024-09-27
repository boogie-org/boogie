using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text.Json.Nodes;
using Microsoft.Boogie;
using VC;
using Block = Microsoft.Boogie.Block;
using Cmd = Microsoft.Boogie.Cmd;
using PredicateCmd = Microsoft.Boogie.PredicateCmd;
using QKeyValue = Microsoft.Boogie.QKeyValue;
using VCGenOptions = Microsoft.Boogie.VCGenOptions;

namespace VCGeneration;

public static class FocusAttribute
{
  
  /// <summary>
  /// Each focus block creates two options.
  /// We recurse twice for each focus, leading to potentially 2^N splits 
  /// </summary>
  public static List<ManualSplit> SplitOnFocus(VCGenOptions options, ImplementationRun run,
    Func<IToken, List<Block>, ManualSplit> createSplit)
  {
    var impl = run.Implementation;
    var dag = Program.GraphFromImpl(impl);
    var topologicallySortedBlocks = dag.TopologicalSort().ToList();
    // By default, we process the foci in a top-down fashion, i.e., in the topological order.
    // If the user sets the RelaxFocus flag, we use the reverse (topological) order.
    var focusBlocks = GetFocusBlocks(topologicallySortedBlocks);
    if (options.RelaxFocus) {
      focusBlocks.Reverse();
    }
    if (!focusBlocks.Any()) {
      return new List<ManualSplit> { createSplit(run.Implementation.tok, impl.Blocks) };
    }

    var ancestorsPerBlock = new Dictionary<Block, HashSet<Block>>();
    var descendantsPerBlock = new Dictionary<Block, HashSet<Block>>();
    focusBlocks.ForEach(fb => {
      var reachables = dag.ComputeReachability(fb.Block, false).ToHashSet();
      reachables.Remove(fb.Block);
      ancestorsPerBlock[fb.Block] = reachables;
    });
    focusBlocks.ForEach(fb => descendantsPerBlock[fb.Block] = dag.ComputeReachability(fb.Block).ToHashSet());
    var result = new List<ManualSplit>();
    var duplicator = new Duplicator();

    FocusRec(run.Implementation.tok, 0, impl.Blocks, new List<Block>());
    return result;

    void FocusRec(IToken focusToken, int focusIndex, IReadOnlyList<Block> blocksToInclude, IReadOnlyList<Block> freeAssumeBlocks)
    {
      if (focusIndex == focusBlocks.Count)
      {
        // it is important for l to be consistent with reverse topological order.
        var reverseSortedBlocks = topologicallySortedBlocks.Where(blocksToInclude.Contains).Reverse();
        // assert that the root block, impl.Blocks[0], is in l
        var newBlocks = new List<Block>();
        var oldToNewBlockMap = new Dictionary<Block, Block>(blocksToInclude.Count());
        foreach (var block in reverseSortedBlocks)
        {
          var newBlock = (Block)duplicator.Visit(block);
          newBlocks.Add(newBlock);
          oldToNewBlockMap[block] = newBlock;
          // freeBlocks consist of the predecessors of the relevant foci.
          // Their assertions turn into assumes and any splits inside them are disabled.
          if(freeAssumeBlocks.Contains(block))
          {
            newBlock.Cmds = block.Cmds.Select(c => CommandTransformations.AssertIntoAssume(options, c)).Select(DisableSplits).ToList();
          }
          if (block.TransferCmd is GotoCmd gtc)
          {
            var targets = gtc.labelTargets.Where(blocksToInclude.Contains).ToList();
            newBlock.TransferCmd = new GotoCmd(gtc.tok,
              targets.Select(blk => oldToNewBlockMap[blk].Label).ToList(),
              targets.Select(blk => oldToNewBlockMap[blk]).ToList());
          }
        }
        newBlocks.Reverse();
        Contract.Assert(newBlocks[0] == oldToNewBlockMap[impl.Blocks[0]]);
        BlockTransformations.DeleteBlocksNotLeadingToAssertions(newBlocks);
        result.Add(createSplit(focusToken, newBlocks));
      } else {
        var (focusBlock, nextToken) = focusBlocks[focusIndex]; // assert b in blocks
        if (!blocksToInclude.Contains(focusBlocks[focusIndex].Block) || freeAssumeBlocks.Contains(focusBlocks[focusIndex].Block))
        {
          // This focus block can not be reached in our current path, so we ignore it by continuing
          FocusRec(focusToken, focusIndex + 1, blocksToInclude, freeAssumeBlocks);
        }
        else
        {
          var dominatedBlocks = DominatedBlocks(topologicallySortedBlocks, focusBlock, blocksToInclude);
          // Recursive call that does NOT focus the block
          // Contains all blocks except the ones dominated by the focus block
          FocusRec(focusToken, focusIndex + 1, 
            blocksToInclude.Where(blk => !dominatedBlocks.Contains(blk)).ToList(), freeAssumeBlocks);
          var ancestors = ancestorsPerBlock[focusBlock];
          var descendants = descendantsPerBlock[focusBlock];
          
          // TODO: nextToken should be a combination of focusToken and nextToken
          // Recursive call that does focus the block
          // Contains all the ancestors, the focus block, and the descendants.
          FocusRec(nextToken, focusIndex + 1, 
            ancestors.Union(descendants).Intersect(blocksToInclude).ToList(), 
            ancestors.Union(freeAssumeBlocks).ToList());
        } 
      }
    }
  }
    
  // finds all the blocks dominated by focusBlock in the subgraph
  // which only contains vertices of subgraph.
  private static HashSet<Block> DominatedBlocks(List<Block> topologicallySortedBlocks, Block focusBlock, IReadOnlyList<Block> subgraph)
  {
    var dominators = new Dictionary<Block, HashSet<Block>>();
    foreach (var b in topologicallySortedBlocks.Where(subgraph.Contains))
    {
      var s = new HashSet<Block>();
      var pred = b.Predecessors.Where(subgraph.Contains).ToList();
      if (pred.Count != 0)
      {
        s.UnionWith(dominators[pred[0]]);
        pred.ForEach(blk => s.IntersectWith(dominators[blk]));
      }
      s.Add(b);
      dominators[b] = s;
    }
    return subgraph.Where(blk => dominators[blk].Contains(focusBlock)).ToHashSet();
  }

  private static Cmd DisableSplits(Cmd command)
  {
    if (command is not PredicateCmd pc)
    {
      return command;
    }

    pc.Attributes = new QKeyValue(Token.NoToken, "split", 
      new List<object> { new LiteralExpr(Token.NoToken, false) }, pc.Attributes);
    return command;
  }
  
  private static List<(Block Block, IToken Token)> GetFocusBlocks(List<Block> blocks) {
    return blocks.
      Select(block => (Block: block, FocusCommand: block.Cmds.FirstOrDefault(IsFocusCmd)?.tok)).
      Where(t => t.FocusCommand != null).ToList();
  }

  private static bool IsFocusCmd(Cmd c) {
    return c is PredicateCmd p && QKeyValue.FindBoolAttribute(p.Attributes, "focus");
  }
}