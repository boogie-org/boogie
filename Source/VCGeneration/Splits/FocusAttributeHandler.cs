using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using VC;
using VCGeneration.Splits;
using Block = Microsoft.Boogie.Block;
using Cmd = Microsoft.Boogie.Cmd;
using PredicateCmd = Microsoft.Boogie.PredicateCmd;
using QKeyValue = Microsoft.Boogie.QKeyValue;

namespace VCGeneration;

public class FocusAttributeHandler {

  /// <summary>
  /// Each focus block creates two options.
  /// We recurse twice for each focus, leading to potentially 2^N splits
  /// </summary>
  public static List<ManualSplit> GetParts(VCGenOptions options, ImplementationRun run, 
    Func<IImplementationPartOrigin, List<Block>, ManualSplit> createPart)
  {
    var rewriter = new BlockRewriter(options, run.Implementation.Blocks, createPart);
    
    var implementation = run.Implementation;
    var dag = rewriter.Dag;
    
    // By default, we process the foci in a top-down fashion, i.e., in the topological order.
    // If the user sets the RelaxFocus flag, we use the reverse (topological) order.
    var focusBlocks = GetFocusBlocks(rewriter.OrderedBlocks);
    if (rewriter.Options.RelaxFocus) {
      focusBlocks.Reverse();
    }
    if (!focusBlocks.Any()) {
      return new List<ManualSplit> { rewriter.CreateSplit(new ImplementationRootOrigin(run.Implementation), implementation.Blocks) };
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

    AddSplitsFromIndex(ImmutableStack<Block>.Empty, 0, implementation.Blocks.ToHashSet(), ImmutableHashSet<Block>.Empty);
    return result;

    void AddSplitsFromIndex(ImmutableStack<Block> path, int focusIndex, ISet<Block> blocksToInclude, ISet<Block> freeAssumeBlocks) {
      var allFocusBlocksHaveBeenProcessed = focusIndex == focusBlocks.Count;
      if (allFocusBlocksHaveBeenProcessed) {
        var (newBlocks, _) = rewriter.ComputeNewBlocks(blocksToInclude, freeAssumeBlocks);
        IImplementationPartOrigin token = path.Any() 
          ? new PathOrigin(run.Implementation.tok, path.ToList()) // TODO fix 
          : new ImplementationRootOrigin(run.Implementation); 
        result.Add(rewriter.CreateSplit(token, newBlocks));
      } else {
        var (focusBlock, nextToken) = focusBlocks[focusIndex]; // assert b in blocks
        if (!blocksToInclude.Contains(focusBlock) || freeAssumeBlocks.Contains(focusBlock))
        {
          // This focus block can not be reached in our current path, so we ignore it by continuing
          AddSplitsFromIndex(path, focusIndex + 1, blocksToInclude, freeAssumeBlocks);
        }
        else
        {
          var dominatedBlocks = DominatedBlocks(rewriter.OrderedBlocks, focusBlock, blocksToInclude);
          // Recursive call that does NOT focus the block
          // Contains all blocks except the ones dominated by the focus block
          AddSplitsFromIndex(path, focusIndex + 1, 
            blocksToInclude.Where(blk => !dominatedBlocks.Contains(blk)).ToHashSet(), freeAssumeBlocks);
          var ancestors = ancestorsPerBlock[focusBlock];
          var descendants = descendantsPerBlock[focusBlock];
          
          // Recursive call that does focus the block
          // Contains all the ancestors, the focus block, and the descendants.
          AddSplitsFromIndex(path.Push(focusBlock), focusIndex + 1, 
            ancestors.Union(descendants).Intersect(blocksToInclude).ToHashSet(), 
            ancestors.Union(freeAssumeBlocks).ToHashSet());
        } 
      }
    }
  }

  // finds all the blocks dominated by focusBlock in the subgraph
  // which only contains vertices of subgraph.
  private static HashSet<Block> DominatedBlocks(List<Block> topologicallySortedBlocks, Block focusBlock, ISet<Block> subgraph)
  {
    var dominatorsPerBlock = new Dictionary<Block, HashSet<Block>>();
    foreach (var block in topologicallySortedBlocks.Where(subgraph.Contains))
    {
      var dominatorsForBlock = new HashSet<Block>();
      var predecessors = block.Predecessors.Where(subgraph.Contains).ToList();
      if (predecessors.Count != 0)
      {
        dominatorsForBlock.UnionWith(dominatorsPerBlock[predecessors[0]]);
        predecessors.ForEach(blk => dominatorsForBlock.IntersectWith(dominatorsPerBlock[blk]));
      }
      dominatorsForBlock.Add(block);
      dominatorsPerBlock[block] = dominatorsForBlock;
    }
    return subgraph.Where(blk => dominatorsPerBlock[blk].Contains(focusBlock)).ToHashSet();
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