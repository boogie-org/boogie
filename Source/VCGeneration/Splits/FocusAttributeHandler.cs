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

namespace VCGeneration;

public class FocusAttributeHandler {

  /// <summary>
  /// Each focus block creates two options.
  /// We recurse twice for each focus, leading to potentially 2^N splits
  /// </summary>
  public static List<ManualSplit> GetParts(VCGenOptions options, ImplementationRun run, 
    Func<IImplementationPartOrigin, IList<Block>, ManualSplit> createPart)
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

    AddSplitsFromIndex(ImmutableStack<IToken>.Empty, 0, implementation.Blocks.ToHashSet(), ImmutableHashSet<Block>.Empty);
    return result;

    void AddSplitsFromIndex(ImmutableStack<IToken> focusedBlocks, int focusIndex, IReadOnlySet<Block> blocksToInclude, ISet<Block> freeAssumeBlocks) {
      var allFocusBlocksHaveBeenProcessed = focusIndex == focusBlocks.Count;
      if (allFocusBlocksHaveBeenProcessed) {
        
        // freeBlocks consist of the predecessors of the relevant foci.
        // Their assertions turn into assumes and any splits inside them are disabled.
        var newBlocks = rewriter.ComputeNewBlocks(blocksToInclude, freeAssumeBlocks);
        var focussedSet = focusedBlocks.ToHashSet();
        IImplementationPartOrigin token = focusedBlocks.Any() 
          ? new FocusOrigin(new ImplementationRootOrigin(run.Implementation), 
            focusBlocks.Select(b => (b.Token, focussedSet.Contains(b.Token))).ToList()) 
          : new ImplementationRootOrigin(run.Implementation); 
        result.Add(rewriter.CreateSplit(token, newBlocks));
      } else {
        var (focusBlock, nextToken) = focusBlocks[focusIndex]; // assert b in blocks
        if (!blocksToInclude.Contains(focusBlock) || freeAssumeBlocks.Contains(focusBlock))
        {
          // This focus block can not be reached in our current path, so we ignore it by continuing
          AddSplitsFromIndex(focusedBlocks, focusIndex + 1, blocksToInclude, freeAssumeBlocks);
        }
        else
        {
          var dominatedBlocks = BlockRewriter.DominatedBlocks(rewriter.OrderedBlocks, focusBlock, blocksToInclude);
          // Recursive call that does NOT focus the block
          // Contains all blocks except the ones dominated by the focus block
          AddSplitsFromIndex(focusedBlocks, focusIndex + 1, 
            blocksToInclude.Where(blk => !dominatedBlocks.Contains(blk)).ToHashSet(), freeAssumeBlocks);
          var ancestors = ancestorsPerBlock[focusBlock];
          var descendants = descendantsPerBlock[focusBlock];
          
          // Recursive call that does focus the block
          // Contains all the ancestors, the focus block, and the descendants.
          AddSplitsFromIndex(focusedBlocks.Push(nextToken), focusIndex + 1, 
            ancestors.Union(descendants).Intersect(blocksToInclude).ToHashSet(), 
            ancestors.Union(freeAssumeBlocks).ToHashSet());
        } 
      }
    }
  }
  
  private static List<(Block Block, IToken Token)> GetFocusBlocks(List<Block> blocks) {
    return blocks.
      Select(block => (Block: block, FocusCommand: block.Cmds.FirstOrDefault(IsFocusCmd)?.tok)).
      Where(t => t.FocusCommand != null).ToList();
  }

  private static bool IsFocusCmd(Cmd c) {
    return c is PredicateCmd p && p.Attributes.FindBoolAttribute("focus");
  }
}