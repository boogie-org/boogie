using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using VC;
using Block = Microsoft.Boogie.Block;
using Cmd = Microsoft.Boogie.Cmd;
using PredicateCmd = Microsoft.Boogie.PredicateCmd;
using QKeyValue = Microsoft.Boogie.QKeyValue;
using VCGenOptions = Microsoft.Boogie.VCGenOptions;

namespace VCGeneration;

public static class Focus
{
  
  /// <summary>
  /// Each focus block creates two options.
  /// We recurse twice for each focus, leading to potentially 2^N splits
  /// </summary>
  public static List<ManualSplit> SplitOnFocus(VCGenOptions options, ImplementationRun run,
    Func<ImplementationPartToken, List<Block>, ManualSplit> createSplit)
  {
    var impl = run.Implementation;
    var dag = Program.GraphFromImpl(impl);
    var topologicallySortedBlocks = dag.TopologicalSort().ToList();
    var blocksReversed = Enumerable.Reverse(topologicallySortedBlocks).ToList();
    // By default, we process the foci in a top-down fashion, i.e., in the topological order.
    // If the user sets the RelaxFocus flag, we use the reverse (topological) order.
    var focusBlocks = GetFocusBlocks(topologicallySortedBlocks);
    if (options.RelaxFocus) {
      focusBlocks.Reverse();
    }
    if (!focusBlocks.Any()) {
      return new List<ManualSplit> { createSplit(new ImplementationRootToken(run.Implementation), impl.Blocks) };
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

    AddSplitsFromIndex(ImmutableStack<IToken>.Empty, 0, impl.Blocks.ToHashSet(), ImmutableHashSet<Block>.Empty);
    return result;

    void AddSplitsFromIndex(ImmutableStack<IToken> path, int focusIndex, ISet<Block> blocksToInclude, ISet<Block> freeAssumeBlocks) {
      var allFocusBlocksHaveBeenProcessed = focusIndex == focusBlocks.Count;
      if (allFocusBlocksHaveBeenProcessed) {
        var newBlocks = ComputeNewBlocks(options, blocksToInclude, blocksReversed, freeAssumeBlocks);
        result.Add(createSplit(new PathToken(run.Implementation.tok, path), newBlocks));
      } else {
        var (focusBlock, nextToken) = focusBlocks[focusIndex]; // assert b in blocks
        if (!blocksToInclude.Contains(focusBlock) || freeAssumeBlocks.Contains(focusBlock))
        {
          // This focus block can not be reached in our current path, so we ignore it by continuing
          AddSplitsFromIndex(path, focusIndex + 1, blocksToInclude, freeAssumeBlocks);
        }
        else
        {
          var dominatedBlocks = DominatedBlocks(topologicallySortedBlocks, focusBlock, blocksToInclude);
          // Recursive call that does NOT focus the block
          // Contains all blocks except the ones dominated by the focus block
          AddSplitsFromIndex(path, focusIndex + 1, 
            blocksToInclude.Where(blk => !dominatedBlocks.Contains(blk)).ToHashSet(), freeAssumeBlocks);
          var ancestors = ancestorsPerBlock[focusBlock];
          var descendants = descendantsPerBlock[focusBlock];
          
          // Recursive call that does focus the block
          // Contains all the ancestors, the focus block, and the descendants.
          AddSplitsFromIndex(path.Push(nextToken), focusIndex + 1, 
            ancestors.Union(descendants).Intersect(blocksToInclude).ToHashSet(), 
            ancestors.Union(freeAssumeBlocks).ToHashSet());
        } 
      }
    }
  }

  private static List<Block> ComputeNewBlocks(VCGenOptions options, ISet<Block> blocksToInclude, List<Block> blocksReversed,
    ISet<Block> freeAssumeBlocks)
  {
    var duplicator = new Duplicator();
    var newBlocks = new List<Block>();
    var oldToNewBlockMap = new Dictionary<Block, Block>(blocksToInclude.Count);
        
    // Traverse backwards to allow settings the jumps to the new blocks
    foreach (var block in blocksReversed)
    {
      if (!blocksToInclude.Contains(block)) {
        continue;
      }
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
        var targets = gtc.LabelTargets.Where(blocksToInclude.Contains).ToList();
        newBlock.TransferCmd = new GotoCmd(gtc.tok,
          targets.Select(blk => oldToNewBlockMap[blk].Label).ToList(),
          targets.Select(blk => oldToNewBlockMap[blk]).ToList());
      }
    }
    newBlocks.Reverse();
    BlockTransformations.DeleteBlocksNotLeadingToAssertions(newBlocks);
    return newBlocks;
  }

  // finds all the blocks dominated by focusBlock in the subgraph
  // which only contains vertices of subgraph.
  private static HashSet<Block> DominatedBlocks(List<Block> topologicallySortedBlocks, Block focusBlock, ISet<Block> subgraph)
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