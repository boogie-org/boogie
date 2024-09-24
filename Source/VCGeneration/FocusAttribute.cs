using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using VC;
using Block = Microsoft.Boogie.Block;
using Cmd = Microsoft.Boogie.Cmd;
using PredicateCmd = Microsoft.Boogie.PredicateCmd;
using QKeyValue = Microsoft.Boogie.QKeyValue;
using ReturnCmd = Microsoft.Boogie.ReturnCmd;
using TransferCmd = Microsoft.Boogie.TransferCmd;
using VCGenOptions = Microsoft.Boogie.VCGenOptions;

namespace VCGeneration;

public static class FocusAttribute
{
  
  public static List<ManualSplit> SplitOnFocus(VCGenOptions options, ImplementationRun run, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VerificationConditionGenerator par)
  {
    var impl = run.Implementation;
    var dag = Program.GraphFromImpl(impl);
    var topologicallySortedBlocks = dag.TopologicalSort().ToList();
    // By default, we process the foci in a top-down fashion, i.e., in the topological order.
    // If the user sets the RelaxFocus flag, we use the reverse (topological) order.
    var focusBlocks = GetFocusBlocks(topologicallySortedBlocks);
    if (par.CheckerPool.Options.RelaxFocus) {
      focusBlocks.Reverse();
    }
    if (!focusBlocks.Any()) {
      return new List<ManualSplit> { new(options, () => impl.Blocks, gotoCmdOrigins, par, run, run.Implementation.tok) };
    }

    var ancestorsPerBlock = new Dictionary<Block, HashSet<Block>>();
    var descendantsPerBlock = new Dictionary<Block, HashSet<Block>>();
    focusBlocks.ForEach(fb => ancestorsPerBlock[fb.Block] = dag.ComputeReachability(fb.Block, false).ToHashSet());
    focusBlocks.ForEach(fb => descendantsPerBlock[fb.Block] = dag.ComputeReachability(fb.Block, true).ToHashSet());
    var result = new List<ManualSplit>();
    var duplicator = new Duplicator();

    FocusRec(run.Implementation.tok, 0, impl.Blocks, new List<Block>());
    return result;

    void FocusRec(IToken focusToken, int focusIndex, IReadOnlyList<Block> blocksToInclude, IReadOnlyList<Block> freeAssumeBlocks)
    {
      if (focusIndex == focusBlocks.Count)
      {
        // it is important for l to be consistent with reverse topological order.
        var sortedBlocks = dag.TopologicalSort().Where(blocksToInclude.Contains).Reverse();
        // assert that the root block, impl.Blocks[0], is in l
        var newBlocks = new List<Block>();
        var oldToNewBlockMap = new Dictionary<Block, Block>(blocksToInclude.Count());
        foreach (var block in sortedBlocks)
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
        result.Add(new ManualSplit(options, () =>
        {
          BlockTransformations.DeleteBlocksNotLeadingToAssertions(newBlocks);
          return newBlocks;
        }, gotoCmdOrigins, par, run, focusToken));
      }
      else if (!blocksToInclude.Contains(focusBlocks[focusIndex].Block) || freeAssumeBlocks.Contains(focusBlocks[focusIndex].Block))
      {
        FocusRec(focusBlocks[focusIndex].Token, focusIndex + 1, blocksToInclude, freeAssumeBlocks);
      }
      else
      {
        var (block, nextToken) = focusBlocks[focusIndex]; // assert b in blocks
        var dominatedBlocks = DominatedBlocks(topologicallySortedBlocks, block, blocksToInclude);
        // the first part takes all blocks except the ones dominated by the focus block
        FocusRec(nextToken, focusIndex + 1, blocksToInclude.Where(blk => !dominatedBlocks.Contains(blk)).ToList(), freeAssumeBlocks);
        var ancestors = ancestorsPerBlock[block];
        ancestors.Remove(block);
        var descendants = descendantsPerBlock[block];
        // the other part takes all the ancestors, the focus block, and the descendants.
        FocusRec(nextToken, focusIndex + 1, 
          ancestors.Union(descendants).Intersect(blocksToInclude).ToList(), 
          ancestors.Union(freeAssumeBlocks).ToList());
      }
    }
  }
    
  // finds all the blocks dominated by focusBlock in the subgraph
  // which only contains vertices of subgraph.
  private static HashSet<Block> DominatedBlocks(List<Block> topologicallySortedBlocks, Block focusBlock, IEnumerable<Block> subgraph)
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

    for (var kv = pc.Attributes; kv != null; kv = kv.Next)
    {
      if (kv.Key == "split")
      {
        kv.AddParam(new LiteralExpr(Token.NoToken, false));
      }
    }
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