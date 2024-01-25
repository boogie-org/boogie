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
  
  public static List<Split> FocusImpl(VCGenOptions options, ImplementationRun run, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VerificationConditionGenerator par)
  {
    bool IsFocusCmd(Cmd c) {
      return c is PredicateCmd p && QKeyValue.FindBoolAttribute(p.Attributes, "focus");
    }

    List<Block> GetFocusBlocks(List<Block> blocks) {
      return blocks.Where(blk => blk.Cmds.Any(IsFocusCmd)).ToList();
    }

    var impl = run.Implementation;
    var dag = Program.GraphFromImpl(impl);
    var topoSorted = dag.TopologicalSort().ToList();
    // By default, we process the foci in a top-down fashion, i.e., in the topological order.
    // If the user sets the RelaxFocus flag, we use the reverse (topological) order.
    var focusBlocks = GetFocusBlocks(topoSorted);
    if (par.CheckerPool.Options.RelaxFocus) {
      focusBlocks.Reverse();
    }
    if (!focusBlocks.Any()) {
      var f = new List<Split>();
      f.Add(new Split(options, impl.Blocks, gotoCmdOrigins, par, run));
      return f;
    }
    // finds all the blocks dominated by focusBlock in the subgraph
    // which only contains vertices of subgraph.
    HashSet<Block> DominatedBlocks(Block focusBlock, IEnumerable<Block> subgraph)
    {
      var dominators = new Dictionary<Block, HashSet<Block>>();
      var todo = new Queue<Block>();
      foreach (var b in topoSorted.Where(blk => subgraph.Contains(blk)))
      {
        var s = new HashSet<Block>();
        var pred = b.Predecessors.Where(blk => subgraph.Contains(blk)).ToList();
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

    var ancestorsPerBlock = new Dictionary<Block, HashSet<Block>>();
    var descendantsPerBlock = new Dictionary<Block, HashSet<Block>>();
    focusBlocks.ForEach(fb => ancestorsPerBlock[fb] = dag.ComputeReachability(fb, false).ToHashSet());
    focusBlocks.ForEach(fb => descendantsPerBlock[fb] = dag.ComputeReachability(fb, true).ToHashSet());
    var result = new List<Split>();
    var duplicator = new Duplicator();

    FocusRec(0, impl.Blocks, new List<Block>());
    return result;

    Cmd DisableSplits(Cmd c)
    {
      if (c is not PredicateCmd pc)
      {
        return c;
      }

      for (var kv = pc.Attributes; kv != null; kv = kv.Next)
      {
        if (kv.Key == "split")
        {
          kv.AddParam(new LiteralExpr(Token.NoToken, false));
        }
      }
      return c;
    }

    void FocusRec(int focusIdx, IReadOnlyList<Block> blocks, IReadOnlyList<Block> freeBlocks)
    {
      if (focusIdx == focusBlocks.Count)
      {
        // it is important for l to be consistent with reverse topological order.
        var l = dag.TopologicalSort().Where(blocks.Contains).Reverse();
        // assert that the root block, impl.Blocks[0], is in l
        Contract.Assert(l.ElementAt(l.Count() - 1) == impl.Blocks[0]);
        var newBlocks = new List<Block>();
        var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count());
        foreach (Block b in l)
        {
          var newBlock = (Block)duplicator.Visit(b);
          newBlocks.Add(newBlock);
          oldToNewBlockMap[b] = newBlock;
          // freeBlocks consist of the predecessors of the relevant foci.
          // Their assertions turn into assumes and any splits inside them are disabled.
          if(freeBlocks.Contains(b))
          {
            newBlock.Cmds = b.Cmds.Select(c => CommandTransformations.AssertIntoAssume(options, c)).Select(c => DisableSplits(c)).ToList();
          }
          if (b.TransferCmd is GotoCmd gtc)
          {
            var targets = gtc.labelTargets.Where(blk => blocks.Contains(blk));
            newBlock.TransferCmd = new GotoCmd(gtc.tok,
              targets.Select(blk => oldToNewBlockMap[blk].Label).ToList(),
              targets.Select(blk => oldToNewBlockMap[blk]).ToList());
          }
        }
        newBlocks.Reverse();
        Contract.Assert(newBlocks[0] == oldToNewBlockMap[impl.Blocks[0]]);
        result.Add(new Split(options, BlockTransformations.PostProcess(newBlocks), gotoCmdOrigins, par, run));
      }
      else if (!blocks.Contains(focusBlocks[focusIdx]) || freeBlocks.Contains(focusBlocks[focusIdx]))
      {
        FocusRec(focusIdx + 1, blocks, freeBlocks);
      }
      else
      {
        var b = focusBlocks[focusIdx]; // assert b in blocks
        var dominatedBlocks = DominatedBlocks(b, blocks);
        // the first part takes all blocks except the ones dominated by the focus block
        FocusRec(focusIdx + 1, blocks.Where(blk => !dominatedBlocks.Contains(blk)).ToList(), freeBlocks);
        var ancestors = ancestorsPerBlock[b];
        ancestors.Remove(b);
        var descendants = descendantsPerBlock[b];
        // the other part takes all the ancestors, the focus block, and the descendants.
        FocusRec(focusIdx + 1, 
          ancestors.Union(descendants).Intersect(blocks).ToList(), 
          ancestors.Union(freeBlocks).ToList());
      }
    }
  }
}