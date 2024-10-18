#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using VC;

namespace VCGeneration.Splits;

public class BlockRewriter {
  private readonly Dictionary<AssertCmd, Cmd> assumedAssertions = new();
  private readonly IReadOnlyList<Block> reversedBlocks;
  public List<Block> OrderedBlocks { get; }
  public VCGenOptions Options { get; }
  public Graph<Block> Dag { get; }
  public Func<IImplementationPartOrigin, List<Block>, ManualSplit> CreateSplit { get; }

  public BlockRewriter(VCGenOptions options, List<Block> blocks,
    Func<IImplementationPartOrigin, List<Block>, ManualSplit> createSplit) {
    this.Options = options;
    CreateSplit = createSplit;
    Dag = Program.GraphFromBlocks(blocks);
    OrderedBlocks = Dag.TopologicalSort();
    reversedBlocks = OrderedBlocks.Reversed();
  }

  public Cmd TransformAssertCmd(Cmd cmd) {
    if (cmd is AssertCmd assertCmd) {
      return assumedAssertions.GetOrCreate(assertCmd,
        () => VerificationConditionGenerator.AssertTurnedIntoAssume(Options, assertCmd));
    }

    return cmd;
  }

  public IEnumerable<ManualSplit> GetSplitsForIsolatedPaths(Block lastBlock, IReadOnlySet<Block>? blocksToInclude,
    IToken origin) {
    var blockToVisit = new Stack<ImmutableStack<Block>>();
    var newToOldBlocks = new Dictionary<Block, Block>();
    var newLastBlock = Block.ShallowClone(lastBlock);
    newLastBlock.Predecessors = lastBlock.Predecessors;
    blockToVisit.Push(ImmutableStack.Create(newLastBlock));
    newToOldBlocks[newLastBlock] = lastBlock;

    while (blockToVisit.Any()) {
      var path = blockToVisit.Pop();
      var firstBlock = path.Peek();
      IEnumerable<Block> predecessors = firstBlock.Predecessors;
      if (blocksToInclude != null) {
        predecessors = predecessors.Where(blocksToInclude.Contains);
      }

      var hadPredecessors = false;
      foreach (var oldPrevious in predecessors) {
        hadPredecessors = true;
        var newPrevious = Block.ShallowClone(oldPrevious);
        newPrevious.Predecessors = oldPrevious.Predecessors;
        newPrevious.Cmds = oldPrevious.Cmds.Select(TransformAssertCmd).ToList();

        newToOldBlocks[newPrevious] = oldPrevious;
        if (newPrevious.TransferCmd is GotoCmd gotoCmd) {
          newPrevious.TransferCmd =
            new GotoCmd(gotoCmd.tok, new List<string> { firstBlock.Label }, new List<Block> {
              firstBlock
            });
        }

        blockToVisit.Push(path.Push(newPrevious));
      }

      if (!hadPredecessors) {
        var filteredDag = blocksToInclude == null
          ? Dag
          : Program.GraphFromBlocksSubset(OrderedBlocks, blocksToInclude);
        var nonDominatedBranches = path.Where(b =>
          !filteredDag.DominatorMap.DominatedBy(lastBlock, newToOldBlocks[b])).ToList();
        var singletonBlock = Block.ShallowClone(firstBlock);
        singletonBlock.TransferCmd = new ReturnCmd(origin);
        singletonBlock.Cmds = path.SelectMany(b => b.Cmds).ToList();
        yield return CreateSplit(new PathOrigin(origin, nonDominatedBranches), new List<Block> { singletonBlock });
      }
    }
  }

  public (List<Block> NewBlocks, Dictionary<Block, Block> Mapping) ComputeNewBlocks(
    ISet<Block> blocksToInclude,
    ISet<Block> freeAssumeBlocks) {
    return ComputeNewBlocks(blocksToInclude, block =>
      freeAssumeBlocks.Contains(block)
        ? block.Cmds.Select(c => CommandTransformations.AssertIntoAssume(Options, c)).ToList()
        : block.Cmds);
  }

  public (List<Block> NewBlocks, Dictionary<Block, Block> Mapping) ComputeNewBlocks(
    ISet<Block>? blocksToInclude,
    Func<Block, List<Cmd>> getCommands)
  {
    var newBlocks = new List<Block>();
    var oldToNewBlockMap = new Dictionary<Block, Block>(reversedBlocks.Count);
        
    // Traverse backwards to allow settings the jumps to the new blocks
    foreach (var block in reversedBlocks)
    {
      if (blocksToInclude != null && !blocksToInclude.Contains(block)) {
        continue;
      }

      var newBlock = Block.ShallowClone(block);
      newBlocks.Add(newBlock);
      oldToNewBlockMap[block] = newBlock;
      // freeBlocks consist of the predecessors of the relevant foci.
      // Their assertions turn into assumes and any splits inside them are disabled.
      newBlock.Cmds = getCommands(block);
      
      if (block.TransferCmd is GotoCmd gtc)
      {
        var targets = blocksToInclude == null ? gtc.LabelTargets : gtc.LabelTargets.Where(blocksToInclude.Contains).ToList();
        newBlock.TransferCmd = new GotoCmd(gtc.tok,
          targets.Select(blk => oldToNewBlockMap[blk].Label).ToList(),
          targets.Select(blk => oldToNewBlockMap[blk]).ToList());
      }
    }
    newBlocks.Reverse();
    
    BlockTransformations.DeleteBlocksNotLeadingToAssertions(newBlocks);
    return (newBlocks, oldToNewBlockMap);
  }


  public static bool ShouldIsolate(bool splitOnEveryAssert, QKeyValue? isolateAttribute)
  {
    return splitOnEveryAssert || isolateAttribute != null;
  }
}