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
  public VCGenOptions Options { get; }
  public Graph<Block> Dag { get; }
  public Func<ImplementationPartOrigin, List<Block>, ManualSplit> CreateSplit { get; }

  public BlockRewriter(VCGenOptions options, List<Block> blocks,
    Func<ImplementationPartOrigin, List<Block>, ManualSplit> createSplit) {
    this.Options = options;
    CreateSplit = createSplit;
    Dag = Program.GraphFromBlocks(blocks);
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
          : Program.GraphFromBlocksSubset(newToOldBlocks[path.Peek()], blocksToInclude);
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
    IEnumerable<Block> blocksReversed,
    ISet<Block> freeAssumeBlocks) {
    return ComputeNewBlocks(blocksToInclude, blocksReversed, block =>
      freeAssumeBlocks.Contains(block)
        ? block.Cmds.Select(c => CommandTransformations.AssertIntoAssume(Options, c)).ToList()
        : block.Cmds);
  }

  public (List<Block> NewBlocks, Dictionary<Block, Block> Mapping) ComputeNewBlocks(
    ISet<Block> blocksToInclude, 
    IEnumerable<Block> blocksReversed,
    Func<Block, List<Cmd>> getCommands)
  {
    var newBlocks = new List<Block>();
    var oldToNewBlockMap = new Dictionary<Block, Block>(blocksToInclude.Count);
        
    // Traverse backwards to allow settings the jumps to the new blocks
    foreach (var block in blocksReversed)
    {
      if (!blocksToInclude.Contains(block)) {
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
        var targets = gtc.LabelTargets.Where(blocksToInclude.Contains).ToList();
        newBlock.TransferCmd = new GotoCmd(gtc.tok,
          targets.Select(blk => oldToNewBlockMap[blk].Label).ToList(),
          targets.Select(blk => oldToNewBlockMap[blk]).ToList());
      }
    }
    newBlocks.Reverse();
    
    // TODO remove?
    BlockTransformations.DeleteBlocksNotLeadingToAssertions(newBlocks);
    return (newBlocks, oldToNewBlockMap);
  }
  
  public static OrderedDictionary<Block, Block> UpdateBlocks(Stack<Block> blocksToVisit, 
    HashSet<Block> visitedBlocks, Func<Block, List<Cmd>> getCommands)
  {
    var oldToNewBlockMap = new OrderedDictionary<Block, Block>();
    while(blocksToVisit.Any()) {
      var oldBlock = blocksToVisit.Pop();
      if (!visitedBlocks.Add(oldBlock)) {
        continue;
      }
        
      var newBlock = Block.ShallowClone(oldBlock);
      oldToNewBlockMap.Add(oldBlock, newBlock);
      newBlock.Cmds = getCommands(oldBlock);
      foreach (var previous in oldBlock.Predecessors) {
        blocksToVisit.Push(previous);
      }
        
    }

    foreach (var (oldBlock, newBlock) in oldToNewBlockMap) {
      if (oldBlock.TransferCmd is GotoCmd gtc)
      {
        var targets = gtc.LabelTargets.Where(oldToNewBlockMap.ContainsKey).ToList();
        newBlock.TransferCmd = new GotoCmd(gtc.tok,
          targets.Select(block => oldToNewBlockMap[block].Label).ToList(),
          targets.Select(block => oldToNewBlockMap[block]).ToList());
      }
    }

    return oldToNewBlockMap;
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
}