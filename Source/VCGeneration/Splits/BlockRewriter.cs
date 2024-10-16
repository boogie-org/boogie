#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Security.Principal;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using VC;

namespace VCGeneration.Splits;

public class BlockRewriter {
  private const string AllowSplit = "allow_split";
  public static readonly QKeyValue AllowSplitQ = new(Token.NoToken, AllowSplit);
  
  private readonly Dictionary<AssertCmd, Cmd> assumedAssertions = new();
  private readonly IReadOnlyList<Block> reversedBlocks;
  public List<Block> OrderedBlocks { get; }
  public VCGenOptions Options { get; }
  public Graph<Block> Dag { get; }
  public Func<IImplementationPartOrigin, IList<Block>, ManualSplit> CreateSplit { get; }

  public BlockRewriter(VCGenOptions options, IList<Block> blocks,
    Func<IImplementationPartOrigin, IList<Block>, ManualSplit> createSplit) {
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
    var filteredDag = blocksToInclude == null
      ? Dag
      : Program.GraphFromBlocksSubset(OrderedBlocks, blocksToInclude);
    
    var blockToVisit = new Stack<(Block Current, ImmutableStack<Block> Choices, ImmutableHashSet<Block> Included)>();
    
    blockToVisit.Push((lastBlock, ImmutableStack<Block>.Empty, ImmutableHashSet.Create(lastBlock)));

    while (blockToVisit.Any()) {
      var path = blockToVisit.Pop();
      var current = path.Current;
      var predecessors = current.Predecessors;
      if (blocksToInclude != null) {
        predecessors = predecessors.Where(blocksToInclude.Contains).ToList();
      }

      switch (predecessors.Count)
      {
        case 0:
          var newBlocks = ComputeNewBlocks(path.Included.ToHashSet(),
              (oldBlock, newBlock) => {
                newBlock.Cmds = oldBlock == lastBlock ? oldBlock.Cmds : oldBlock.Cmds.Select(TransformAssertCmd).ToList();
                if (oldBlock == lastBlock) {
                  newBlock.TransferCmd = new ReturnCmd(origin);
                }
              });
            
          yield return CreateSplit(new PathOrigin(origin, path.Choices.ToList()), newBlocks);
          break;
        case 1:
          var singlePredecessor = predecessors.First();
          blockToVisit.Push((singlePredecessor, path.Choices, path.Included.Add(singlePredecessor)));
          break;
        default:
          var immediateDominator = Dag.DominatorMap.GetImmediateDominator(current);
          if (immediateDominator.TransferCmd is GotoCmd gotoCmd && gotoCmd.Attributes.FindBoolAttribute(AllowSplit))
          {
            foreach (var predecessor in predecessors)
            {
              blockToVisit.Push((predecessor, path.Choices.Push(predecessor), path.Included.Add(predecessor)));
            }
          }
          else
          {
            var included = path.Included;
            foreach (var inBetweenNode in Dag.DominatorMap.GetNodesUntilImmediateDominatorForDag(current))
            {
              included = included.Add(inBetweenNode);
            }

            included = included.Add(immediateDominator);
            blockToVisit.Push((immediateDominator, path.Choices, included));
          }

          break;
      }


    }
  }

  private static IEnumerable<Block> GetNodesBetween(List<Block> predecessors, ImmutableStack<Block> path,
    Block immediateDominator)
  {
    var smallStack = new Stack<Block>(predecessors);
    var nextPath = path;
    while (smallStack.Any())
    {
      var addition = smallStack.Pop();
      if (addition == immediateDominator)
      {
        continue;
      }

      foreach (var pred in addition.Predecessors)
      {
        smallStack.Push(pred);
      }
      nextPath = nextPath.Push(addition);
    } 
    return nextPath.Push(immediateDominator);
  }

  public List<Block> ComputeNewBlocks(
    ISet<Block> blocksToInclude,
    ISet<Block> freeAssumeBlocks) {
    return ComputeNewBlocks(blocksToInclude, (oldBlock, newBlock) => {
        newBlock.Cmds = freeAssumeBlocks.Contains(oldBlock)
          ? oldBlock.Cmds.Select(c => CommandTransformations.AssertIntoAssume(Options, c)).ToList()
          : oldBlock.Cmds;
      });
  }

  public List<Block> ComputeNewBlocks(
    ISet<Block>? blocksToInclude,
    Action<Block, Block> updateNewBlock)
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
      if (block.TransferCmd is GotoCmd gtc)
      {
        var targets = blocksToInclude == null ? gtc.LabelTargets : gtc.LabelTargets.Where(blocksToInclude.Contains).ToList();
        newBlock.TransferCmd = new GotoCmd(gtc.tok,
          targets.Select(blk => oldToNewBlockMap[blk].Label).ToList(),
          targets.Select(blk => oldToNewBlockMap[blk]).ToList());
      }
      updateNewBlock(block, newBlock);
    }
    newBlocks.Reverse();
    
    BlockTransformations.DeleteBlocksNotLeadingToAssertions(newBlocks);
    
    BlockCoalescer.CoalesceInPlace(newBlocks);
    return newBlocks;
  }


  public static bool ShouldIsolate(bool splitOnEveryAssert, QKeyValue? isolateAttribute)
  {
    return splitOnEveryAssert || isolateAttribute != null;
  }
}