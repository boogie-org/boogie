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


  /// <summary>
  /// Each focus block creates two options.
  /// We recurse twice for each focus, leading to potentially 2^N splits
  /// </summary>
  public IEnumerable<ManualSplit> GetSplitsForIsolatedPaths(Block lastBlock, IReadOnlySet<Block> blocksToInclude, IImplementationPartOrigin origin) 
  {
    // By default, we process the foci in a top-down fashion, i.e., in the topological order.
    // If the user sets the RelaxFocus flag, we use the reverse (topological) order.
    var splitCommands = GetSplitCommands(blocksToInclude);
    if (!splitCommands.Any()) {
      return new List<ManualSplit> { CreateSplit(origin, OrderedBlocks) };
    }
    
    var result = new List<ManualSplit>();

    AddSplitsFromIndex(ImmutableStack<Block>.Empty, 0, blocksToInclude);
    return result;

    void AddSplitsFromIndex(ImmutableStack<Block> choices, int gotoIndex, IReadOnlySet<Block> blocksToIncludeForChoices) {
      
      if (!blocksToIncludeForChoices.Any()) {
        return;
      }
      
      var allFocusBlocksHaveBeenProcessed = gotoIndex == splitCommands.Count;
      if (allFocusBlocksHaveBeenProcessed) {
        
        // freeBlocks consist of the predecessors of the relevant foci.
        // Their assertions turn into assumes and any splits inside them are disabled.
        var newBlocks = ComputeNewBlocks(blocksToIncludeForChoices,
          (oldBlock, newBlock) => {
            newBlock.Cmds = oldBlock == lastBlock ? oldBlock.Cmds : oldBlock.Cmds.Select(TransformAssertCmd).ToList();
            if (oldBlock == lastBlock) {
              newBlock.TransferCmd = new ReturnCmd(origin);
            }
          });
        result.Add(CreateSplit(new PathOrigin(origin, choices.OrderBy(b => b.tok.pos).ToList()), newBlocks));
      } else {
        var splitGoto = splitCommands[gotoIndex];
        if (!blocksToIncludeForChoices.Contains(splitGoto.Block))
        {
          AddSplitsFromIndex(choices, gotoIndex + 1, blocksToIncludeForChoices);
        } else {
          var includedTargetBlocks = splitGoto.Goto.LabelTargets.Where(blocksToIncludeForChoices.Contains).ToList();

          var remainingBlocks = blocksToIncludeForChoices.Where(
            blk => Dag.DominatorMap.DominatedBy(splitGoto.Block, blk)).ToHashSet();
          AddSplitsFromIndex(choices, gotoIndex + 1, remainingBlocks);

          var addChoice = /*remainingBlocks.Any() ||*/ includedTargetBlocks.Count > 1;
          var ancestors = Dag.ComputeReachability(splitGoto.Block, false);
          foreach (var targetBlock in includedTargetBlocks) {
            var descendants = Dag.ComputeReachability(targetBlock, true);
          
            // Recursive call that does focus the block
            // Contains all the ancestors, the focus block, and the descendants.
            var newChoices = addChoice ? choices.Push(targetBlock) : choices;
            AddSplitsFromIndex(newChoices, gotoIndex + 1, 
                ancestors.Union(descendants).Intersect(blocksToIncludeForChoices).ToHashSet()); 
          }
        }
      }
    }
  }


  // finds all the blocks dominated by focusBlock in the subgraph
  // which only contains vertices of subgraph.
  public static HashSet<Block> DominatedBlocks(List<Block> topologicallySortedBlocks, Block focusBlock, IReadOnlySet<Block> subgraph)
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
  
  private static List<(Block Block, GotoCmd Goto)> GetSplitCommands(IEnumerable<Block> blocks) {
    return blocks.
      Where(t => t.TransferCmd is GotoCmd gotoCmd && gotoCmd.Attributes.FindBoolAttribute(AllowSplit)).
      Select(block => (block, (GotoCmd)block.TransferCmd)).ToList();
  }

  public List<Block> ComputeNewBlocks(
    IReadOnlySet<Block> blocksToInclude,
    ISet<Block> freeAssumeBlocks) {
    return ComputeNewBlocks(blocksToInclude, (oldBlock, newBlock) => {
        newBlock.Cmds = freeAssumeBlocks.Contains(oldBlock)
          ? oldBlock.Cmds.Select(c => CommandTransformations.AssertIntoAssume(Options, c)).ToList()
          : oldBlock.Cmds;
      });
  }

  public List<Block> ComputeNewBlocks(
    IReadOnlySet<Block>? blocksToInclude,
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