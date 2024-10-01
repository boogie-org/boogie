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
  private readonly Graph<Block> dag;
  public Func<ImplementationPartOrigin, List<Block>, ManualSplit> CreateSplit { get; }

  public BlockRewriter(VCGenOptions options, List<Block> blocks, Func<ImplementationPartOrigin, List<Block>, ManualSplit> createSplit) {
    this.Options = options;
    CreateSplit = createSplit;
    dag = Program.GraphFromBlocks(blocks);
  }

  public Cmd TransformAssertCmd(Cmd cmd) {
    if (cmd is AssertCmd assertCmd) {
      return assumedAssertions.GetOrCreate(assertCmd, () => VerificationConditionGenerator.AssertTurnedIntoAssume(Options, assertCmd));
    }

    return cmd;
  }

  public IEnumerable<ManualSplit> GetSplitsForIsolatedPaths(Block lastBlock, ISet<Block>? blocksToInclude, IToken origin) {
    var blockToVisit = new Stack<ImmutableStack<Block>>();
    blockToVisit.Push(ImmutableStack.Create(new Block(lastBlock.tok)
    {
      Predecessors = lastBlock.Predecessors,
      Label = lastBlock.Label,
      TransferCmd = null,
      Cmds = lastBlock.Cmds
    }));
    
    while(blockToVisit.Any()) {
      var path = blockToVisit.Pop();
      var firstBlock = path.Peek();
      IEnumerable<Block> predecessors = firstBlock.Predecessors;
      if (blocksToInclude != null) {
        predecessors = predecessors.Where(blocksToInclude.Contains);
      }

      var hadPredecessors = false;
      foreach (var oldPrevious in predecessors) {
        hadPredecessors = true;
        var newPrevious = new Block(oldPrevious.tok)
        {
          Predecessors = oldPrevious.Predecessors,
          Label = oldPrevious.Label,
          TransferCmd = oldPrevious.TransferCmd,
          Cmds = oldPrevious.Cmds.Select(TransformAssertCmd).ToList()
        };
        if (newPrevious.TransferCmd is GotoCmd gotoCmd) {
          newPrevious.TransferCmd =
            new GotoCmd(gotoCmd.tok, new List<string> { firstBlock.Label }, new List<Block>
            {
              firstBlock
            });
        }
        blockToVisit.Push(path.Push(newPrevious));
      }
      if (!hadPredecessors) {
        yield return CreateSplit(new PathOrigin(origin, path, dag.DominatorMap), new List<Block> { new(firstBlock.tok) {
          Label = firstBlock.Label,
          Cmds = path.SelectMany(b => b.Cmds).ToList() 
        } });
      }
    }
  }
  
  public List<Block> ComputeNewBlocks(ISet<Block> blocksToInclude, IEnumerable<Block> blocksReversed,
    ISet<Block> freeAssumeBlocks)
  {
    var duplicator = new Duplicator();
    var newBlocks = new List<Block>();
    var oldToNewBlockMap = new Dictionary<Block, Block>(blocksToInclude.Count);
        
    // TODO, use ManualSplitFinder.CreateSplit()
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
        newBlock.Cmds = block.Cmds.Select(c => CommandTransformations.AssertIntoAssume(Options, c)).Select(DisableSplits).ToList();
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
    
    // TODO remove?
    BlockTransformations.DeleteBlocksNotLeadingToAssertions(newBlocks);
    return newBlocks;
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
        
      var newBlock = new Block(oldBlock.tok)
      {
        Label = oldBlock.Label
      };
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