#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using VC;

namespace VCGeneration;

public static class ManualSplitFinder {
  public static List<Block> UpdateBlocks(IReadOnlyList<Block> blocks,
    Func<Block, List<Cmd>> getCommands)
  {
    var newBlocks = new List<Block>(blocks.Count);
    var oldToNewBlockMap = new Dictionary<Block, Block>(newBlocks.Count);
    foreach (var currentBlock in blocks) {
      var newBlock = new Block(currentBlock.tok)
      {
        Label = currentBlock.Label
      };

      oldToNewBlockMap[currentBlock] = newBlock;
      newBlocks.Add(newBlock);
      newBlock.Cmds = getCommands(currentBlock);
    }
      
    AddJumpsToNewBlocks(oldToNewBlockMap);
    return newBlocks;
  }
  
  public static IEnumerable<ManualSplit> SplitOnPathsAndAssertions(VCGenOptions options, ImplementationRun run, 
    Func<ImplementationPartOrigin, List<Block>, ManualSplit> createSplit) {
    var focussedParts = FocusApplier.GetFocusParts(options, run, createSplit);
    var isolatedParts = focussedParts.SelectMany(s =>
      IsolateAttributeHandler.GetPartsFromIsolatedAssertions(options, s, createSplit)).ToList();

    if (!isolatedParts.Any()) {
      return Enumerable.Empty<ManualSplit>();
    }

    var notIsolatedPart = isolatedParts.First();
    return GetVcsForSplits(notIsolatedPart).Concat(isolatedParts.Skip(1));
  }
  
  private static List<ManualSplit> GetVcsForSplits(ManualSplit partToSplit) {
    var splitsPerBlock = new Dictionary<Block, List<Cmd>>();
    var splits = new HashSet<Cmd>();
    foreach (var block in partToSplit.Blocks) {
      var splitsForThisBlock = new List<Cmd>();
      foreach (var command in block.Cmds) {
        if (!ShouldSplitHere(command)) {
          continue;
        }

        splits.Add(command);
        splitsForThisBlock.Add(command);
      }

      if (splitsForThisBlock.Any()) {
        splitsPerBlock[block] = splitsForThisBlock;
      }
    }

    if (!splits.Any()) {
      return new List<ManualSplit> { partToSplit };
    }

    var vcs = new List<ManualSplit>();
    var entryPoint = partToSplit.Blocks[0];
    var blockStartToSplit = GetMapFromBlockStartToSplit(partToSplit.Blocks, splitsPerBlock);

    var beforeSplitsVc = GetImplementationPartAfterSplit(CreateVc, partToSplit, blockStartToSplit,
      entryPoint, splits, null);
    if (beforeSplitsVc != null)
    {
      vcs.Add(beforeSplitsVc);
    }
    foreach (var block in partToSplit.Blocks) {
      var splitsForBlock = splitsPerBlock.GetValueOrDefault(block);
      if (splitsForBlock == null) {
        continue;
      }
        
      foreach (var split in splitsForBlock)
      {
        var splitVc = GetImplementationPartAfterSplit(CreateVc, partToSplit, 
          blockStartToSplit, block, splits, split);
        if (splitVc != null)
        {
          vcs.Add(splitVc);
        }
      }
    }
    return vcs;

    ManualSplit CreateVc(ImplementationPartOrigin token, List<Block> blocks) {
      return new ManualSplit(partToSplit.Options, () => {
        BlockTransformations.Optimize(blocks);
        return blocks;
      }, partToSplit.GotoCmdOrigins, partToSplit.parent, partToSplit.Run, token);
    }
  }

  private static bool ShouldSplitHere(Cmd c) {
    if (c is not PredicateCmd predicateCmd) {
      return false;
    }

    return QKeyValue.FindBoolAttribute(predicateCmd.Attributes, "split_here");
  }

  private static Dictionary<Block, Cmd?> GetMapFromBlockStartToSplit(List<Block> blocks, Dictionary<Block, List<Cmd>> splitsPerBlock) {
    var todo = new Stack<Block>();
    var blockAssignments = new Dictionary<Block, Cmd?>();
    var immediateDominators = Program.GraphFromBlocks(blocks).ImmediateDominator();
    todo.Push(blocks[0]);
    while (todo.Count > 0) {
      var currentBlock = todo.Pop();
      if (blockAssignments.Keys.Contains(currentBlock)) {
        continue;
      }

      if (!immediateDominators.TryGetValue(currentBlock, out var immediateDominator))
      {
        blockAssignments[currentBlock] = null;
      } 
      else if (splitsPerBlock.TryGetValue(immediateDominator, out var splitsForDominator)) // if the currentBlock's dominator has a split then it will be associated with that split
      {
        blockAssignments[currentBlock] = splitsForDominator.Last();
      } 
      else {
        Contract.Assert(blockAssignments.Keys.Contains(immediateDominator));
        blockAssignments[currentBlock] = blockAssignments[immediateDominator];
      }
      
      if (currentBlock.TransferCmd is GotoCmd gotoCmd) {
        gotoCmd.LabelTargets.ForEach(block => todo.Push(block));
      }
    }
    return blockAssignments;
  }
  
  private static ManualSplit? GetImplementationPartAfterSplit(Func<ImplementationPartOrigin, List<Block>, ManualSplit> createVc, 
    ManualSplit partToSplit, 
    Dictionary<Block, Cmd?> blockStartToSplit, Block blockWithSplit, 
    HashSet<Cmd> splits, Cmd? split) 
  {
    var assertionCount = 0;
    
    var newBlocks = UpdateBlocks(partToSplit.Implementation.Blocks, currentBlock => {
      if (currentBlock == blockWithSplit) {
        return GetCommandsForBlockWithSplit(currentBlock);
      }

      if (blockStartToSplit[currentBlock] == split) {
        return GetCommandsForBlockImmediatelyDominatedBySplit(currentBlock);
      }

      return currentBlock.Cmds.Select(x => CommandTransformations.AssertIntoAssume(partToSplit.Options, x)).ToList();
    });

    if (assertionCount == 0) {
      return null;
    }

    var partToken = split == null ? partToSplit.Origin : new SplitOrigin(false, split.tok, blockWithSplit, partToSplit.Origin);
    return createVc(partToken, newBlocks);

    List<Cmd> GetCommandsForBlockImmediatelyDominatedBySplit(Block currentBlock)
    {
      var verify = true;
      var newCmds = new List<Cmd>();
      foreach (var command in currentBlock.Cmds) {
        verify &= !splits.Contains(command);
        if (verify && BlockTransformations.IsNonTrivialAssert(command))
        {
          assertionCount++;
        }
        newCmds.Add(verify ? command : CommandTransformations.AssertIntoAssume(partToSplit.Options, command));
      }

      return newCmds;
    }

    List<Cmd> GetCommandsForBlockWithSplit(Block currentBlock)
    {
      var newCmds = new List<Cmd>();
      var verify = false;
      foreach (var command in currentBlock.Cmds) {
        if (splits.Contains(command)) {
          verify = command == split;
        }

        if (verify && BlockTransformations.IsNonTrivialAssert(command))
        {
          assertionCount++;
        }
        newCmds.Add(verify ? command : CommandTransformations.AssertIntoAssume(partToSplit.Options, command));
      }

      return newCmds;
    }
  }

  public static void AddJumpsToNewBlocks(Dictionary<Block, Block> oldToNewBlockMap)
  {
    foreach (var (oldBlock, newBlock) in oldToNewBlockMap) {
      if (oldBlock.TransferCmd is ReturnCmd returnCmd) {
        ((ReturnCmd)newBlock.TransferCmd).tok = returnCmd.tok;
        continue;
      }

      var gotoCmd = (GotoCmd)oldBlock.TransferCmd;
      var newLabelTargets = new List<Block>(gotoCmd.LabelTargets.Count);
      var newLabelNames = new List<string>(gotoCmd.LabelTargets.Count);
      foreach (var target in gotoCmd.LabelTargets) {
        newLabelTargets.Add(oldToNewBlockMap[target]);
        newLabelNames.Add(oldToNewBlockMap[target].Label);
      }

      oldToNewBlockMap[oldBlock].TransferCmd = new GotoCmd(gotoCmd.tok, newLabelNames, newLabelTargets);
    }
  }
}

public interface ImplementationPartOrigin : IToken {
}

public class SplitOrigin : TokenWrapper, ImplementationPartOrigin {
  public bool Implicit { get; }
  public Block ContainingBlock { get; }
  public ImplementationPartOrigin PartThatWasSplit { get; }

  public SplitOrigin(bool @implicit, IToken split, Block containingBlock, ImplementationPartOrigin partThatWasSplit) : base(split) {
    Implicit = @implicit;
    ContainingBlock = containingBlock;
    PartThatWasSplit = partThatWasSplit;
  }

  public string KindName => Implicit ? "assertion" : "split";
}