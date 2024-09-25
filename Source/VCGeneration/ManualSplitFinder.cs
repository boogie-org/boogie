#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.CSharp.RuntimeBinder;
using VC;

namespace VCGeneration;

static class HashCodeExtensions {
  internal static int GetHashCodeByItems<T>(this IEnumerable<T> lst)
  {
    unchecked
    {
      int hash = 19;
      foreach (T item in lst)
      {
        hash = hash * 31 + (item != null ? item.GetHashCode() : 1);
      }
      return hash;
    }
  }
}

public static class ManualSplitFinder {
  public static IEnumerable<ManualSplit> SplitOnPathsAndAssertions(VCGenOptions options, ImplementationRun run, 
    Func<IToken, List<Block>, ManualSplit> createSplit) {
    var paths = options.IsolatePaths || QKeyValue.FindBoolAttribute(run.Implementation.Attributes, "isolate_paths") 
      ? IsolatedPathSplits(options, run, createSplit) 
      : FocusAttribute.SplitOnFocus(options, run, createSplit);
    return paths.SelectMany(SplitOnAssertions);
  }

  class PathBlocksComparer : IEqualityComparer<PathBlocks> {

    public PathBlocksComparer() {
    }

    public bool Equals(PathBlocks? x, PathBlocks? y) {
      if (x == null || y == null) {
        return x == y;
      }

      return x.TransferCmd == y.TransferCmd && x.Commands.SequenceEqual(y.Commands);
    }

    public int GetHashCode(PathBlocks obj) {
      return HashCode.Combine(obj.TransferCmd.GetHashCode(), obj.Commands.GetHashCodeByItems());
    }
  }

  record PathBlocks(ImmutableStack<Cmd> Assumed, ImmutableStack<Cmd> UnAssumed, TransferCmd TransferCmd) {
    public IEnumerable<Cmd> Commands => UnAssumed.Concat(Assumed);
  }

  private static List<ManualSplit> IsolatedPathSplits(VCGenOptions options, ImplementationRun run,
    Func<IToken, List<Block>, ManualSplit> createSplit) {
    var comparer = new PathBlocksComparer();
    var visitedPathBlocks = new HashSet<PathBlocks>(comparer);
    
    var result = new List<ManualSplit>();
    var firstBlock = run.Implementation.Blocks[0];
    var paths = new Stack<PathBlocks>();
    paths.Push(new PathBlocks(ImmutableStack<Cmd>.Empty, ImmutableStack.CreateRange(firstBlock.Cmds), firstBlock.TransferCmd));
    while (paths.Any())
    {
      var current = paths.Pop();
      // if (!visitedPathBlocks.Add(current)) {
      //   continue;
      // }
      
      if (current.TransferCmd is not GotoCmd gotoCmd || !gotoCmd.labelTargets.Any())
      {
        var masterBlock = new Block(firstBlock.tok)
        {
          Label = firstBlock.Label,
          Cmds = current.UnAssumed.Concat(current.Assumed).Reverse().ToList(),
          TransferCmd = current.TransferCmd
        };
        result.Add(createSplit(run.Implementation.tok, new List<Block> { masterBlock }));
        continue;
      }

      var firstTarget = gotoCmd.labelTargets.First();

      paths.Push(current with { UnAssumed = PushRange(firstTarget.Cmds, current.UnAssumed), TransferCmd = firstTarget.TransferCmd });
      
      if (gotoCmd.labelTargets.Count <= 1) {
        continue;
      }

      var assumed = PushRange(current.UnAssumed.ToList(), current.Assumed);
      foreach (var target in gotoCmd.labelTargets.Skip(1))
      {
        paths.Push(new PathBlocks(assumed, ImmutableStack.CreateRange(target.Cmds), target.TransferCmd));
      }

    }

    return result;
  }

  private static ImmutableStack<T> PushRange<T>(IReadOnlyList<T> newElements, ImmutableStack<T> stack) {
    for (var i = newElements.Count - 1; i >= 0; i--) {
      stack = stack.Push(newElements[i]);
    }

    return stack;
  }
  
  private static List<ManualSplit> SplitOnAssertions(ManualSplit initialSplit) {

    var splitOnEveryAssert = initialSplit.Options.VcsSplitOnEveryAssert;
    initialSplit.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);

    var splitPoints = new Dictionary<Block, List<IToken>>();
    foreach (var block in initialSplit.Blocks) {
      foreach (Cmd command in block.Cmds) {
        if (ShouldSplitHere(command, splitOnEveryAssert)) {
          splitPoints.GetOrCreate(block, () => new List<IToken>()).Add(command.tok);
        }
      }
    }
    var splits = new List<ManualSplit>();
    if (!splitPoints.Any()) {
      splits.Add(initialSplit);
    } else {
      Block entryPoint = initialSplit.Blocks[0];
      var blockAssignments = PickBlocksToVerify(initialSplit.Blocks, splitPoints);
      var entryBlockHasSplit = splitPoints.ContainsKey(entryPoint);
      var firstSplitBlocks = DoPreAssignedManualSplit(initialSplit.Options, initialSplit.Blocks, blockAssignments,
        -1, entryPoint, !entryBlockHasSplit, splitOnEveryAssert);
      if (firstSplitBlocks != null)
      {
        splits.Add(new ManualSplit(initialSplit.Options, () => {
          BlockTransformations.Optimize(firstSplitBlocks);
          return firstSplitBlocks;
        }, initialSplit.GotoCmdOrigins, initialSplit.parent, initialSplit.Run, initialSplit.Token));
      }
      foreach (var block in initialSplit.Blocks) {
        var tokens = splitPoints.GetValueOrDefault(block);
        if (tokens == null) {
          continue;
        }
        
        for (int i = 0; i < tokens.Count; i++) {
          var token = tokens[i];
          bool lastSplitInBlock = i == tokens.Count - 1;
          var newBlocks = DoPreAssignedManualSplit(initialSplit.Options, initialSplit.Blocks, blockAssignments, i, block, lastSplitInBlock, splitOnEveryAssert);
          if (newBlocks != null)
          {
            splits.Add(new ManualSplit(initialSplit.Options, 
              () => {
                BlockTransformations.Optimize(newBlocks);
                return newBlocks;
              }, initialSplit.GotoCmdOrigins, initialSplit.parent, initialSplit.Run, token));
          }
        }
      }
    }
    return splits;
  }

  private static bool ShouldSplitHere(Cmd c, bool splitOnEveryAssert) {
    return c is PredicateCmd p && QKeyValue.FindBoolAttribute(p.Attributes, "split_here")
           || c is AssertCmd && splitOnEveryAssert;
  }

  // Verify b with the last split in blockAssignments[b]
  private static Dictionary<Block, Block> PickBlocksToVerify(List<Block> blocks, Dictionary<Block, List<IToken>> splitPoints) {
    var todo = new Stack<Block>();
    var blockAssignments = new Dictionary<Block, Block>();
    var immediateDominator = Program.GraphFromBlocks(blocks).ImmediateDominator();
    todo.Push(blocks[0]);
    while (todo.Count > 0) {
      var currentBlock = todo.Pop();
      if (blockAssignments.Keys.Contains(currentBlock)) {
        continue;
      }

      if (immediateDominator[currentBlock] == currentBlock) // if the currentBlock doesn't have a predecessor.
      {
        blockAssignments[currentBlock] = currentBlock;
      } else if (splitPoints.ContainsKey(immediateDominator[currentBlock])) // if the currentBlock's dominator has a split then it will be associated with that split
      {
        blockAssignments[currentBlock] = immediateDominator[currentBlock];
      } else {
        Contract.Assert(blockAssignments.Keys.Contains(immediateDominator[currentBlock]));
        blockAssignments[currentBlock] = blockAssignments[immediateDominator[currentBlock]];
      }
      if (currentBlock.TransferCmd is GotoCmd exit) {
        exit.labelTargets.ForEach(blk => todo.Push(blk));
      }
    }
    return blockAssignments;
  }
  
  private static List<Block>? DoPreAssignedManualSplit(VCGenOptions options, List<Block> blocks, 
    Dictionary<Block, Block> blockAssignments, int splitNumberWithinBlock,
    Block containingBlock, bool lastSplitInBlock, bool splitOnEveryAssert) {
    var newBlocks = new List<Block>(blocks.Count); // Copies of the original blocks
    //var duplicator = new Duplicator();
    var assertionCount = 0;
    var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count); // Maps original blocks to their new copies in newBlocks
    foreach (var currentBlock in blocks) {
      var newBlock = new Block(currentBlock.tok)
      {
        Label = currentBlock.Label
      };

      oldToNewBlockMap[currentBlock] = newBlock;
      newBlocks.Add(newBlock);
      if (currentBlock == containingBlock) {
        var newCmds = new List<Cmd>();
        var splitCount = -1;
        var verify = splitCount == splitNumberWithinBlock;
        foreach (Cmd command in currentBlock.Cmds) {
          if (ShouldSplitHere(command, splitOnEveryAssert)) {
            splitCount++;
            verify = splitCount == splitNumberWithinBlock;
          }

          if (verify && BlockTransformations.IsNonTrivialAssert(command))
          {
            assertionCount++;
          }
          newCmds.Add(verify ? command : CommandTransformations.AssertIntoAssume(options, command));
        }
        newBlock.Cmds = newCmds;
      } else if (lastSplitInBlock && blockAssignments[currentBlock] == containingBlock) {
        var verify = true;
        var newCmds = new List<Cmd>();
        foreach (var command in currentBlock.Cmds) {
          verify = !ShouldSplitHere(command, splitOnEveryAssert) && verify;
          if (verify && BlockTransformations.IsNonTrivialAssert(command))
          {
            assertionCount++;
          }
          newCmds.Add(verify ? command : CommandTransformations.AssertIntoAssume(options, command));
        }
        newBlock.Cmds = newCmds;
      } else {
        newBlock.Cmds = currentBlock.Cmds.Select(x => CommandTransformations.AssertIntoAssume(options, x)).ToList();
      }
    }

    if (assertionCount == 0)
    {
      return null;
    }
    
    // Patch the edges between the new blocks
    AddBlockJumps(blocks, oldToNewBlockMap);
    return newBlocks;
  }

  private static void AddBlockJumps(List<Block> oldBlocks, Dictionary<Block, Block> oldToNewBlockMap)
  {
    foreach (var oldBlock in oldBlocks) {
      var newBlock = oldToNewBlockMap[oldBlock];
      if (oldBlock.TransferCmd is ReturnCmd returnCmd) {
        ((ReturnCmd)newBlock.TransferCmd).tok = returnCmd.tok;
        continue;
      }

      var gotoCmd = (GotoCmd)oldBlock.TransferCmd;
      var newLabelTargets = new List<Block>(gotoCmd.labelTargets.Count());
      var newLabelNames = new List<string>(gotoCmd.labelTargets.Count());
      foreach (var target in gotoCmd.labelTargets) {
        newLabelTargets.Add(oldToNewBlockMap[target]);
        newLabelNames.Add(oldToNewBlockMap[target].Label);
      }

      oldToNewBlockMap[oldBlock].TransferCmd = new GotoCmd(gotoCmd.tok, newLabelNames, newLabelTargets);
    }
  }
}