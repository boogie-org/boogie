#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using VC;

namespace VCGeneration;

static class IsolateAttributeHandler {
  public static List<ManualSplit> GetPartsFromIsolatedAssertions(VCGenOptions options, ManualSplit partToDivide,
    Func<ImplementationPartOrigin, List<Block>, ManualSplit> createSplit) {
    
    var splitOnEveryAssert = partToDivide.Options.VcsSplitOnEveryAssert;
    partToDivide.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);
    
    var isolatedAssertions = new HashSet<AssertCmd>();
    var results = new List<ManualSplit>();
    var dag = Program.GraphFromBlocks(partToDivide.Blocks);
    
    var assumedAssertions = new Dictionary<AssertCmd, Cmd>();
    foreach (var block in partToDivide.Blocks) {
      foreach (var assert in block.Cmds.OfType<AssertCmd>()) {
        var isolateAttribute = QKeyValue.FindAttribute(assert.Attributes, p => p.Key == "isolate");
        if (splitOnEveryAssert) {
          if (isolateAttribute != null) {
            if (isolateAttribute.Params.OfType<string>().Any(p => Equals(p, "none"))) {
              continue;
            }
            // isolate
          }
          // isolate
        } else {
          if (isolateAttribute == null) {
            continue;
          }
          // isolate
        }

        isolatedAssertions.Add(assert);
        if (isolateAttribute != null && isolateAttribute.Params.OfType<string>().Any(p => Equals(p, "paths"))) {
          results.AddRange(GetSplitsForIsolatedPathAssertion(block, assert));
        } else {
          results.Add(GetSplitForIsolatedAssertion(block, assert));
        }
      }
    }

    results.Add(GetSplitWithoutIsolatedAssertions());

    return results;

    Cmd TransformAssertCmd(Cmd cmd) {
      if (cmd is AssertCmd assertCmd) {
        return assumedAssertions.GetOrCreate(assertCmd, () => VerificationConditionGenerator.AssertTurnedIntoAssume(options, assertCmd));
      }

      return cmd;
    }

    IEnumerable<ManualSplit> GetSplitsForIsolatedPathAssertion(Block blockWithAssert, AssertCmd assertCmd) {
      var blockToVisit = new Stack<ImmutableStack<Block>>();
      blockToVisit.Push(ImmutableStack.Create(new Block(blockWithAssert.tok)
      {
        Predecessors = blockWithAssert.Predecessors,
        Label = blockWithAssert.Label,
        TransferCmd = new GotoCmd(Token.NoToken, new List<string>(), new List<Block>()),
        Cmds = GetCommandsForBlockWithAssert(blockWithAssert, assertCmd)
      }));
      while(blockToVisit.Any()) {
        var path = blockToVisit.Pop();
        var firstBlock = path.Peek();
        if (!firstBlock.Predecessors.Any()) {
          yield return createSplit(new PathOrigin(assertCmd.tok, path, dag.DominatorMap), new List<Block>() { new(firstBlock.tok) {
            Label = firstBlock.Label,
            Cmds = path.SelectMany(b => b.Cmds).ToList() 
          } });
        }
        foreach (var oldPrevious in firstBlock.Predecessors) {
          var newPrevious = new Block(oldPrevious.tok)
          {
            Predecessors = oldPrevious.Predecessors,
            Label = oldPrevious.Label,
            TransferCmd = oldPrevious.TransferCmd,
            Cmds = oldPrevious.Cmds.Select(TransformAssertCmd).ToList()
          };
          if (newPrevious.TransferCmd is GotoCmd gotoCmd) {
            newPrevious.TransferCmd =
              new GotoCmd(gotoCmd.tok, new List<string>() { firstBlock.Label }, new List<Block>
                {
                  firstBlock
                });
          }
          blockToVisit.Push(path.Push(newPrevious));
        }
      }
    }

    ManualSplit GetSplitForIsolatedAssertion(Block blockWithAssert, AssertCmd assertCmd) {
      var newBlocks = new List<Block>();
      var oldToNewBlockMap = new Dictionary<Block, Block>();
      var blockToVisit = new Stack<Block>();
      blockToVisit.Push(blockWithAssert);
      var visitedBlocks = new HashSet<Block>();
      while(blockToVisit.Any()) {
        var oldBlock = blockToVisit.Pop();
        if (!visitedBlocks.Add(oldBlock)) {
          continue;
        }
        
        var newBlock = new Block(oldBlock.tok)
        {
          Label = oldBlock.Label,
          TransferCmd = oldBlock.TransferCmd
        };
        oldToNewBlockMap[oldBlock] = newBlock;

        newBlocks.Add(newBlock);
        newBlock.Cmds = oldBlock == blockWithAssert
          ? GetCommandsForBlockWithAssert(oldBlock, assertCmd)
          : oldBlock.Cmds.Select(TransformAssertCmd).ToList();
        foreach (var previous in oldBlock.Predecessors) {
          blockToVisit.Push(previous);
        }
        
        if (newBlock.TransferCmd is GotoCmd gtc)
        {
          var targets = gtc.LabelTargets.Where(oldToNewBlockMap.ContainsKey).ToList();
          newBlock.TransferCmd = new GotoCmd(gtc.tok,
            targets.Select(block => oldToNewBlockMap[block].Label).ToList(),
            targets.Select(block => oldToNewBlockMap[block]).ToList());
        }
      }

      return createSplit(new IsolatedAssertionOrigin(assertCmd), newBlocks.OrderBy(b => b.tok).ToList());
    }
    
    List<Cmd> GetCommandsForBlockWithAssert(Block currentBlock, AssertCmd assert)
    {
      var result = new List<Cmd>();
      foreach (var command in currentBlock.Cmds) {
        if (assert == command) {
          result.Add(command);
          break;
        }
        result.Add(TransformAssertCmd(command));
      }

      return result;
    }

    ManualSplit GetSplitWithoutIsolatedAssertions() {
      var origin = new ImplementationRootOrigin(partToDivide.Implementation);
      if (!isolatedAssertions.Any()) {
        return createSplit(origin, partToDivide.Blocks);
      }

      // TODO don't copy list if it is unchanged.
      var newBlocks = ManualSplitFinder.UpdateBlocks(partToDivide.Blocks, 
        block => block.Cmds.Select(cmd => {
          if (isolatedAssertions.Contains(cmd)) {
            return TransformAssertCmd(cmd);
          }

          return cmd;
        }).ToList());
      return createSplit(origin, newBlocks);
    }
  }
}


public class IsolatedAssertionOrigin : TokenWrapper, ImplementationPartOrigin {
  public AssertCmd IsolatedAssert { get; }

  public IsolatedAssertionOrigin(AssertCmd isolatedAssert) : base(isolatedAssert.tok) {
    this.IsolatedAssert = isolatedAssert;
  }
}