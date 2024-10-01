#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using VC;
using VCGeneration.Splits;

namespace VCGeneration;

class IsolateAttributeOnAsserts {
  private readonly Dictionary<AssertCmd, Cmd> assumedAssertions = new();
  private readonly VCGenOptions options;

  public IsolateAttributeOnAsserts(VCGenOptions options) {
    this.options = options;
  }

  private Cmd TransformAssertCmd(Cmd cmd) {
    if (cmd is AssertCmd assertCmd) {
      return assumedAssertions.GetOrCreate(assertCmd, () => VerificationConditionGenerator.AssertTurnedIntoAssume(options, assertCmd));
    }

    return cmd;
  }

  public List<ManualSplit> GetPartsFromIsolatedAssertions(ManualSplit partToDivide,
    Func<ImplementationPartOrigin, List<Block>, ManualSplit> createSplit) {
    
    var splitOnEveryAssert = partToDivide.Options.VcsSplitOnEveryAssert;
    partToDivide.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);
    
    var isolatedAssertions = new HashSet<AssertCmd>();
    var results = new List<ManualSplit>();
    var dag = Program.GraphFromBlocks(partToDivide.Blocks);
    
    foreach (var block in partToDivide.Blocks) {
      foreach (var assert in block.Cmds.OfType<AssertCmd>()) {
        var attributes = assert.Attributes;
        var isolateAttribute = QKeyValue.FindAttribute(attributes, p => p.Key == "isolate");
        if (!ShouldIsolate(splitOnEveryAssert, isolateAttribute)) {
          continue;
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
              new GotoCmd(gotoCmd.tok, new List<string> { firstBlock.Label }, new List<Block>
                {
                  firstBlock
                });
          }
          blockToVisit.Push(path.Push(newPrevious));
        }
      }
    }

    ManualSplit GetSplitForIsolatedAssertion(Block blockWithAssert, AssertCmd assertCmd) {
      var blocksToVisit = new Stack<Block>(new[] { blockWithAssert });
      var orderedNewBlocks = BlockRewriter.UpdateBlocks(blocksToVisit, 
        new HashSet<Block>(), 
        oldBlock => oldBlock == blockWithAssert
        ? GetCommandsForBlockWithAssert(oldBlock, assertCmd)
        : oldBlock.Cmds.Select(TransformAssertCmd).ToList());
      return createSplit(new IsolatedAssertionOrigin(assertCmd), orderedNewBlocks.Values.OrderBy(b => b.tok).ToList());
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

      var newBlocks = ManualSplitFinder.UpdateBlocks(partToDivide.Blocks, 
        block => block.Cmds.Select(cmd => isolatedAssertions.Contains(cmd) ? TransformAssertCmd(cmd) : cmd).ToList());
      return createSplit(origin, newBlocks);
    }
  }

  private static bool ShouldIsolate(bool splitOnEveryAssert, QKeyValue? isolateAttribute) {
    if (splitOnEveryAssert) {
      if (isolateAttribute == null) {
        return true;
      }

      return !isolateAttribute.Params.OfType<string>().Any(p => Equals(p, "none"));
    }

    return isolateAttribute != null;
  }
}


public class IsolatedAssertionOrigin : TokenWrapper, ImplementationPartOrigin {
  public AssertCmd IsolatedAssert { get; }

  public IsolatedAssertionOrigin(AssertCmd isolatedAssert) : base(isolatedAssert.tok) {
    this.IsolatedAssert = isolatedAssert;
  }
}