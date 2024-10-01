#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using VC;
using VCGeneration.Splits;

namespace VCGeneration;

class IsolateAttributeOnAssertsHandler {
  private readonly BlockRewriter rewriter;

  public IsolateAttributeOnAssertsHandler(BlockRewriter rewriter) {
    this.rewriter = rewriter;
  }

  public (List<ManualSplit> IsolatedParts, ManualSplit Remainder) GetParts(ManualSplit partToDivide) {
    
    var splitOnEveryAssert = partToDivide.Options.VcsSplitOnEveryAssert;
    partToDivide.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);
    
    var isolatedAssertions = new HashSet<AssertCmd>();
    var results = new List<ManualSplit>();
    
    foreach (var block in partToDivide.Blocks) {
      foreach (var assert in block.Cmds.OfType<AssertCmd>()) {
        var attributes = assert.Attributes;
        var isolateAttribute = QKeyValue.FindAttribute(attributes, p => p.Key == "isolate");
        if (!ShouldIsolate(splitOnEveryAssert, isolateAttribute)) {
          continue;
        }

        isolatedAssertions.Add(assert);
        if (isolateAttribute != null && isolateAttribute.Params.OfType<string>().Any(p => Equals(p, "paths"))) {
          results.AddRange(rewriter.GetSplitsForIsolatedPaths(block, null, assert.tok).Select(p => {
            var newAssertBlock = p.Blocks.Last();
            newAssertBlock.Cmds = GetCommandsForBlockWithAssert(newAssertBlock, assert);
            return p;
          }));
        } else {
          results.Add(GetSplitForIsolatedAssertion(block, assert));
        }
      }
    }

    return (results,GetSplitWithoutIsolatedAssertions());


    ManualSplit GetSplitForIsolatedAssertion(Block blockWithAssert, AssertCmd assertCmd) {
      var blocksToVisit = new Stack<Block>(new[] { blockWithAssert });
      var orderedNewBlocks = BlockRewriter.UpdateBlocks(blocksToVisit, 
        new HashSet<Block>(), 
        oldBlock => oldBlock == blockWithAssert
        ? GetCommandsForBlockWithAssert(oldBlock, assertCmd)
        : oldBlock.Cmds.Select(rewriter.TransformAssertCmd).ToList());
      return rewriter.CreateSplit(new IsolatedAssertionOrigin(assertCmd), orderedNewBlocks.Values.OrderBy(b => b.tok).ToList());
    }
    
    List<Cmd> GetCommandsForBlockWithAssert(Block currentBlock, AssertCmd assert)
    {
      var result = new List<Cmd>();
      foreach (var command in currentBlock.Cmds) {
        if (assert == command) {
          result.Add(command);
          break;
        }
        result.Add(rewriter.TransformAssertCmd(command));
      }

      return result;
    }

    ManualSplit GetSplitWithoutIsolatedAssertions() {
      var origin = new ImplementationRootOrigin(partToDivide.Implementation);
      if (!isolatedAssertions.Any()) {
        return rewriter.CreateSplit(origin, partToDivide.Blocks);
      }

      var newBlocks = ManualSplitFinder.UpdateBlocks(partToDivide.Blocks, 
        block => block.Cmds.Select(cmd => isolatedAssertions.Contains(cmd) ? rewriter.TransformAssertCmd(cmd) : cmd).ToList());
      return rewriter.CreateSplit(origin, newBlocks);
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