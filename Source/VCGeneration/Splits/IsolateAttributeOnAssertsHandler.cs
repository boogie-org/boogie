#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using VC;
using VCGeneration.Splits;

namespace VCGeneration;

class IsolateAttributeOnAssertsHandler {

  public static (List<ManualSplit> IsolatedParts, ManualSplit Remainder) GetParts(VCGenOptions options, ManualSplit partToDivide, 
    Func<IImplementationPartOrigin, IList<Block>, ManualSplit> createPart) {
    var rewriter = new BlockRewriter(options, partToDivide.Blocks, createPart);
      
    var splitOnEveryAssert = partToDivide.Options.VcsSplitOnEveryAssert;
    partToDivide.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);
    
    var isolatedAssertions = new HashSet<AssertCmd>();
    var results = new List<ManualSplit>();

    foreach (var b in partToDivide.Blocks) {
      b.Predecessors.Clear();
    }
    Implementation.ComputePredecessorsForBlocks(partToDivide.Blocks);
    foreach (var block in partToDivide.Blocks) {
      foreach (var assert in block.Cmds.OfType<AssertCmd>()) {
        var attributes = assert.Attributes;
        var isolateAttribute = QKeyValue.FindAttribute(attributes, p => p.Key == "isolate");
        if (!BlockRewriter.ShouldIsolate(splitOnEveryAssert, isolateAttribute)) {
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

    if (!results.Any()) {
      return (results,partToDivide);
    }
    
    return (results,GetSplitWithoutIsolatedAssertions());

    ManualSplit GetSplitForIsolatedAssertion(Block blockWithAssert, AssertCmd assertCmd) {
      var blocksToKeep = rewriter.Dag.ComputeReachability(blockWithAssert, false);

      List<Cmd> GetCommands(Block oldBlock) =>
        oldBlock == blockWithAssert
          ? GetCommandsForBlockWithAssert(oldBlock, assertCmd)
          : oldBlock.Cmds.Select(rewriter.TransformAssertCmd).ToList();

      var newBlocks = rewriter.ComputeNewBlocks(blocksToKeep, (oldBlock, newBlock) => newBlock.Cmds = GetCommands(oldBlock));
      return rewriter.CreateSplit(new IsolatedAssertionOrigin(assertCmd), newBlocks);
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

      var newBlocks = rewriter.ComputeNewBlocks(null, (oldBlock, newBlock) => newBlock.Cmds = GetCommands(oldBlock));
      return rewriter.CreateSplit(origin, newBlocks);

      List<Cmd> GetCommands(Block block) => block.Cmds.Select(cmd => 
        isolatedAssertions.Contains(cmd) ? rewriter.TransformAssertCmd(cmd) : cmd).ToList();
    }
  }
}


public class IsolatedAssertionOrigin : TokenWrapper, IImplementationPartOrigin {
  public AssertCmd IsolatedAssert { get; }

  public IsolatedAssertionOrigin(AssertCmd isolatedAssert) : base(isolatedAssert.tok) {
    this.IsolatedAssert = isolatedAssert;
  }

  public string ShortName => $"/assert@{IsolatedAssert.Line}";
}