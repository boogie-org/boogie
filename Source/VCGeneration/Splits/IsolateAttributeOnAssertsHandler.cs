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
          var origin = new IsolatedAssertionOrigin(new ImplementationRootOrigin(partToDivide.Implementation), assert);
          results.AddRange(rewriter.GetSplitsForIsolatedPaths(block, rewriter.OrderedBlocks.ToHashSet(), origin).Select(p => {
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

    var remainder = GetSplitWithoutIsolatedAssertions();
    return (results,remainder);

    ManualSplit GetSplitForIsolatedAssertion(Block blockWithAssert, AssertCmd assertCmd) {
      var blocksToKeep = rewriter.Dag.ComputeReachability(blockWithAssert, false);

      List<Cmd> GetCommands(Block oldBlock) =>
        oldBlock == blockWithAssert
          ? GetCommandsForBlockWithAssert(oldBlock, assertCmd)
          : oldBlock.Cmds.Select(rewriter.TransformAssertCmd).ToList();

      var newBlocks = rewriter.ComputeNewBlocks(blocksToKeep, (oldBlock, newBlock) => newBlock.Cmds = GetCommands(oldBlock));
      return rewriter.CreateSplit(new IsolatedAssertionOrigin(partToDivide.Token, assertCmd), newBlocks);
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
      if (!isolatedAssertions.Any()) {
        return rewriter.CreateSplit(new RemainingAssertionsOrigin(partToDivide.Token), partToDivide.Blocks);
      }

      var newBlocks = rewriter.ComputeNewBlocks(null, (oldBlock, newBlock) => newBlock.Cmds = GetCommands(oldBlock));
      return rewriter.CreateSplit(partToDivide.Token, newBlocks);

      List<Cmd> GetCommands(Block block) => block.Cmds.Select(cmd => 
        isolatedAssertions.Contains(cmd) ? rewriter.TransformAssertCmd(cmd) : cmd).ToList();
    }
  }
}

public class IsolatedAssertionOrigin : TokenWrapper, IImplementationPartOrigin {
  public IImplementationPartOrigin Origin { get; }
  public AssertCmd IsolatedAssert { get; }

  public IsolatedAssertionOrigin(IImplementationPartOrigin origin, AssertCmd isolatedAssert) : base(isolatedAssert.tok) {
    Origin = origin;
    this.IsolatedAssert = isolatedAssert;
  }

  public string ShortName => $"{Origin.ShortName}/assert@{IsolatedAssert.Line}";
}