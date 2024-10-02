#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie;
using VC;
using VCGeneration.Splits;
using VCGeneration.Transformations;

namespace VCGeneration;

class IsolateAttributeOnJumpsHandler {
  private readonly BlockRewriter rewriter;

  public IsolateAttributeOnJumpsHandler(BlockRewriter rewriter) {
    this.rewriter = rewriter;
  }
  
  public (List<ManualSplit> Isolated, ManualSplit Remainder) GetParts(
    ManualSplit partToDivide) {

    var results = new List<ManualSplit>();
    var blocks = partToDivide.Blocks;
    var dag = Program.GraphFromBlocks(blocks);
    var topoSorted = dag.TopologicalSort();
    var reversedBlocks = topoSorted.Reversed();
    
    var splitOnEveryAssert = partToDivide.Options.VcsSplitOnEveryAssert;
    partToDivide.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);

    var isolatedBlocks = new HashSet<Block>();
    
    foreach (var block in partToDivide.Blocks) {
      if (block.TransferCmd is not GotoCmd gotoCmd) {
        continue;
      }

      var isTypeOfAssert = gotoCmd.tok is GotoFromReturn;
      var isolateAttribute = QKeyValue.FindAttribute(gotoCmd.Attributes, p => p.Key == "isolate");
      var isolate = ShouldIsolate(isTypeOfAssert && splitOnEveryAssert, isolateAttribute);
      if (!isolate) {
        continue;
      }

      isolatedBlocks.Add(block);
      var ancestors = dag.ComputeReachability(block, false);
      var descendants = dag.ComputeReachability(block, true);
      var blocksToInclude = ancestors.Union(descendants).ToHashSet();

      var originalReturn = ((GotoFromReturn)gotoCmd.tok).Origin;
      if (isolateAttribute != null && isolateAttribute.Params.OfType<string>().Any(p => Equals(p, "paths"))) {
        // These conditions hold if the goto was originally a return
        Debug.Assert(gotoCmd.LabelTargets.Count == 1);
        Debug.Assert(gotoCmd.LabelTargets[0].TransferCmd is not GotoCmd);
        results.AddRange(rewriter.GetSplitsForIsolatedPaths(gotoCmd.LabelTargets[0], blocksToInclude, originalReturn.tok));
      } else {
        var (newBlocks, _) = rewriter.ComputeNewBlocks(blocksToInclude,
          reversedBlocks, ancestors.ToHashSet());
        results.Add(rewriter.CreateSplit(new ReturnOrigin(originalReturn), newBlocks));
      }
    }

    return (results, GetPartWithoutIsolatedReturns());
    
    ManualSplit GetPartWithoutIsolatedReturns() {
      // TODO this needs an extra test. In case the isolated jump is followed by something it dominates
      var (newBlocks, mapping) = rewriter.ComputeNewBlocks(blocks.ToHashSet(), reversedBlocks, new HashSet<Block>());
      foreach (var (oldBlock, newBlock) in mapping) {
        if (isolatedBlocks.Contains(oldBlock)) {
          newBlock.TransferCmd = new ReturnCmd(Token.NoToken);
        }
      }
      BlockTransformations.DeleteBlocksNotLeadingToAssertions(newBlocks);
      return rewriter.CreateSplit(new ImplementationRootOrigin(partToDivide.Implementation), 
        newBlocks);
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


public class ReturnOrigin : TokenWrapper, ImplementationPartOrigin {
  public ReturnCmd IsolatedReturn { get; }

  public ReturnOrigin(ReturnCmd isolatedReturn) : base(isolatedReturn.tok) {
    this.IsolatedReturn = isolatedReturn;
  }

  public string ShortName => $"/return@{IsolatedReturn.Line}";
}