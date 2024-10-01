#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie;
using VC;
using VCGeneration.Splits;

namespace VCGeneration;

class IsolateAttributeOnJumpsHandler {
  private readonly BlockRewriter rewriter;

  public IsolateAttributeOnJumpsHandler(BlockRewriter rewriter) {
    this.rewriter = rewriter;
  }
  
  public (List<ManualSplit> Isolated, ManualSplit Remainder) GetParts( 
    Dictionary<TransferCmd, ReturnCmd> gotoToOriginalReturn, 
    ManualSplit partToDivide) {

    var results = new List<ManualSplit>();
    var blocks = partToDivide.Blocks;
    var dag = Program.GraphFromBlocks(blocks);
    var reversedBlocks = dag.TopologicalSort().Reversed();
    
    var splitOnEveryAssert = partToDivide.Options.VcsSplitOnEveryAssert;
    partToDivide.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);

    var isolatedBlocks = new HashSet<Block>();
    
    foreach (var block in partToDivide.Blocks) {
      if (block.TransferCmd is not GotoCmd gotoCmd) {
        continue;
      }

      var isTypeOfAssert = gotoToOriginalReturn.ContainsKey(gotoCmd);
      var isolateAttribute = QKeyValue.FindAttribute(gotoCmd.Attributes, p => p.Key == "isolate");
      var isolate = ShouldIsolate(isTypeOfAssert && splitOnEveryAssert, isolateAttribute);
      if (!isolate) {
        continue;
      }

      isolatedBlocks.Add(block);
      var ancestors = dag.ComputeReachability(block, false);
      var descendants = dag.ComputeReachability(block, true);
      var blocksToInclude = ancestors.Union(descendants).ToHashSet();

      if (isolateAttribute != null && isolateAttribute.Params.OfType<string>().Any(p => Equals(p, "paths"))) {
        // These conditions hold if the goto was originally a return
        Debug.Assert(gotoCmd.LabelTargets.Count == 1);
        Debug.Assert(gotoCmd.LabelTargets[0].TransferCmd is not GotoCmd);
        results.AddRange(rewriter.GetSplitsForIsolatedPaths(gotoCmd.LabelTargets[0], blocksToInclude, gotoToOriginalReturn[gotoCmd].tok));
      } else {
        var newBlocks = rewriter.ComputeNewBlocks(blocksToInclude,
          reversedBlocks, ancestors.ToHashSet());
        results.Add(createSplit(new ReturnOrigin(gotoToOriginalReturn[gotoCmd]), newBlocks));
      }

    }

    return (results, GetPartWithoutIsolatedReturns());
    
    ManualSplit GetPartWithoutIsolatedReturns() {
      var newBlocks = BlockRewriter.UpdateBlocks(new Stack<Block>(reversedBlocks), new HashSet<Block>(), 
        oldBlock => oldBlock.Cmds.Select(rewriter.TransformAssertCmd).ToList());
      foreach (var (oldBlock, newBlock) in newBlocks) {
        if (isolatedBlocks.Contains(oldBlock)) {
          newBlock.TransferCmd = null;
        }
      }
      return createSplit(new ImplementationRootOrigin(partToDivide.Implementation), newBlocks.Values.ToList());
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
}