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
  public static (List<ManualSplit> Isolated, ManualSplit Remainder) GetParts(VCGenOptions options, ManualSplit partToDivide, 
    Func<IImplementationPartOrigin, List<Block>, ManualSplit> createPart) {

    var rewriter = new BlockRewriter(options, partToDivide.Blocks, createPart);
    
    var results = new List<ManualSplit>();
    var blocks = partToDivide.Blocks;
    var dag = Program.GraphFromBlocks(blocks);
    
    var splitOnEveryAssert = partToDivide.Options.VcsSplitOnEveryAssert;
    partToDivide.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);

    var isolatedBlockJumps = new HashSet<Block>();
    
    foreach (var block in partToDivide.Blocks) {
      if (block.TransferCmd is not GotoCmd gotoCmd) {
        continue;
      }

      var isTypeOfAssert = gotoCmd.tok is GotoFromReturn;
      var isolateAttribute = QKeyValue.FindAttribute(gotoCmd.Attributes, p => p.Key == "isolate");
      var isolate = BlockRewriter.ShouldIsolate(isTypeOfAssert && splitOnEveryAssert, isolateAttribute);
      if (!isolate) {
        continue;
      }

      isolatedBlockJumps.Add(block);
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
        var newBlocks = rewriter.ComputeNewBlocks(blocksToInclude, ancestors.ToHashSet());
        results.Add(rewriter.CreateSplit(new ReturnOrigin(originalReturn), newBlocks));
      }
    }

    if (!results.Any()) {
      return (results,partToDivide);
    }

    return (results, GetPartWithoutIsolatedReturns());
    
    ManualSplit GetPartWithoutIsolatedReturns() {
      var newBlocks = rewriter.ComputeNewBlocks(blocks.ToHashSet(), (oldBlock, newBlock) => {
        if (isolatedBlockJumps.Contains(oldBlock)) {
          newBlock.TransferCmd = new ReturnCmd(Token.NoToken);
        }
      });
      return rewriter.CreateSplit(new ImplementationRootOrigin(partToDivide.Implementation), 
        newBlocks);
    }
  }
}


public class ReturnOrigin : TokenWrapper, IImplementationPartOrigin {
  public ReturnCmd IsolatedReturn { get; }

  public ReturnOrigin(ReturnCmd isolatedReturn) : base(isolatedReturn.tok) {
    this.IsolatedReturn = isolatedReturn;
  }

  public string ShortName => $"/return@{IsolatedReturn.Line}";
}