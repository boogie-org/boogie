#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using VC;
using VCGeneration.Splits;

namespace VCGeneration;

class IsolateAttributeOnReturns {
  private readonly Dictionary<AssertCmd, Cmd> assumedAssertions = new();
  private readonly VCGenOptions options;

  public IsolateAttributeOnReturns(VCGenOptions options) {
    this.options = options;
  }

  private Cmd TransformAssertCmd(Cmd cmd) {
    if (cmd is AssertCmd assertCmd) {
      return assumedAssertions.GetOrCreate(assertCmd, () => VerificationConditionGenerator.AssertTurnedIntoAssume(options, assertCmd));
    }

    return cmd;
  }
  
  public List<ManualSplit> GetPartsFromIsolatedReturns( 
    Dictionary<TransferCmd, ReturnCmd> gotoToOriginalReturn, 
    ManualSplit partToDivide,
    Func<ImplementationPartOrigin, List<Block>, ManualSplit> createSplit) {

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

      if (!gotoToOriginalReturn.TryGetValue(gotoCmd, out var returnCmd)) {
        continue;
      }

      var isolateAttribute = QKeyValue.FindAttribute(returnCmd.Attributes, p => p.Key == "isolate");
      var isolate = ShouldIsolate(splitOnEveryAssert, isolateAttribute);
      if (!isolate) {
        continue;
      }

      // TODO support isolate paths for returns
      isolatedBlocks.Add(block);
      var ancestors = dag.ComputeReachability(block, false);
      var descendants = dag.ComputeReachability(block, true);
      var blocksToInclude = ancestors.Union(descendants).ToHashSet();
      var newBlocks = FocusApplier.ComputeNewBlocks(options, blocksToInclude,
        reversedBlocks, ancestors.ToHashSet());
      var partFromIsolatedReturn = createSplit(new ReturnOrigin(gotoToOriginalReturn[gotoCmd]), newBlocks);
      results.Add(partFromIsolatedReturn);
    }
    
    results.Add(GetPartWithoutIsolatedReturns());

    return results;
    
    ManualSplit GetPartWithoutIsolatedReturns() {
      var newBlocks = BlockRewriter.UpdateBlocks(new Stack<Block>(reversedBlocks), new HashSet<Block>(), 
        oldBlock => oldBlock.Cmds.Select(TransformAssertCmd).ToList());
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