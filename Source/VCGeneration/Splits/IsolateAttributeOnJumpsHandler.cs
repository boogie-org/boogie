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
    Func<IImplementationPartOrigin, IList<Block>, ManualSplit> createPart) {

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

      var gotoFromReturn = gotoCmd.tok as GotoFromReturn;
      var isolateAttribute = QKeyValue.FindAttribute(gotoCmd.Attributes, p => p.Key == "isolate");
      var isTypeOfAssert = gotoFromReturn != null && gotoFromReturn.Origin.tok.IsSourceToken;
      var isolate = BlockRewriter.ShouldIsolate(isTypeOfAssert && splitOnEveryAssert, isolateAttribute);
      if (!isolate) {
        continue;
      }

      isolatedBlockJumps.Add(block);
      var ancestors = dag.ComputeReachability(block, false);
      var descendants = dag.ComputeReachability(block, true);
      var blocksToInclude = ancestors.Union(descendants).ToHashSet();

      var originalJump = gotoFromReturn?.Origin ?? (TransferCmd)gotoCmd;
      var origin = new JumpOrigin(partToDivide.Token, originalJump);
      
      if (isolateAttribute != null && isolateAttribute.Params.OfType<string>().Any(p => Equals(p, "paths"))) {
        // These conditions hold if the goto was originally a return
        Debug.Assert(gotoCmd.LabelTargets.Count == 1);
        Debug.Assert(gotoCmd.LabelTargets[0].TransferCmd is not GotoCmd);
        results.AddRange(rewriter.GetSplitsForIsolatedPaths(gotoCmd.LabelTargets[0], blocksToInclude, origin));
      } else {
        var newBlocks = rewriter.ComputeNewBlocks(blocksToInclude, (oldBlock, newBlock) => {
          if (ancestors.Contains(oldBlock)) {
            newBlock.Cmds = oldBlock.Cmds.Select(c => CommandTransformations.AssertIntoAssume(rewriter.Options, c))
              .ToList();
          } else {
            newBlock.Cmds = oldBlock.Cmds;
            if (newBlock.TransferCmd is ReturnCmd && gotoFromReturn != null) {
              /*
               I'm not sure why this is necessary.
               Possibly two block are coalesced which deletes the goto with the GotoFromReturn
               */
              newBlock.TransferCmd = gotoFromReturn.Origin;
            }
          }
        });
        results.Add(rewriter.CreateSplit(origin, newBlocks));
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
      return rewriter.CreateSplit(new RemainingAssertionsOrigin(partToDivide.Token), newBlocks);
    }
  }
}

public class JumpOrigin : TokenWrapper, IImplementationPartOrigin {
  public IImplementationPartOrigin Origin { get; }
  public TransferCmd IsolatedReturn { get; }

  public JumpOrigin(IImplementationPartOrigin origin, TransferCmd isolatedReturn) : base(isolatedReturn.tok) {
    Origin = origin;
    this.IsolatedReturn = isolatedReturn;
  }

  public string ShortName => $"{Origin.ShortName}/{KindName}@{IsolatedReturn.Line}";
  public string KindName => IsolatedReturn is ReturnCmd ? "return" : "goto";
}