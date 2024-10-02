#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using VC;
using VCGeneration.Splits;

namespace VCGeneration;


public static class ManualSplitFinder {
  
  public static IEnumerable<ManualSplit> GetParts(VCGenOptions options, ImplementationRun run,
    Func<ImplementationPartOrigin, List<Block>, ManualSplit> createPart) 
  {
    var blockRewriter = new BlockRewriter(options, run.Implementation.Blocks, createPart);
    var focussedParts = new FocusAttributeHandler(blockRewriter).GetParts(run);
    return focussedParts.SelectMany(focussedPart => {
      var (isolatedJumps, withoutIsolatedJumps) =
        new IsolateAttributeOnJumpsHandler(blockRewriter).GetParts(focussedPart);
      var (isolatedAssertions, withoutIsolatedAssertions) =
        new IsolateAttributeOnAssertsHandler(new BlockRewriter(options, withoutIsolatedJumps.Blocks, createPart)).GetParts(withoutIsolatedJumps);

      var splitParts = new SplitAttributeHandler(blockRewriter).GetParts(withoutIsolatedAssertions);
      return isolatedJumps.Concat(isolatedAssertions).Concat(splitParts);
    });
  }
}

public interface ImplementationPartOrigin : IToken {
  string ShortName { get; }
}