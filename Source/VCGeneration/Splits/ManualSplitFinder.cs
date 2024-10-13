#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using VC;

namespace VCGeneration;


public static class ManualSplitFinder {
  
  public static IEnumerable<ManualSplit> GetParts(VCGenOptions options, ImplementationRun run,
    Func<IImplementationPartOrigin, List<Block>, ManualSplit> createPart) {
    
    var focussedParts = FocusAttributeHandler.GetParts(options, run, createPart);
    var result = focussedParts.SelectMany(focussedPart => {
      var (isolatedJumps, withoutIsolatedJumps) =
        IsolateAttributeOnJumpsHandler.GetParts(options, focussedPart, createPart);
      var (isolatedAssertions, withoutIsolatedAssertions) =
        IsolateAttributeOnAssertsHandler.GetParts(options, withoutIsolatedJumps, createPart);
    
      var splitParts = SplitAttributeHandler.GetParts(withoutIsolatedAssertions);
      var splits = isolatedJumps.Concat(isolatedAssertions).Concat(splitParts).Where(s => s.Asserts.Any()).ToList();
      return splits.ToList().Any() ? splits.ToList() : new List<ManualSplit> { focussedPart };
    });
    return result;
  }
}

public interface IImplementationPartOrigin : IToken {
  string ShortName { get; }
}