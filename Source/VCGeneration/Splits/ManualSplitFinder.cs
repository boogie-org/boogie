#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using VC;

namespace VCGeneration;


public static class ManualSplitFinder {
  
  public static IEnumerable<ManualSplit> GetParts(VCGenOptions options, ImplementationRun run,
    Func<IImplementationPartOrigin, IList<Block>, ManualSplit> createPart) {
    
    var focussedParts = FocusAttributeHandler.GetParts(options, run, createPart);
    var result = focussedParts.SelectMany(focussedPart => {
      var (isolatedJumps, withoutIsolatedJumps) =
        IsolateAttributeOnJumpsHandler.GetParts(options, focussedPart, createPart);
      return new[] { withoutIsolatedJumps }.Concat(isolatedJumps).SelectMany(isolatedJumpSplit => {
        var (isolatedAssertions, withoutIsolatedAssertions) =
          IsolateAttributeOnAssertsHandler.GetParts(options, isolatedJumpSplit, createPart);

        var splitParts =  SplitAttributeHandler.GetParts(withoutIsolatedAssertions);
        return isolatedAssertions.Concat(splitParts).ToList();
      });
    });
    // return result;
    var nonEmptyResults = result.Where(s => s.Asserts.Any()).ToList();
    return nonEmptyResults.Any() ? nonEmptyResults : focussedParts;
  }
}

public interface IImplementationPartOrigin : IToken {
  string ShortName { get; }
}