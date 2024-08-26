using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using VC;

namespace VCGeneration;

public static class CommandTransformations
{
  public static IEnumerable<Cmd> AssertIntoAssumes(VCGenOptions options, Cmd cmd)
  {
    if (cmd is AssertCmd assertCmd) {
      return assertCmd.Remember 
        ? new[] { VerificationConditionGenerator.AssertTurnedIntoAssume(options, assertCmd) } 
        : Enumerable.Empty<Cmd>();
    }

    return new[] {cmd};
  }
}