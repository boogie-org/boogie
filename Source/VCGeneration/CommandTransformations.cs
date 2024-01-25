using Microsoft.Boogie;
using VC;

namespace VCGeneration;

public static class CommandTransformations
{
  public static Cmd AssertIntoAssume(VCGenOptions options, Cmd c)
  {
    if (c is AssertCmd assertCmd)
    {
      return VerificationConditionGenerator.AssertTurnedIntoAssume(options, assertCmd);
    }

    return c;
  }
}