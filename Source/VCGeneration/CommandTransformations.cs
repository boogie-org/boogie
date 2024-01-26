using Microsoft.Boogie;
using VC;

namespace VCGeneration;

public class CommandTransformations
{
  public static Cmd AssertIntoAssume(VCGenOptions options, Cmd c)
  {
    if (c is AssertCmd assrt)
    {
      return VCGen.AssertTurnedIntoAssume(options, assrt);
    }

    return c;
  }
}