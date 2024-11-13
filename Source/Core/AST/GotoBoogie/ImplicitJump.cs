#nullable enable
using Microsoft.Boogie;

namespace VCGeneration;

public class ImplicitJump : TokenWrapper {
  public ImplicitJump(IToken inner) : base(inner)
  {
  }
}