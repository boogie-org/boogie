#nullable enable
using Microsoft.Boogie;

namespace VCGeneration;

public class ImplementationRootOrigin : TokenWrapper, IImplementationPartOrigin {
  public ImplementationRootOrigin(Implementation implementation) : base(implementation.tok)
  {
  }

  public string ShortName => "";
}