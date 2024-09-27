#nullable enable
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using Microsoft.Boogie;

namespace VCGeneration;

public class PathOrigin : TokenWrapper, ImplementationPartOrigin {

  public PathOrigin(IToken inner, ImmutableStack<IToken> branches) : base(inner) {
    Branches = branches;
  }
  
  public ImmutableStack<IToken> Branches { get; }

  public string Render(CoreOptions options) {
    return $" passing through: [{string.Join(", ", Branches.Select(b => $"({b.line},{b.col})"))}]";
  }
}

class ImplementationRootOrigin : TokenWrapper, ImplementationPartOrigin {
  public ImplementationRootOrigin(Implementation implementation) : base(implementation.tok)
  {
  }

  public string Render(CoreOptions options) {
    return "";
  }
}