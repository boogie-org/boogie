#nullable enable
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using Microsoft.Boogie;

namespace VCGeneration;

class PathToken : TokenWrapper, ImplementationPartToken {

  public PathToken(IToken inner, ImmutableStack<IToken> branches) : base(inner) {
    Branches = branches;
  }
  
  public ImmutableStack<IToken> Branches { get; }

  public string Render(CoreOptions options) {
    return $" after passing through: [{string.Join(", ", Branches.Select(b => $"({b.line},{b.col})"))}]";
  }
}

class ImplementationRootToken : TokenWrapper, ImplementationPartToken {
  public ImplementationRootToken(Implementation implementation) : base(implementation.tok)
  {
  }

  public string Render(CoreOptions options) {
    return "";
  }
}