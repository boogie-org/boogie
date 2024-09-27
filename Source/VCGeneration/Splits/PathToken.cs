#nullable enable
using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Boogie;

namespace VCGeneration;

class PathToken : TokenWrapper {

  public PathToken(IToken inner, ImmutableStack<IToken> branches) : base(inner) {
    Branches = branches;
  }
  
  public ImmutableStack<IToken> Branches { get; }
  public override string Render(CoreOptions options) {
    return base.Render(options);
  }
}