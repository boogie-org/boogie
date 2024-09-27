#nullable enable
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace VCGeneration;

public class PathOrigin : TokenWrapper, ImplementationPartOrigin {

  public PathOrigin(IToken inner, ImmutableStack<Block> branches, DomRelation<Block> dominators) : base(inner) {
    Branches = branches;
    Dominators = dominators;
  }
  
  public ImmutableStack<Block> Branches { get; }
  public DomRelation<Block> Dominators { get; }
}

class ImplementationRootOrigin : TokenWrapper, ImplementationPartOrigin {
  public ImplementationRootOrigin(Implementation implementation) : base(implementation.tok)
  {
  }
}