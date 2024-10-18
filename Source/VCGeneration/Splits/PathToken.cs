#nullable enable
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace VCGeneration;

public class PathOrigin : TokenWrapper, IImplementationPartOrigin {

  public PathOrigin(IToken inner, List<Block> branches) : base(inner) {
    Branches = branches;
  }
  
  public List<Block> Branches { get; }
  public string ShortName => $"/assert@{line}[{string.Join(",", Branches.Select(b => b.tok.line))}]";
}

class ImplementationRootOrigin : TokenWrapper, IImplementationPartOrigin {
  public ImplementationRootOrigin(Implementation implementation) : base(implementation.tok)
  {
  }

  public string ShortName => "";
}