#nullable enable
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace VCGeneration;

public class PathOrigin : TokenWrapper, IImplementationPartOrigin {
  private readonly string kindName;

  public PathOrigin(IImplementationPartOrigin inner, List<IToken> branchTokens, string kindName) : base(inner) {
    this.kindName = kindName;
    Inner = inner;
    BranchTokens = branchTokens;
  }

  public new IImplementationPartOrigin Inner { get; }
  public List<IToken> BranchTokens { get; }
  public string ShortName => $"{Inner.ShortName}/{kindName}[{string.Join(",", BranchTokens.Select(b => b.line))}]";
  public string KindName => "path";
}

class ImplementationRootOrigin : TokenWrapper, IImplementationPartOrigin {
  public ImplementationRootOrigin(Implementation implementation) : base(implementation.tok)
  {
  }

  public string ShortName => "";
  public string KindName => "root";
}