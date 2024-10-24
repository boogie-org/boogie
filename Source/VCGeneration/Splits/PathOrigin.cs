#nullable enable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace VCGeneration;

public class PathOrigin : TokenWrapper, IImplementationPartOrigin {

  public PathOrigin(IImplementationPartOrigin inner, List<IToken> branchTokens) : base(inner) {
    Inner = inner;
    BranchTokens = branchTokens;
  }

  public new IImplementationPartOrigin Inner { get; }
  public List<IToken> BranchTokens { get; }
  public string ShortName => $"{Inner.ShortName}/path[{string.Join(",", BranchTokens.Select(b => b.line))}]";
}