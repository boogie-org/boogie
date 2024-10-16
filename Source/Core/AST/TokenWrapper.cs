#nullable enable
using Microsoft.Boogie;

namespace VCGeneration;

public class ImplicitJump : TokenWrapper {
  public ImplicitJump(IToken inner) : base(inner)
  {
  }
}

public class TokenWrapper : IToken {
  public IToken Inner { get; }

  public TokenWrapper(IToken inner) {
    this.Inner = inner;
  }

  public int CompareTo(IToken? other) {
    return Inner.CompareTo(other);
  }

  public int kind {
    get => Inner.kind;
    set => Inner.kind = value;
  }

  public string filename {
    get => Inner.filename;
    set => Inner.filename = value;
  }

  public int pos {
    get => Inner.pos;
    set => Inner.pos = value;
  }

  public int col {
    get => Inner.col;
    set => Inner.col = value;
  }

  public int line {
    get => Inner.line;
    set => Inner.line = value;
  }

  public string val {
    get => Inner.val;
    set => Inner.val = value;
  }

  public bool IsValid => Inner.IsValid;
}