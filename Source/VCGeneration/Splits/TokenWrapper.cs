using Microsoft.Boogie;

namespace VCGeneration;

class TokenWrapper : IToken {
  private readonly IToken inner;

  public TokenWrapper(IToken inner) {
    this.inner = inner;
  }

  public int CompareTo(IToken? other) {
    return inner.CompareTo(other);
  }

  public int kind {
    get => inner.kind;
    set => inner.kind = value;
  }

  public string filename {
    get => inner.filename;
    set => inner.filename = value;
  }

  public int pos {
    get => inner.pos;
    set => inner.pos = value;
  }

  public int col {
    get => inner.col;
    set => inner.col = value;
  }

  public int line {
    get => inner.line;
    set => inner.line = value;
  }

  public string val {
    get => inner.val;
    set => inner.val = value;
  }

  public bool IsValid => inner.IsValid;
}