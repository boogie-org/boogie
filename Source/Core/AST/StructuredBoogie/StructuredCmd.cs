using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

[ContractClass(typeof(StructuredCmdContracts))]
public abstract class StructuredCmd
{
  private IToken
    _tok;

  public IToken tok
  {
    get
    {
      Contract.Ensures(Contract.Result<IToken>() != null);
      return this._tok;
    }
    set
    {
      Contract.Requires(value != null);
      this._tok = value;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(this._tok != null);
  }

  public StructuredCmd(IToken tok)
  {
    Contract.Requires(tok != null);
    this._tok = tok;
  }

  public abstract void Emit(TokenTextWriter stream, int level);
}