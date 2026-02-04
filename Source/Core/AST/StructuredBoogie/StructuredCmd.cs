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
      
      return this._tok;
    }
    set
    {
      
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
    
    this._tok = tok;
  }

  public abstract void Emit(TokenTextWriter stream, int level);
}