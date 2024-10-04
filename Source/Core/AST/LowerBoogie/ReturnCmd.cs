using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class ReturnCmd : TransferCmd
{
  public QKeyValue Attributes { get; set; }
    
  public ReturnCmd(IToken /*!*/ tok)
    : base(tok)
  {
    Contract.Requires(tok != null);
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    //Contract.Requires(stream != null);
    stream.WriteLine(this, level, "return;");
  }

  public override void Resolve(ResolutionContext rc)
  {
    //Contract.Requires(rc != null);
    // nothing to resolve
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    //Contract.Requires(visitor != null);
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitReturnCmd(this);
  }
}