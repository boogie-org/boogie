using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class ReturnCmd : TransferCmd
{
  public QKeyValue Attributes { get; set; }
    
  public ReturnCmd(IToken tok)
    : base(tok)
  {
    Contract.Requires(tok != null);
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    stream.WriteLine(this, level, "return;");
  }

  public override void Resolve(ResolutionContext rc)
  {
    // nothing to resolve
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitReturnCmd(this);
  }
}