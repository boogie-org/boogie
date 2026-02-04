using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class ReturnCmd : TransferCmd
{
  public QKeyValue Attributes { get; set; }
    
  public ReturnCmd(IToken tok)
    : base(tok)
  {
    
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
    
    return visitor.VisitReturnCmd(this);
  }
}