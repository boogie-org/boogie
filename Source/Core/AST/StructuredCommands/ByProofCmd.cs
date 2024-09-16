namespace Microsoft.Boogie;

public class ByProofCmd : StructuredCmd
{
  public StmtList Body;
  public StmtList Proof;
  
  public ByProofCmd(IToken tok) : base(tok)
  {
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    throw new System.NotImplementedException();
  }
}