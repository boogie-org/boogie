using System.Collections.Generic;

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

  public override void InjectEmptyBigBlockInsideWhileLoopBody(BigBlocksResolutionContext context)
  {
    throw new System.NotImplementedException();
  }

  public override void CheckLegalLabels(BigBlocksResolutionContext context, StmtList stmtList, BigBlock bigBlock)
  {
    throw new System.NotImplementedException();
  }

  public override void ComputeAllLabels(BigBlocksResolutionContext context)
  {
    throw new System.NotImplementedException();
  }

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock b, List<Cmd> theSimpleCmds, StmtList stmtList,
    string runOffTheEndLabel)
  {
    throw new System.NotImplementedException();
  }
}