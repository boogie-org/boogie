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

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock bigBlock, List<Cmd> theSimpleCmds,
    string runOffTheEndLabel)
  {
    throw new System.NotImplementedException();
  }

  public override IEnumerable<StmtList> StatementLists => new[] { Body, Proof };
  public override void RecordSuccessors(BigBlocksResolutionContext context, BigBlock bigBlock)
  {
    throw new System.NotImplementedException();
  }
}