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

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock bigBlock, List<Cmd> incomingCommands,
    string runOffTheEndLabel)
  {
    bigBlock.LabelName
    context.CreateBlocks(Proof, null);
    context.CreateBlocks(Body, runOffTheEndLabel);
  }

  public override IEnumerable<StmtList> StatementLists => new[] { Body, Proof };
  public override void RecordSuccessors(BigBlocksResolutionContext context, BigBlock bigBlock)
  {
    context.RecordSuccessors(Body, bigBlock.Successor);
  }
}