using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class BreakCmd : StructuredCmd
{
  public string Label;
  public BigBlock BreakEnclosure;

  public BreakCmd(IToken tok, string label)
    : base(tok)
  {
    Contract.Requires(tok != null);
    Label = label;
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    if (Label == null)
    {
      stream.WriteLine(level, "break;");
    }
    else
    {
      stream.WriteLine(level, "break {0};", Label);
    }
  }

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock bigBlock, List<Cmd> incomingCommands,
    string runOffTheEndLabel)
  {
    Contract.Assert(this.BreakEnclosure != null);
    Block block = new Block(bigBlock.tok, bigBlock.LabelName, incomingCommands, BigBlocksResolutionContext.GotoSuccessor(bigBlock.Ec.tok, BreakEnclosure));
    context.AddBlock(block);
  }

  public override IEnumerable<StmtList> StatementLists => Enumerable.Empty<StmtList>();
  public override void RecordSuccessors(BigBlocksResolutionContext context, BigBlock bigBlock)
  {
  }
}