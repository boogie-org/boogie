using System.Collections.Generic;
using System.Diagnostics.Contracts;

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

  public override void InjectEmptyBigBlockInsideWhileLoopBody(BigBlocksResolutionContext context)
  {
  }

  public override void CheckLegalLabels(BigBlocksResolutionContext context, StmtList stmtList, BigBlock bigBlock)
  {
    Contract.Assert(BreakEnclosure == null); // it hasn't been initialized yet
    bool found = false;
    for (StmtList sl = stmtList; sl.ParentBigBlock != null; sl = sl.ParentContext)
    {
      cce.LoopInvariant(sl != null);
      BigBlock bb = sl.ParentBigBlock;

      if (Label == null)
      {
        // a label-less break statement breaks out of the innermost enclosing while statement
        if (bb.ec is WhileCmd)
        {
          BreakEnclosure = bb;
          found = true;
          break;
        }
      }
      else if (Label == bb.LabelName)
      {
        // a break statement with a label can break out of both if statements and while statements
        if (bb.simpleCmds.Count == 0)
        {
          // this is a good target:  the label refers to the if/while statement
          BreakEnclosure = bb;
        }
        else
        {
          // the label of bb refers to the first statement of bb, which in which case is a simple statement, not an if/while statement
          context.ErrorHandler.SemErr(tok,
            "Error: break label '" + Label + "' must designate an enclosing statement");
        }

        found = true; // don't look any further, since we've found a matching label
        break;
      }
    }

    if (!found)
    {
      if (Label == null)
      {
        context.ErrorHandler.SemErr(tok, "Error: break statement is not inside a loop");
      }
      else
      {
        context.ErrorHandler.SemErr(tok,
          "Error: break label '" + Label + "' must designate an enclosing statement");
      }
    }
  }

  public override void ComputeAllLabels(BigBlocksResolutionContext context)
  {
  }

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock b, List<Cmd> theSimpleCmds, StmtList stmtList,
    string runOffTheEndLabel)
  {
    Contract.Assert(this.BreakEnclosure != null);
    Block block = new Block(b.tok, b.LabelName, theSimpleCmds, BigBlocksResolutionContext.GotoSuccessor(b.ec.tok, BreakEnclosure));
    context.AddBlock(block);
  }
}