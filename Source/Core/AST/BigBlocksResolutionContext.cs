using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class BigBlocksResolutionContext
{
  StmtList /*!*/ stmtList;

  [Peer] List<Block /*!*/> blocks;

  string /*!*/ prefix = "anon";

  int anon = 0;

  public string FreshPrefix()
  {
    return prefix + anon++;
  }

  HashSet<string /*!*/> allLabels = new();

  public Errors ErrorHandler { get; }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(stmtList != null);
    Contract.Invariant(cce.NonNullElements(blocks, true));
    Contract.Invariant(prefix != null);
    Contract.Invariant(cce.NonNullElements(allLabels, true));
    Contract.Invariant(ErrorHandler != null);
  }

  private void ComputeAllLabels(StmtList stmts)
  {
    if (stmts == null)
    {
      return;
    }

    foreach (BigBlock bb in stmts.BigBlocks)
    {
      if (bb.LabelName != null)
      {
        allLabels.Add(bb.LabelName);
      }

      if (bb.ec == null)
      {
        continue;
      }
      
      foreach (var list in bb.ec.StatementLists)
      {
        ComputeAllLabels(list);
      }
    }
  }

  public BigBlocksResolutionContext(StmtList stmtList, Errors errorHandler)
  {
    Contract.Requires(errorHandler != null);
    Contract.Requires(stmtList != null);
    this.stmtList = stmtList;
    // Inject an empty big block at the end of the body of a while loop if its current end is another while loop.
    // This transformation creates a suitable jump target for break statements inside the nested while loop.
    InjectEmptyBigBlockInsideWhileLoopBody(stmtList);
    this.ErrorHandler = errorHandler;
    ComputeAllLabels(stmtList);
  }

  public void AddBlock(Block block)
  {
    blocks.Add(block);
  }

  public List<Block /*!*/> /*!*/ Blocks
  {
    get
    {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
      if (blocks == null)
      {
        blocks = new List<Block /*!*/>();

        int startErrorCount = this.ErrorHandler.count;
        // Check that all goto statements go to a label in allLabels, and no break statement to a non-enclosing loop.
        // Also, determine a good value for "prefix".
        CheckLegalLabels(stmtList, null, null);

        // fill in names of anonymous blocks
        NameAnonymousBlocks(stmtList);

        // determine successor blocks
        RecordSuccessors(stmtList, null);

        if (this.ErrorHandler.count == startErrorCount)
        {
          // generate blocks from the big blocks
          CreateBlocks(stmtList, null);
        }
      }

      return blocks;
    }
  }

  public void InjectEmptyBigBlockInsideWhileLoopBody(StmtList stmtList)
  {
    foreach (var bb in stmtList.BigBlocks)
    {
      bb.ec.InjectEmptyBigBlockInsideWhileLoopBody(this);
    }
  }

  public void CheckLegalLabels(StmtList stmtList, StmtList parentContext, BigBlock parentBigBlock)
  {
    Contract.Requires(stmtList != null);
    Contract.Requires((parentContext == null) == (parentBigBlock == null));
    Contract.Requires(stmtList.ParentContext == null); // it hasn't been set yet
    //modifies stmtList.*;
    Contract.Ensures(stmtList.ParentContext == parentContext);
    stmtList.ParentContext = parentContext;
    stmtList.ParentBigBlock = parentBigBlock;

    // record the labels declared in this StmtList
    foreach (BigBlock b in stmtList.BigBlocks)
    {
      if (b.LabelName != null)
      {
        string n = b.LabelName;
        if (n.StartsWith(prefix))
        {
          if (prefix.Length < n.Length && n[prefix.Length] == '0')
          {
            prefix += "1";
          }
          else
          {
            prefix += "0";
          }
        }

        stmtList.AddLabel(b.LabelName);
      }
    }

    // check that labels in this and nested StmtList's are legal
    foreach (BigBlock b in stmtList.BigBlocks)
    {
      // goto's must reference blocks in enclosing blocks
      if (b.tc is GotoCmd)
      {
        GotoCmd g = (GotoCmd) b.tc;
        foreach (string /*!*/ lbl in cce.NonNull(g.labelNames))
        {
          Contract.Assert(lbl != null);
          /*
            bool found = false;
            for (StmtList sl = stmtList; sl != null; sl = sl.ParentContext) {
              if (sl.Labels.Contains(lbl)) {
                found = true;
                break;
              }
            }
            if (!found) {
              this.errorHandler.SemErr(g.tok, "Error: goto label '" + lbl + "' is undefined or out of reach");
            }
            */
          if (!allLabels.Contains(lbl))
          {
            this.ErrorHandler.SemErr(g.tok, "Error: goto label '" + lbl + "' is undefined");
          }
        }
      }
      else
      {
        b.ec.CheckLegalLabels(this, this.stmtList, b);
      }
    }
  }

  void NameAnonymousBlocks(StmtList stmtList)
  {
    Contract.Requires(stmtList != null);
    foreach (BigBlock b in stmtList.BigBlocks)
    {
      if (b.LabelName == null)
      {
        b.LabelName = FreshPrefix();
      }

      foreach (var l in b.ec.StatementLists)
      {
        NameAnonymousBlocks(l);
      }
    }
  }

  public void RecordSuccessors(StmtList stmtList, BigBlock successor)
  {
    Contract.Requires(stmtList != null);
    for (int i = stmtList.BigBlocks.Count; 0 <= --i;)
    {
      BigBlock big = stmtList.BigBlocks[i];
      big.successorBigBlock = successor;

      big.ec.RecordSuccessors(this, big);
      successor = big;
    }
  }

  // If the enclosing context is a loop, then "runOffTheEndLabel" is the loop head label;
  // otherwise, it is null.
  public void CreateBlocks(StmtList stmtList, string runOffTheEndLabel)
  {
    Contract.Requires(stmtList != null);
    Contract.Requires(blocks != null);
    List<Cmd> cmdPrefixToApply = stmtList.PrefixCommands;

    int n = stmtList.BigBlocks.Count;
    foreach (BigBlock b in stmtList.BigBlocks)
    {
      n--;
      Contract.Assert(b.LabelName != null);
      List<Cmd> theSimpleCmds;
      if (cmdPrefixToApply == null)
      {
        theSimpleCmds = b.simpleCmds;
      }
      else
      {
        theSimpleCmds = new List<Cmd>();
        theSimpleCmds.AddRange(cmdPrefixToApply);
        theSimpleCmds.AddRange(b.simpleCmds);
        cmdPrefixToApply = null; // now, we've used 'em up
      }

      if (b.tc != null)
      {
        // this BigBlock has the very same components as a Block
        Contract.Assert(b.ec == null);
        Block block = new Block(b.tok, b.LabelName, theSimpleCmds, b.tc);
        blocks.Add(block);
      }
      else if (b.ec == null)
      {
        TransferCmd trCmd;
        if (n == 0 && runOffTheEndLabel != null)
        {
          // goto the given label instead of the textual successor block
          trCmd = new GotoCmd(stmtList.EndCurly, new List<String> {runOffTheEndLabel});
        }
        else
        {
          trCmd = GotoSuccessor(stmtList.EndCurly, b);
        }

        Block block = new Block(b.tok, b.LabelName, theSimpleCmds, trCmd);
        blocks.Add(block);
      }
      else
      {
        b.ec.CreateBlocks(this, b, theSimpleCmds, n == 0 ? runOffTheEndLabel : null);
      }
    }
  }

  public static TransferCmd GotoSuccessor(IToken tok, BigBlock b)
  {
    Contract.Requires(b != null);
    Contract.Requires(tok != null);
    Contract.Ensures(Contract.Result<TransferCmd>() != null);
    if (b.successorBigBlock != null)
    {
      return new GotoCmd(tok, new List<String> {b.successorBigBlock.LabelName});
    }
    else
    {
      return new ReturnCmd(tok);
    }
  }
}