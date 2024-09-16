using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class BigBlocksResolutionContext
{
  private readonly StmtList /*!*/ rootList;

  [Peer] private List<Block /*!*/> blocks;
  private string /*!*/ prefix = "anon";
  private int anon = 0;
  private readonly HashSet<string /*!*/> allLabels = new();
  private Errors ErrorHandler { get; }
  
  public string FreshPrefix()
  {
    return prefix + anon++;
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(rootList != null);
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

      if (bb.Ec == null)
      {
        continue;
      }
      
      foreach (var list in bb.Ec.StatementLists)
      {
        ComputeAllLabels(list);
      }
    }
  }

  public BigBlocksResolutionContext(StmtList rootList, Errors errorHandler)
  {
    Contract.Requires(errorHandler != null);
    Contract.Requires(rootList != null);
    this.rootList = rootList;
    this.ErrorHandler = errorHandler;
    
    // Inject an empty big block at the end of the body of a while loop if its current end is another while loop.
    // This transformation creates a suitable jump target for break statements inside the nested while loop.
    InjectEmptyBigBlockInsideWhileLoopBody(rootList);
    ComputeAllLabels(rootList);
  }

  public void AddBlock(Block block)
  {
    blocks.Add(block);
  }

  public List<Block /*!*/> /*!*/ GetOrComputeBlocks
  {
    get
    {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
      if (blocks != null)
      {
        return blocks;
      }

      blocks = new List<Block /*!*/>();

      int startErrorCount = this.ErrorHandler.count;
      // Check that all goto statements go to a label in allLabels, and no break statement to a non-enclosing loop.
      // Also, determine a good value for "prefix".
      CheckLegalLabels(rootList, null, null);

      // fill in names of anonymous blocks
      NameAnonymousBlocks(rootList);

      // determine successor blocks
      RecordSuccessors(rootList, null);

      if (this.ErrorHandler.count == startErrorCount)
      {
        // generate blocks from the big blocks
        CreateBlocks(rootList, null);
      }

      return blocks;
    }
  }

  private static void InjectEmptyBigBlockInsideWhileLoopBody(StmtList stmtList)
  {
    foreach (var bb in stmtList.BigBlocks)
    {
      foreach (var childList in bb.Ec.StatementLists)
      {
        InjectEmptyBigBlockInsideWhileLoopBody(childList);
      }

      if (bb.Ec is not WhileCmd whileCmd)
      {
        continue;
      }

      var newBigBlocks = new List<BigBlock>(whileCmd.Body.BigBlocks)
      {
        new(Token.NoToken, null, new List<Cmd>(), null, null)
      };
      whileCmd.Body = new StmtList(newBigBlocks, whileCmd.Body.EndCurly);
    }
  }

  private void CheckLegalLabels(StmtList stmtList, StmtList parentContext, BigBlock parentBigBlock)
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
    foreach (var bigBlock in stmtList.BigBlocks)
    {
      // goto's must reference blocks in enclosing blocks
      if (bigBlock.tc is GotoCmd gotoCmd)
      {
        foreach (string /*!*/ lbl in cce.NonNull(gotoCmd.labelNames))
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
            this.ErrorHandler.SemErr(gotoCmd.tok, "Error: goto label '" + lbl + "' is undefined");
          }
        }
      }
      else
      {
        foreach (var childList in bigBlock.Ec.StatementLists)
        {
          CheckLegalLabels(childList, this.rootList, bigBlock); 
        }
      }
    }
  }

  private void NameAnonymousBlocks(StmtList stmtList)
  {
    Contract.Requires(stmtList != null);
    foreach (var b in stmtList.BigBlocks)
    {
      b.LabelName ??= FreshPrefix();

      foreach (var l in b.Ec.StatementLists)
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
      big.Successor = successor;

      big.Ec.RecordSuccessors(this, big);
      successor = big;
    }
  }

  // If the enclosing context is a loop, then "runOffTheEndLabel" is the loop head label;
  // otherwise, it is null.
  public void CreateBlocks(StmtList stmtList, string runOffTheEndLabel)
  {
    Contract.Requires(stmtList != null);
    Contract.Requires(blocks != null);
    var cmdPrefixToApply = stmtList.PrefixCommands;

    int n = stmtList.BigBlocks.Count;
    foreach (var childBigBlock in stmtList.BigBlocks)
    {
      n--;
      Contract.Assert(childBigBlock.LabelName != null);
      List<Cmd> theSimpleCmds;
      if (cmdPrefixToApply == null)
      {
        theSimpleCmds = childBigBlock.PrefixCmds;
      }
      else
      {
        theSimpleCmds = new List<Cmd>();
        theSimpleCmds.AddRange(cmdPrefixToApply);
        theSimpleCmds.AddRange(childBigBlock.PrefixCmds);
        cmdPrefixToApply = null; // now, we've used 'em up
      }

      if (childBigBlock.tc != null)
      {
        // this BigBlock has the very same components as a Block
        Contract.Assert(childBigBlock.Ec == null);
        var block = new Block(childBigBlock.tok, childBigBlock.LabelName, theSimpleCmds, childBigBlock.tc);
        blocks.Add(block);
      }
      else if (childBigBlock.Ec == null)
      {
        TransferCmd trCmd;
        if (n == 0 && runOffTheEndLabel != null)
        {
          // goto the given label instead of the textual successor block
          trCmd = new GotoCmd(stmtList.EndCurly, new List<string> {runOffTheEndLabel});
        }
        else
        {
          trCmd = GotoSuccessor(stmtList.EndCurly, childBigBlock);
        }

        Block block = new Block(childBigBlock.tok, childBigBlock.LabelName, theSimpleCmds, trCmd);
        blocks.Add(block);
      }
      else
      {
        childBigBlock.Ec.CreateBlocks(this, childBigBlock, theSimpleCmds, n == 0 ? runOffTheEndLabel : null);
      }
    }
  }

  public static TransferCmd GotoSuccessor(IToken tok, BigBlock b)
  {
    Contract.Requires(b != null);
    Contract.Requires(tok != null);
    Contract.Ensures(Contract.Result<TransferCmd>() != null);
    if (b.Successor != null)
    {
      return new GotoCmd(tok, new List<String> {b.Successor.LabelName});
    }
    else
    {
      return new ReturnCmd(tok);
    }
  }
}