//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// BoogiePL - Absy.cs
//---------------------------------------------------------------------------------------------

namespace Microsoft.Boogie {
  using System;
  using System.Collections;
  using System.Diagnostics;
  using System.Collections.Generic;
  using Microsoft.Boogie.AbstractInterpretation;
  using AI = Microsoft.AbstractInterpretationFramework;
  using System.Diagnostics.Contracts;


  //---------------------------------------------------------------------
  // BigBlock
  public class BigBlock {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Anonymous || LabelName != null);
      Contract.Invariant(ec == null || tc == null);
      Contract.Invariant(simpleCmds != null);
    }

    public readonly IToken/*!*/ tok;
    public string LabelName;
    public readonly bool Anonymous;

    [Rep]
    public CmdSeq/*!*/ simpleCmds;
    public StructuredCmd ec;
    public TransferCmd tc;

    public BigBlock successorBigBlock;  // null if successor is end of procedure body (or if field has not yet been initialized)

    public BigBlock(IToken tok, string labelName, [Captured] CmdSeq simpleCmds, StructuredCmd ec, TransferCmd tc) {
      Contract.Requires(simpleCmds != null);
      Contract.Requires(tok != null);
      Contract.Requires(ec == null || tc == null);
      this.tok = tok;
      this.LabelName = labelName;
      this.Anonymous = labelName == null;
      this.simpleCmds = simpleCmds;
      this.ec = ec;
      this.tc = tc;
    }

    public void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      if (!Anonymous) {
        stream.WriteLine(level, "{0}:",
          CommandLineOptions.Clo.PrintWithUniqueASTIds ? String.Format("h{0}^^{1}", this.GetHashCode(), this.LabelName) : this.LabelName);
      }

      foreach (Cmd/*!*/ c in this.simpleCmds) {
        Contract.Assert(c != null);
        c.Emit(stream, level + 1);
      }

      if (this.ec != null) {
        this.ec.Emit(stream, level + 1);
      } else if (this.tc != null) {
        this.tc.Emit(stream, level + 1);
      }
    }
  }

  public class StmtList {
    [Rep]
    public readonly List<BigBlock/*!*/>/*!*/ BigBlocks;
    public CmdSeq PrefixCommands;
    public readonly IToken/*!*/ EndCurly;
    public StmtList ParentContext;
    public BigBlock ParentBigBlock;
    public HashSet<string/*!*/>/*!*/ Labels = new HashSet<string/*!*/>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(EndCurly != null);
      Contract.Invariant(cce.NonNullElements(BigBlocks));
      Contract.Invariant(cce.NonNullElements(Labels));
    }


    public StmtList([Captured] List<BigBlock/*!*/>/*!*/ bigblocks, IToken endCurly) {
      Contract.Requires(endCurly != null);
      Contract.Requires(cce.NonNullElements(bigblocks));
      Contract.Requires(bigblocks.Count > 0);
      this.BigBlocks = bigblocks;
      this.EndCurly = endCurly;
    }

    // prints the list of statements, not the surrounding curly braces
    public void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      bool needSeperator = false;
      foreach (BigBlock b in BigBlocks) {
        Contract.Assert(b != null);
        Contract.Assume(cce.IsPeerConsistent(b));
        if (needSeperator) {
          stream.WriteLine();
        }
        b.Emit(stream, level);
        needSeperator = true;
      }
    }

    /// <summary>
    /// Tries to insert the commands "prefixCmds" at the beginning of the first block
    /// of the StmtList, and returns "true" iff it succeeded.
    /// In the event of success, the "suggestedLabel" returns as the name of the
    /// block inside StmtList where "prefixCmds" were inserted.  This name may be the
    /// same as the one passed in, in case this StmtList has no preference as to what
    /// to call its first block.  In the event of failure, "suggestedLabel" is returned
    /// as its input value.
    /// Note, to be conservative (that is, ignoring the possible optimization that this
    /// method enables), this method can do nothing and return false.
    /// </summary>
    public bool PrefixFirstBlock([Captured] CmdSeq prefixCmds, ref string suggestedLabel) {
      Contract.Requires(suggestedLabel != null);
      Contract.Requires(prefixCmds != null);
      Contract.Ensures(Contract.Result<bool>() || cce.Owner.None(prefixCmds));  // "prefixCmds" is captured only on success
      Contract.Assume(PrefixCommands == null);  // prefix has not been used

      BigBlock bb0 = BigBlocks[0];
      if (prefixCmds.Length == 0) {
        // This is always a success, since there is nothing to insert.  Now, decide
        // which name to use for the first block.
        if (bb0.Anonymous) {
          bb0.LabelName = suggestedLabel;
        } else {
          Contract.Assert(bb0.LabelName != null);
          suggestedLabel = bb0.LabelName;
        }
        return true;

      } else {
        // There really is something to insert.  We can do this inline only if the first
        // block is anonymous (which implies there is no branch to it from within the block).
        if (bb0.Anonymous) {
          PrefixCommands = prefixCmds;
          bb0.LabelName = suggestedLabel;
          return true;
        } else {
          return false;
        }
      }
    }
  }

  /// <summary>
  /// The AST for Boogie structured commands was designed to support backward compatibility with
  /// the Boogie unstructured commands.  This has made the structured commands hard to construct.
  /// The StmtListBuilder class makes it easier to build structured commands.
  /// </summary>
  public class StmtListBuilder {
    List<BigBlock/*!*/>/*!*/ bigBlocks = new List<BigBlock/*!*/>();
    string label;
    CmdSeq simpleCmds;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(bigBlocks));
    }

    void Dump(StructuredCmd scmd, TransferCmd tcmd) {
      Contract.Requires(scmd == null || tcmd == null);
      Contract.Ensures(label == null && simpleCmds == null);
      if (label == null && simpleCmds == null && scmd == null && tcmd == null) {
        // nothing to do
      } else {
        if (simpleCmds == null) {
          simpleCmds = new CmdSeq();
        }
        bigBlocks.Add(new BigBlock(Token.NoToken, label, simpleCmds, scmd, tcmd));
        label = null;
        simpleCmds = null;
      }
    }

    /// <summary>
    /// Collects the StmtList built so far and returns it.  The StmtListBuilder should no longer
    /// be used once this method has been invoked.
    /// </summary>
    public StmtList Collect(IToken endCurlyBrace) {
      Contract.Requires(endCurlyBrace != null);
      Contract.Ensures(Contract.Result<StmtList>() != null);
      Dump(null, null);
      if (bigBlocks.Count == 0) {
        simpleCmds = new CmdSeq();  // the StmtList constructor doesn't like an empty list of BigBlock's
        Dump(null, null);
      }
      return new StmtList(bigBlocks, endCurlyBrace);
    }

    public void Add(Cmd cmd) {
      Contract.Requires(cmd != null);
      if (simpleCmds == null) {
        simpleCmds = new CmdSeq();
      }
      simpleCmds.Add(cmd);
    }

    public void Add(StructuredCmd scmd) {
      Contract.Requires(scmd != null);
      Dump(scmd, null);
    }

    public void Add(TransferCmd tcmd) {
      Contract.Requires(tcmd != null);
      Dump(null, tcmd);
    }

    public void AddLabelCmd(string label) {
      Contract.Requires(label != null);
      Dump(null, null);
      this.label = label;
    }

    public void AddLocalVariable(string name) {
      Contract.Requires(name != null);
      // TODO
    }
  }

  class BigBlocksResolutionContext {
    StmtList/*!*/ stmtList;
    [Peer]
    List<Block/*!*/> blocks;
    string/*!*/ prefix = "anon";
    int anon = 0;
    HashSet<string/*!*/> allLabels = new HashSet<string/*!*/>();
    Errors/*!*/ errorHandler;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(stmtList != null);
      Contract.Invariant(cce.NonNullElements(blocks, true));
      Contract.Invariant(prefix != null);
      Contract.Invariant(cce.NonNullElements(allLabels, true));
      Contract.Invariant(errorHandler != null);
    }

    private void ComputeAllLabels(StmtList stmts) {
      if (stmts == null) return;
      foreach (BigBlock bb in stmts.BigBlocks) {
        if (bb.LabelName != null) {
          allLabels.Add(bb.LabelName);
        }
        ComputeAllLabels(bb.ec);
      }
    }

    private void ComputeAllLabels(StructuredCmd cmd) {
      if (cmd == null) return;
      if (cmd is IfCmd) {
        IfCmd ifCmd = (IfCmd)cmd;
        ComputeAllLabels(ifCmd.thn);
        ComputeAllLabels(ifCmd.elseIf);
        ComputeAllLabels(ifCmd.elseBlock);
      }
      else if (cmd is WhileCmd) {
        WhileCmd whileCmd = (WhileCmd)cmd;
        ComputeAllLabels(whileCmd.Body);
      }
    }

    public BigBlocksResolutionContext(StmtList stmtList, Errors errorHandler) {
      Contract.Requires(errorHandler != null);
      Contract.Requires(stmtList != null);
      this.stmtList = stmtList;
      this.errorHandler = errorHandler;
      ComputeAllLabels(stmtList);
    }

    public List<Block/*!*/>/*!*/ Blocks {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
        if (blocks == null) {
          blocks = new List<Block/*!*/>();

          int startErrorCount = this.errorHandler.count;
          // Check that all goto statements go to a label in allLabels, and no break statement to a non-enclosing loop.
          // Also, determine a good value for "prefix".
          CheckLegalLabels(stmtList, null, null);

          // fill in names of anonymous blocks
          NameAnonymousBlocks(stmtList);

          // determine successor blocks
          RecordSuccessors(stmtList, null);

          if (this.errorHandler.count == startErrorCount) {
            // generate blocks from the big blocks
            CreateBlocks(stmtList, null);
          }
        }
        return blocks;
      }
    }

    void CheckLegalLabels(StmtList stmtList, StmtList parentContext, BigBlock parentBigBlock) {
      Contract.Requires(stmtList != null);
      Contract.Requires((parentContext == null) == (parentBigBlock == null));
      Contract.Requires(stmtList.ParentContext == null);  // it hasn't been set yet
      //modifies stmtList.*;
      Contract.Ensures(stmtList.ParentContext == parentContext);
      stmtList.ParentContext = parentContext;
      stmtList.ParentBigBlock = parentBigBlock;

      // record the labels declared in this StmtList
      foreach (BigBlock b in stmtList.BigBlocks) {
        if (b.LabelName != null) {
          string n = b.LabelName;
          if (n.StartsWith(prefix)) {
            if (prefix.Length < n.Length && n[prefix.Length] == '0') {
              prefix += "1";
            } else {
              prefix += "0";
            }
          }
          stmtList.Labels.Add(b.LabelName);
        }
      }

      // check that labels in this and nested StmtList's are legal
      foreach (BigBlock b in stmtList.BigBlocks) {
        // goto's must reference blocks in enclosing blocks
        if (b.tc is GotoCmd) {
          GotoCmd g = (GotoCmd)b.tc;
          foreach (string/*!*/ lbl in cce.NonNull(g.labelNames)) {
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
            if (!allLabels.Contains(lbl)) {
              this.errorHandler.SemErr(g.tok, "Error: goto label '" + lbl + "' is undefined");
            }
          }
        }

        // break labels must refer to an enclosing while statement
        else if (b.ec is BreakCmd) {
          BreakCmd bcmd = (BreakCmd)b.ec;
          Contract.Assert(bcmd.BreakEnclosure == null);  // it hasn't been initialized yet
          bool found = false;
          for (StmtList sl = stmtList; sl.ParentBigBlock != null; sl = sl.ParentContext) {
            cce.LoopInvariant(sl != null);
            BigBlock bb = sl.ParentBigBlock;

            if (bcmd.Label == null) {
              // a label-less break statement breaks out of the innermost enclosing while statement
              if (bb.ec is WhileCmd) {
                bcmd.BreakEnclosure = bb;
                found = true;
                break;
              }
            } else if (bcmd.Label == bb.LabelName) {
              // a break statement with a label can break out of both if statements and while statements
              if (bb.simpleCmds.Length == 0) {
                // this is a good target:  the label refers to the if/while statement
                bcmd.BreakEnclosure = bb;
              } else {
                // the label of bb refers to the first statement of bb, which in which case is a simple statement, not an if/while statement
                this.errorHandler.SemErr(bcmd.tok, "Error: break label '" + bcmd.Label + "' must designate an enclosing statement");
              }
              found = true;  // don't look any further, since we've found a matching label
              break;
            }
          }
          if (!found) {
            if (bcmd.Label == null) {
              this.errorHandler.SemErr(bcmd.tok, "Error: break statement is not inside a loop");
            } else {
              this.errorHandler.SemErr(bcmd.tok, "Error: break label '" + bcmd.Label + "' must designate an enclosing statement");
            }
          }
        }

        // recurse
        else if (b.ec is WhileCmd) {
          WhileCmd wcmd = (WhileCmd)b.ec;
          CheckLegalLabels(wcmd.Body, stmtList, b);
        } else {
          for (IfCmd ifcmd = b.ec as IfCmd; ifcmd != null; ifcmd = ifcmd.elseIf) {
            CheckLegalLabels(ifcmd.thn, stmtList, b);
            if (ifcmd.elseBlock != null) {
              CheckLegalLabels(ifcmd.elseBlock, stmtList, b);
            }
          }
        }
      }
    }

    void NameAnonymousBlocks(StmtList stmtList) {
      Contract.Requires(stmtList != null);
      foreach (BigBlock b in stmtList.BigBlocks) {
        if (b.LabelName == null) {
          b.LabelName = prefix + anon;
          anon++;
        }
        if (b.ec is WhileCmd) {
          WhileCmd wcmd = (WhileCmd)b.ec;
          NameAnonymousBlocks(wcmd.Body);
        } else {
          for (IfCmd ifcmd = b.ec as IfCmd; ifcmd != null; ifcmd = ifcmd.elseIf) {
            NameAnonymousBlocks(ifcmd.thn);
            if (ifcmd.elseBlock != null) {
              NameAnonymousBlocks(ifcmd.elseBlock);
            }
          }
        }
      }
    }

    void RecordSuccessors(StmtList stmtList, BigBlock successor) {
      Contract.Requires(stmtList != null);
      for (int i = stmtList.BigBlocks.Count; 0 <= --i; ) {
        BigBlock big = stmtList.BigBlocks[i];
        big.successorBigBlock = successor;

        if (big.ec is WhileCmd) {
          WhileCmd wcmd = (WhileCmd)big.ec;
          RecordSuccessors(wcmd.Body, successor);
        } else {
          for (IfCmd ifcmd = big.ec as IfCmd; ifcmd != null; ifcmd = ifcmd.elseIf) {
            RecordSuccessors(ifcmd.thn, successor);
            if (ifcmd.elseBlock != null) {
              RecordSuccessors(ifcmd.elseBlock, successor);
            }
          }
        }

        successor = big;
      }
    }

    // If the enclosing context is a loop, then "runOffTheEndLabel" is the loop head label;
    // otherwise, it is null.
    void CreateBlocks(StmtList stmtList, string runOffTheEndLabel) {
      Contract.Requires(stmtList != null);
      Contract.Requires(blocks != null);
      CmdSeq cmdPrefixToApply = stmtList.PrefixCommands;

      int n = stmtList.BigBlocks.Count;
      foreach (BigBlock b in stmtList.BigBlocks) {
        n--;
        Contract.Assert(b.LabelName != null);
        CmdSeq theSimpleCmds;
        if (cmdPrefixToApply == null) {
          theSimpleCmds = b.simpleCmds;
        } else {
          theSimpleCmds = new CmdSeq();
          theSimpleCmds.AddRange(cmdPrefixToApply);
          theSimpleCmds.AddRange(b.simpleCmds);
          cmdPrefixToApply = null;  // now, we've used 'em up
        }

        if (b.tc != null) {
          // this BigBlock has the very same components as a Block
          Contract.Assert(b.ec == null);
          Block block = new Block(b.tok, b.LabelName, theSimpleCmds, b.tc);
          blocks.Add(block);

        } else if (b.ec == null) {
          TransferCmd trCmd;
          if (n == 0 && runOffTheEndLabel != null) {
            // goto the given label instead of the textual successor block
            trCmd = new GotoCmd(stmtList.EndCurly, new StringSeq(runOffTheEndLabel));
          } else {
            trCmd = GotoSuccessor(stmtList.EndCurly, b);
          }
          Block block = new Block(b.tok, b.LabelName, theSimpleCmds, trCmd);
          blocks.Add(block);

        } else if (b.ec is BreakCmd) {
          BreakCmd bcmd = (BreakCmd)b.ec;
          Contract.Assert(bcmd.BreakEnclosure != null);
          Block block = new Block(b.tok, b.LabelName, theSimpleCmds, GotoSuccessor(b.ec.tok, bcmd.BreakEnclosure));
          blocks.Add(block);

        } else if (b.ec is WhileCmd) {
          WhileCmd wcmd = (WhileCmd)b.ec;
          string loopHeadLabel = prefix + anon + "_LoopHead";
          string/*!*/ loopBodyLabel = prefix + anon + "_LoopBody";
          string loopDoneLabel = prefix + anon + "_LoopDone";
          anon++;

          CmdSeq ssBody = new CmdSeq();
          CmdSeq ssDone = new CmdSeq();
          if (wcmd.Guard != null) {
            ssBody.Add(new AssumeCmd(wcmd.tok, wcmd.Guard));
            ssDone.Add(new AssumeCmd(wcmd.tok, Expr.Not(wcmd.Guard)));
          }

          // Try to squeeze in ssBody into the first block of wcmd.Body
          bool bodyGuardTakenCareOf = wcmd.Body.PrefixFirstBlock(ssBody, ref loopBodyLabel);

          // ... goto LoopHead;
          Block block = new Block(b.tok, b.LabelName, theSimpleCmds, new GotoCmd(wcmd.tok, new StringSeq(loopHeadLabel)));
          blocks.Add(block);

          // LoopHead: assert/assume loop_invariant; goto LoopDone, LoopBody;
          CmdSeq ssHead = new CmdSeq();
          foreach (PredicateCmd inv in wcmd.Invariants) {
            ssHead.Add(inv);
          }
          block = new Block(wcmd.tok, loopHeadLabel, ssHead, new GotoCmd(wcmd.tok, new StringSeq(loopDoneLabel, loopBodyLabel)));
          blocks.Add(block);

          if (!bodyGuardTakenCareOf) {
            // LoopBody: assume guard; goto firstLoopBlock;
            block = new Block(wcmd.tok, loopBodyLabel, ssBody, new GotoCmd(wcmd.tok, new StringSeq(wcmd.Body.BigBlocks[0].LabelName)));
            blocks.Add(block);
          }

          // recurse to create the blocks for the loop body
          CreateBlocks(wcmd.Body, loopHeadLabel);

          // LoopDone: assume !guard; goto loopSuccessor;
          TransferCmd trCmd;
          if (n == 0 && runOffTheEndLabel != null) {
            // goto the given label instead of the textual successor block
            trCmd = new GotoCmd(wcmd.tok, new StringSeq(runOffTheEndLabel));
          } else {
            trCmd = GotoSuccessor(wcmd.tok, b);
          }
          block = new Block(wcmd.tok, loopDoneLabel, ssDone, trCmd);
          blocks.Add(block);

        } else {
          IfCmd ifcmd = (IfCmd)b.ec;
          string predLabel = b.LabelName;
          CmdSeq predCmds = theSimpleCmds;

          for (; ifcmd != null; ifcmd = ifcmd.elseIf) {
            string thenLabel = prefix + anon + "_Then";
            Contract.Assert(thenLabel != null);
            string elseLabel = prefix + anon + "_Else";
            Contract.Assert(elseLabel != null);
            anon++;

            CmdSeq ssThen = new CmdSeq();
            CmdSeq ssElse = new CmdSeq();
            if (ifcmd.Guard != null) {
              ssThen.Add(new AssumeCmd(ifcmd.tok, ifcmd.Guard));
              ssElse.Add(new AssumeCmd(ifcmd.tok, Expr.Not(ifcmd.Guard)));
            }

            // Try to squeeze in ssThen/ssElse into the first block of ifcmd.thn/ifcmd.elseBlock
            bool thenGuardTakenCareOf = ifcmd.thn.PrefixFirstBlock(ssThen, ref thenLabel);
            bool elseGuardTakenCareOf = false;
            if (ifcmd.elseBlock != null) {
              elseGuardTakenCareOf = ifcmd.elseBlock.PrefixFirstBlock(ssElse, ref elseLabel);
            }

            // ... goto Then, Else;
            Block block = new Block(b.tok, predLabel, predCmds,
              new GotoCmd(ifcmd.tok, new StringSeq(thenLabel, elseLabel)));
            blocks.Add(block);

            if (!thenGuardTakenCareOf) {
              // Then: assume guard; goto firstThenBlock;
              block = new Block(ifcmd.tok, thenLabel, ssThen, new GotoCmd(ifcmd.tok, new StringSeq(ifcmd.thn.BigBlocks[0].LabelName)));
              blocks.Add(block);
            }

            // recurse to create the blocks for the then branch
            CreateBlocks(ifcmd.thn, n == 0 ? runOffTheEndLabel : null);

            if (ifcmd.elseBlock != null) {
              Contract.Assert(ifcmd.elseIf == null);
              if (!elseGuardTakenCareOf) {
                // Else: assume !guard; goto firstElseBlock;
                block = new Block(ifcmd.tok, elseLabel, ssElse, new GotoCmd(ifcmd.tok, new StringSeq(ifcmd.elseBlock.BigBlocks[0].LabelName)));
                blocks.Add(block);
              }

              // recurse to create the blocks for the else branch
              CreateBlocks(ifcmd.elseBlock, n == 0 ? runOffTheEndLabel : null);

            } else if (ifcmd.elseIf != null) {
              // this is an "else if"
              predLabel = elseLabel;
              predCmds = new CmdSeq();
              if (ifcmd.Guard != null) {
                predCmds.Add(new AssumeCmd(ifcmd.tok, Expr.Not(ifcmd.Guard)));
              }

            } else {
              // no else alternative is specified, so else branch is just "skip"
              // Else: assume !guard; goto ifSuccessor;
              TransferCmd trCmd;
              if (n == 0 && runOffTheEndLabel != null) {
                // goto the given label instead of the textual successor block
                trCmd = new GotoCmd(ifcmd.tok, new StringSeq(runOffTheEndLabel));
              } else {
                trCmd = GotoSuccessor(ifcmd.tok, b);
              }
              block = new Block(ifcmd.tok, elseLabel, ssElse, trCmd);
              blocks.Add(block);
            }
          }
        }
      }
    }

    TransferCmd GotoSuccessor(IToken tok, BigBlock b) {
      Contract.Requires(b != null);
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<TransferCmd>() != null);
      if (b.successorBigBlock != null) {
        return new GotoCmd(tok, new StringSeq(b.successorBigBlock.LabelName));
      } else {
        return new ReturnCmd(tok);
      }
    }
  }

  [ContractClass(typeof(StructuredCmdContracts))]
  public abstract class StructuredCmd {
    public IToken/*!*/ tok;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }

    public StructuredCmd(IToken tok) {
      Contract.Requires(tok != null);
      this.tok = tok;
    }

    public abstract void Emit(TokenTextWriter/*!*/ stream, int level);
  }
  [ContractClassFor(typeof(StructuredCmd))]
  public abstract class StructuredCmdContracts : StructuredCmd {
    public override void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }
    public StructuredCmdContracts() :base(null){

    }
  }

  public class IfCmd : StructuredCmd {
    public Expr Guard;
    public StmtList/*!*/ thn;
    public IfCmd elseIf;
    public StmtList elseBlock;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(thn != null);
      Contract.Invariant(elseIf == null || elseBlock == null);
    }



    public IfCmd(IToken/*!*/ tok, Expr guard, StmtList/*!*/ thn, IfCmd elseIf, StmtList elseBlock)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(thn != null);
      Contract.Requires(elseIf == null || elseBlock == null);
      this.Guard = guard;
      this.thn = thn;
      this.elseIf = elseIf;
      this.elseBlock = elseBlock;
      // base(tok);
    }

    public override void Emit(TokenTextWriter stream, int level) {
      stream.Write(level, "if (");
      IfCmd/*!*/ ifcmd = this;
      while (true) {
        if (ifcmd.Guard == null) {
          stream.Write("*");
        } else {
          ifcmd.Guard.Emit(stream);
        }
        stream.WriteLine(")");

        stream.WriteLine(level, "{");
        ifcmd.thn.Emit(stream, level + 1);
        stream.WriteLine(level, "}");

        if (ifcmd.elseIf != null) {
          stream.Write(level, "else if (");
          ifcmd = ifcmd.elseIf;
          continue;
        } else if (ifcmd.elseBlock != null) {
          stream.WriteLine(level, "else");
          stream.WriteLine(level, "{");
          ifcmd.elseBlock.Emit(stream, level + 1);
          stream.WriteLine(level, "}");
        }
        break;
      }
    }
  }

  public class WhileCmd : StructuredCmd {
    [Peer]
    public Expr Guard;
    public List<PredicateCmd/*!*/>/*!*/ Invariants;
    public StmtList/*!*/ Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Body != null);
      Contract.Invariant(cce.NonNullElements(Invariants));
    }


    public WhileCmd(IToken tok, [Captured] Expr guard, List<PredicateCmd/*!*/>/*!*/ invariants, StmtList/*!*/ body)
      : base(tok) {
      Contract.Requires(cce.NonNullElements(invariants));
      Contract.Requires(body != null);
      Contract.Requires(tok != null);
      this.Guard = guard;
      this.Invariants = invariants;
      this.Body = body;
      /// base(tok);
    }

    public override void Emit(TokenTextWriter stream, int level) {
      stream.Write(level, "while (");
      if (Guard == null) {
        stream.Write("*");
      } else {
        Guard.Emit(stream);
      }
      stream.WriteLine(")");

      foreach (PredicateCmd inv in Invariants) {
        if (inv is AssumeCmd) {
          stream.Write(level + 1, "free invariant ");
        } else {
          stream.Write(level + 1, "invariant ");
        }
        inv.Expr.Emit(stream);
        stream.WriteLine(";");
      }

      stream.WriteLine(level, "{");
      Body.Emit(stream, level + 1);
      stream.WriteLine(level, "}");
    }
  }

  public class BreakCmd : StructuredCmd {
    public string Label;
    public BigBlock BreakEnclosure;

    public BreakCmd(IToken tok, string label)
      : base(tok) {
      Contract.Requires(tok != null);
      this.Label = label;
      // base(tok);
    }

    public override void Emit(TokenTextWriter stream, int level) {
      
      if (Label == null) {
        stream.WriteLine(level, "break;");
      } else {
        stream.WriteLine(level, "break {0};", Label);
      }
    }
  }

  //---------------------------------------------------------------------
  // Block
  public sealed class Block : Absy {
    public string/*!*/ Label;  // Note, Label is mostly readonly, but it can change to the name of a nearby block during block coalescing and empty-block removal
    [Rep]
    [ElementsPeer]
    public CmdSeq/*!*/ Cmds;
    [Rep]  //PM: needed to verify Traverse.Visit
    public TransferCmd TransferCmd; // maybe null only because we allow deferred initialization (necessary for cyclic structures)

    // Abstract interpretation

    // public bool currentlyTraversed;

    public enum VisitState {
      ToVisit,
      BeingVisited,
      AlreadyVisited
    };     // used by WidenPoints.Compute
    public VisitState TraversingStatus;

    public bool widenBlock;
    public int iterations;         // Count the number of time we visited the block during fixpoint computation. Used to decide if we widen or not

    // Block-specific invariants...
    public AI.Lattice Lattice;    // The lattice used for the analysis of this block
    public AI.Lattice.Element PreInvariant;   // The initial abstract states for this block
    public AI.Lattice.Element PostInvariant;  // The exit abstract states for this block
    // KRML: We want to include the following invariant, but at the moment, doing so causes a run-time error (something about committed):
    //invariant ;

    // VC generation and SCC computation
    public BlockSeq/*!*/ Predecessors;

    // This field is used during passification to null-out entries in block2Incartion hashtable early
    public int succCount;

    public HashSet<Variable/*!*/> liveVarsBefore;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Label != null);
      Contract.Invariant(Cmds != null);
      Contract.Invariant(cce.NonNullElements(liveVarsBefore, true));
      Contract.Invariant((PreInvariant != null) == (PostInvariant != null));
    }

    public bool IsLive(Variable v) {
      Contract.Requires(v != null);
      if (liveVarsBefore == null)
        return true;
      return liveVarsBefore.Contains(v);
    }

    public Block()
      : this(Token.NoToken, "", new CmdSeq(), new ReturnCmd(Token.NoToken)) {

    }

    public Block(IToken tok, string/*!*/ label, CmdSeq/*!*/ cmds, TransferCmd transferCmd)
      : base(tok) {
      Contract.Requires(label != null);
      Contract.Requires(cmds != null);
      Contract.Requires(tok != null);
      this.Label = label;
      this.Cmds = cmds;
      this.TransferCmd = transferCmd;
      this.PreInvariant = null;
      this.PostInvariant = null;
      this.Predecessors = new BlockSeq();
      this.liveVarsBefore = null;
      this.TraversingStatus = VisitState.ToVisit;
      this.iterations = 0;
      // base(tok);
    }

    public void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      stream.WriteLine();
      stream.WriteLine(
        this,
        level,
        "{0}:{1}",
        CommandLineOptions.Clo.PrintWithUniqueASTIds ? String.Format("h{0}^^{1}", this.GetHashCode(), this.Label) : this.Label,
        this.widenBlock ? "  // cut point" : "");

      foreach (Cmd/*!*/ c in this.Cmds) {
        Contract.Assert(c != null);
        c.Emit(stream, level + 1);
      }
      Contract.Assume(this.TransferCmd != null);
      this.TransferCmd.Emit(stream, level + 1);
    }

    public void Register(ResolutionContext rc) {
      Contract.Requires(rc != null);
      rc.AddBlock(this);
    }

    public override void Resolve(ResolutionContext rc) {
      

      foreach (Cmd/*!*/ c in Cmds) {
        Contract.Assert(c != null);
        c.Resolve(rc);
      }
      Contract.Assume(this.TransferCmd != null);
      TransferCmd.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc) {
      
      foreach (Cmd/*!*/ c in Cmds) {
        Contract.Assert(c != null);
        c.Typecheck(tc);
      }
      Contract.Assume(this.TransferCmd != null);
      TransferCmd.Typecheck(tc);
    }

    /// <summary>
    /// Reset the abstract intepretation state of this block. It does this by putting the iterations to 0 and the pre and post states to null
    /// </summary>
    public void ResetAbstractInterpretationState() {
      //      this.currentlyTraversed = false;
      this.TraversingStatus = VisitState.ToVisit;
      this.iterations = 0;
      this.Lattice = null;
      this.PreInvariant = null;
      this.PostInvariant = null;
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return this.Label + (this.widenBlock ? "[w]" : "");
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBlock(this);
    }
  }

  //---------------------------------------------------------------------
  // Commands
  [ContractClassFor(typeof(Cmd))]
  public abstract class CmdContracts : Cmd {
    public CmdContracts() :base(null){

    }
    public override void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }
    public override void AddAssignedVariables(VariableSeq vars) {
      Contract.Requires(vars != null);
      throw new NotImplementedException();
    }
  }
  [ContractClass(typeof(CmdContracts))]
  public abstract class Cmd : Absy {
    public Cmd(IToken/*!*/ tok)
      : base(tok) {
      Contract.Assert(tok != null);
    }
    public abstract void Emit(TokenTextWriter/*!*/ stream, int level);
    public abstract void AddAssignedVariables(VariableSeq/*!*/ vars);
    public void CheckAssignments(TypecheckingContext tc) {
      Contract.Requires(tc != null);
      VariableSeq/*!*/ vars = new VariableSeq();
      this.AddAssignedVariables(vars);
      foreach (Variable/*!*/ v in vars) {
        Contract.Assert(v != null);
        if (!v.IsMutable) {
          tc.Error(this, "command assigns to an immutable variable: {0}", v.Name);
        } else if (!CommandLineOptions.Clo.DoModSetAnalysis && v is GlobalVariable && !tc.InFrame(v)) {
          tc.Error(this, "command assigns to a global variable that is not in the enclosing method's modifies clause: {0}", v.Name);
        }
      }
    }

    // Methods to simulate the old SimpleAssignCmd and MapAssignCmd
    public static AssignCmd SimpleAssign(IToken tok, IdentifierExpr lhs, Expr rhs) {
      Contract.Requires(rhs != null);
      Contract.Requires(lhs != null);
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<AssignCmd>() != null);
      List<AssignLhs/*!*/>/*!*/ lhss = new List<AssignLhs/*!*/>();
      List<Expr/*!*/>/*!*/ rhss = new List<Expr/*!*/>();

      lhss.Add(new SimpleAssignLhs(lhs.tok, lhs));
      rhss.Add(rhs);

      return new AssignCmd(tok, lhss, rhss);
    }

    public static AssignCmd/*!*/ MapAssign(IToken tok,
                                       IdentifierExpr/*!*/ map,
                                       ExprSeq/*!*/ indexes, Expr/*!*/ rhs) {

      Contract.Requires(tok != null);
      Contract.Requires(map != null);
      Contract.Requires(indexes != null);
      Contract.Requires(rhs != null);
      Contract.Ensures(Contract.Result<AssignCmd>() != null);
      List<AssignLhs/*!*/>/*!*/ lhss = new List<AssignLhs/*!*/>();
      List<Expr/*!*/>/*!*/ rhss = new List<Expr/*!*/>();
      List<Expr/*!*/>/*!*/ indexesList = new List<Expr/*!*/>();
      


      foreach (Expr e in indexes)
        indexesList.Add(cce.NonNull(e));

      lhss.Add(new MapAssignLhs(map.tok,
                                 new SimpleAssignLhs(map.tok, map),
                                 indexesList));
      rhss.Add(rhs);

      return new AssignCmd(tok, lhss, rhss);
    }

    public static AssignCmd/*!*/ MapAssign(IToken tok,
                                       IdentifierExpr/*!*/ map,
                                       params Expr[]/*!*/ args) {
      Contract.Requires(tok != null);
      Contract.Requires(map != null);
      Contract.Requires(args != null);
      Contract.Requires(args.Length > 0);   // at least the rhs
      Contract.Requires(Contract.ForAll(args, i => i != null));
      Contract.Ensures(Contract.Result<AssignCmd>() != null);

      List<AssignLhs/*!*/>/*!*/ lhss = new List<AssignLhs/*!*/>();
      List<Expr/*!*/>/*!*/ rhss = new List<Expr/*!*/>();
      List<Expr/*!*/>/*!*/ indexesList = new List<Expr/*!*/>();

      for (int i = 0; i < args.Length - 1; ++i)
        indexesList.Add(cce.NonNull(args[i]));

      lhss.Add(new MapAssignLhs(map.tok,
                                 new SimpleAssignLhs(map.tok, map),
                                 indexesList));
      rhss.Add(cce.NonNull(args[args.Length - 1]));

      return new AssignCmd(tok, lhss, rhss);
    }

    /// <summary>
    /// This is a helper routine for printing a linked list of attributes.  Each attribute
    /// is terminated by a space.
    /// </summary>
    public static void EmitAttributes(TokenTextWriter stream, QKeyValue attributes) {
      Contract.Requires(stream != null);
      for (QKeyValue kv = attributes; kv != null; kv = kv.Next) {
        kv.Emit(stream);
        stream.Write(" ");
      }
    }
    public static void ResolveAttributes(QKeyValue attributes, ResolutionContext rc) {
      Contract.Requires(rc != null);
      for (QKeyValue kv = attributes; kv != null; kv = kv.Next) {
        kv.Resolve(rc);
      }
    }
    public static void TypecheckAttributes(QKeyValue attributes, TypecheckingContext tc) {
      Contract.Requires(tc != null);
      for (QKeyValue kv = attributes; kv != null; kv = kv.Next) {
        kv.Typecheck(tc);
      }
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      System.IO.StringWriter buffer = new System.IO.StringWriter();
      using (TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, false)) {
        this.Emit(stream, 0);
      }
      return buffer.ToString();
    }
  }

  public class CommentCmd : Cmd // just a convenience for debugging
  {
    public readonly string/*!*/ Comment;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Comment != null);
    }

    public CommentCmd(string c)
      : base(Token.NoToken) {
      Contract.Requires(c != null);
      Comment = c;
      // base(Token.NoToken);
    }
    public override void Emit(TokenTextWriter stream, int level) {
      
      if (this.Comment.Contains("\n")) {
        stream.WriteLine(this, level, "/* {0} */", this.Comment);
      } else {
        stream.WriteLine(this, level, "// {0}", this.Comment);
      }
    }
    public override void Resolve(ResolutionContext rc) {
      
    }
    public override void AddAssignedVariables(VariableSeq vars) {
      
    }
    public override void Typecheck(TypecheckingContext tc) {
      
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      
      
      return visitor.VisitCommentCmd(this);
    }
  }

  // class for parallel assignments, which subsumes both the old
  // SimpleAssignCmd and the old MapAssignCmd
  public class AssignCmd : Cmd {
    public List<AssignLhs/*!*/>/*!*/ Lhss;
    public List<Expr/*!*/>/*!*/ Rhss;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Lhss));
      Contract.Invariant(cce.NonNullElements(Rhss));
    }


    public AssignCmd(IToken tok, List<AssignLhs/*!*/>/*!*/ lhss, List<Expr/*!*/>/*!*/ rhss)
      : base(tok) {//BASEMOVEA
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(cce.NonNullElements(lhss));
      //base(tok);
      Lhss = lhss;
      Rhss = rhss;
    }

    public override void Emit(TokenTextWriter stream, int level) {
      
      stream.Write(this, level, "");

      string/*!*/ sep = "";
      foreach (AssignLhs/*!*/ l in Lhss) {
        Contract.Assert(l != null);
        stream.Write(sep);
        sep = ", ";
        l.Emit(stream);
      }

      stream.Write(" := ");

      sep = "";
      foreach (Expr/*!*/ e in Rhss) {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }

      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc) {
      
      if (Lhss.Count != Rhss.Count)
        rc.Error(this,
                 "number of left-hand sides does not match number of right-hand sides");

      foreach (AssignLhs/*!*/ e in Lhss) {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }
      foreach (Expr/*!*/ e in Rhss) {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }

      // check for double occurrences of assigned variables
      // (could be optimised)
      for (int i = 0; i < Lhss.Count; ++i) {
        for (int j = i + 1; j < Lhss.Count; ++j) {
          if (cce.NonNull(Lhss[i].DeepAssignedVariable).Equals(
                  Lhss[j].DeepAssignedVariable))
            rc.Error(Lhss[j],
                     "variable {0} is assigned more than once in parallel assignment",
                     Lhss[j].DeepAssignedVariable);
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc) {
      
      foreach (AssignLhs/*!*/ e in Lhss) {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }
      foreach (Expr/*!*/ e in Rhss) {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }

      this.CheckAssignments(tc);

      for (int i = 0; i < Lhss.Count; ++i) {
        Type ltype = Lhss[i].Type;
        Type rtype = Rhss[i].Type;
        if (ltype != null && rtype != null) {
          // otherwise, there has already been an error when
          // typechecking the lhs or rhs
          if (!ltype.Unify(rtype))
            tc.Error(Lhss[i],
                     "mismatched types in assignment command (cannot assign {0} to {1})",
                     rtype, ltype);
        }
      }
    }

    public override void AddAssignedVariables(VariableSeq vars) {
      
      foreach (AssignLhs/*!*/ l in Lhss) {
        Contract.Assert(l != null);
        vars.Add(l.DeepAssignedVariable);
      }
    }

    // transform away the syntactic sugar of map assignments and
    // determine an equivalent assignment in which all rhs are simple
    // variables
    public AssignCmd/*!*/ AsSimpleAssignCmd {
      get {
        Contract.Ensures(Contract.Result<AssignCmd>() != null);

        List<AssignLhs/*!*/>/*!*/ newLhss = new List<AssignLhs/*!*/>();
        List<Expr/*!*/>/*!*/ newRhss = new List<Expr/*!*/>();

        for (int i = 0; i < Lhss.Count; ++i) {
          IdentifierExpr/*!*/ newLhs;
          Expr/*!*/ newRhs;
          Lhss[i].AsSimpleAssignment(Rhss[i], out newLhs, out newRhs);
          newLhss.Add(new SimpleAssignLhs(Token.NoToken, newLhs));
          newRhss.Add(newRhs);
        }

        return new AssignCmd(Token.NoToken, newLhss, newRhss);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      

      return visitor.VisitAssignCmd(this);
    }
  }

  // There are two different kinds of left-hand sides in assignments:
  // simple variables (identifiers), or locations of a map
  [ContractClass(typeof(AssignLhsContracts))]
  public abstract class AssignLhs : Absy {
    // The type of the lhs is determined during typechecking
    public abstract Type Type {
      get;
    }
    // Determine the variable that is actually assigned in this lhs
    public abstract IdentifierExpr/*!*/ DeepAssignedIdentifier {
      get;
    }
    public abstract Variable DeepAssignedVariable {
      get;
    }

    public AssignLhs(IToken/*!*/ tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
    public abstract void Emit(TokenTextWriter/*!*/ stream);

    public abstract Expr/*!*/ AsExpr {
      get;
    }

    // transform away the syntactic sugar of map assignments and
    // determine an equivalent simple assignment
    internal abstract void AsSimpleAssignment(Expr/*!*/ rhs,
                                              out IdentifierExpr/*!*/ simpleLhs,
                                              out Expr/*!*/ simpleRhs);
  }
  [ContractClassFor(typeof(AssignLhs))]
  public abstract class AssignLhsContracts : AssignLhs {
    public AssignLhsContracts():base(null)
	{

	}public override IdentifierExpr DeepAssignedIdentifier {
      
      get {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
        throw new NotImplementedException();
      }
    }
    public override Expr AsExpr {
      get {
        Contract.Ensures(Contract.Result<Expr>() != null);
        throw new NotImplementedException();
      }

    }
    internal override void AsSimpleAssignment(Expr rhs, out IdentifierExpr simpleLhs, out Expr simpleRhs) {
      Contract.Requires(rhs != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleLhs) != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleRhs) != null);

      throw new NotImplementedException();
    }
  }

  public class SimpleAssignLhs : AssignLhs {
    public IdentifierExpr/*!*/ AssignedVariable;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(AssignedVariable != null);
    }


    public override Type Type {
      get {
        return AssignedVariable.Type;
      }
    }

    public override IdentifierExpr/*!*/ DeepAssignedIdentifier {
      get {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
        return AssignedVariable;
      }
    }

    public override Variable DeepAssignedVariable {
      get {
        return AssignedVariable.Decl;
      }
    }

    public SimpleAssignLhs(IToken tok, IdentifierExpr assignedVariable)
      : base(tok) {
      Contract.Requires(assignedVariable != null);
      Contract.Requires(tok != null);
      //base(tok);
      AssignedVariable = assignedVariable;
    }
    public override void Resolve(ResolutionContext rc) {
      
      AssignedVariable.Resolve(rc);
    }
    public override void Typecheck(TypecheckingContext tc) {
      
      AssignedVariable.Typecheck(tc);
    }
    public override void Emit(TokenTextWriter stream) {
      
      AssignedVariable.Emit(stream);
    }
    public override Expr/*!*/ AsExpr {
      get {
        Contract.Ensures(Contract.Result<Expr>() != null);

        return AssignedVariable;
      }
    }
    internal override void AsSimpleAssignment(Expr rhs,
                                              out IdentifierExpr/*!*/ simpleLhs,
                                              out Expr/*!*/ simpleRhs) {


      
      simpleLhs = AssignedVariable;
      simpleRhs = rhs;
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      

      return visitor.VisitSimpleAssignLhs(this);
    }
  }

  // A map-assignment-lhs (m[t1, t2, ...] := ...) is quite similar to
  // a map select expression, but it is cleaner to keep those two
  // things separate
  public class MapAssignLhs : AssignLhs {
    public AssignLhs/*!*/ Map;

    public List<Expr/*!*/>/*!*/ Indexes;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Map != null);
      Contract.Invariant(cce.NonNullElements(Indexes));
    }


    // The instantiation of type parameters of the map that is
    // determined during type checking.
    public TypeParamInstantiation TypeParameters = null;

    private Type TypeAttr = null;

    public override Type Type {
      get {
        return TypeAttr;
      }
    }

    public override IdentifierExpr/*!*/ DeepAssignedIdentifier {
      get {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);

        return Map.DeepAssignedIdentifier;
      }
    }

    public override Variable DeepAssignedVariable {
      get {
        return Map.DeepAssignedVariable;
      }
    }

    public MapAssignLhs(IToken tok, AssignLhs map, List<Expr/*!*/>/*!*/ indexes)
      : base(tok) {//BASEMOVEA
      //:base(tok);
      Contract.Requires(map != null);
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(indexes));

      Map = map;
      Indexes = indexes;
    }
    public override void Resolve(ResolutionContext rc) {
      
      Map.Resolve(rc);
      foreach (Expr/*!*/ e in Indexes) {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }
    }
    public override void Typecheck(TypecheckingContext tc) {
      
      Map.Typecheck(tc);
      foreach (Expr/*!*/ e in Indexes) {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }

      // we use the same typechecking code as in MapSelect
      ExprSeq/*!*/ selectArgs = new ExprSeq();
      foreach (Expr/*!*/ e in Indexes) {
        Contract.Assert(e != null);
        selectArgs.Add(e);
      }
      TypeParamInstantiation/*!*/ tpInsts;
      TypeAttr =
        MapSelect.Typecheck(cce.NonNull(Map.Type), Map,
                            selectArgs, out tpInsts, tc, tok, "map assignment");
      TypeParameters = tpInsts;
    }
    public override void Emit(TokenTextWriter stream) {
      
      Map.Emit(stream);
      stream.Write("[");
      string/*!*/ sep = "";
      foreach (Expr/*!*/ e in Indexes) {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }
      stream.Write("]");
    }
    public override Expr/*!*/ AsExpr {
      get {
        Contract.Ensures(Contract.Result<Expr>() != null);

        NAryExpr/*!*/ res = Expr.Select(Map.AsExpr, Indexes);
        Contract.Assert(res != null);
        res.TypeParameters = this.TypeParameters;
        return res;
      }
    }
    internal override void AsSimpleAssignment(Expr rhs,
                                              out IdentifierExpr/*!*/ simpleLhs,
                                              out Expr/*!*/ simpleRhs) { //Contract.Requires(rhs != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleLhs) != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleRhs) != null);
     
      NAryExpr/*!*/ newRhs = Expr.Store(Map.AsExpr, Indexes, rhs);
      Contract.Assert(newRhs != null);
      newRhs.TypeParameters = this.TypeParameters;
      Map.AsSimpleAssignment(newRhs, out simpleLhs, out simpleRhs);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitMapAssignLhs(this);
    }
  }

  /// <summary>
  /// A StateCmd is like an imperative-let binding around a sequence of commands.
  /// There is no user syntax for a StateCmd.  Instead, a StateCmd is only used
  /// temporarily during the desugaring phase inside the VC generator.
  /// </summary>
  public class StateCmd : Cmd {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Locals != null);
      Contract.Invariant(Cmds != null);
    }

    public /*readonly, except for the StandardVisitor*/ VariableSeq/*!*/ Locals;
    public /*readonly, except for the StandardVisitor*/ CmdSeq/*!*/ Cmds;

    public StateCmd(IToken tok, VariableSeq/*!*/ locals, CmdSeq/*!*/ cmds)
      : base(tok) {
      Contract.Requires(locals != null);
      Contract.Requires(cmds != null);
      Contract.Requires(tok != null);
      this.Locals = locals;
      this.Cmds = cmds;
      // base(tok);
    }

    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      rc.PushVarContext();
      foreach (Variable/*!*/ v in Locals) {
        Contract.Assert(v != null);
        rc.AddVariable(v, false);
      }
      foreach (Cmd/*!*/ cmd in Cmds) {
        Contract.Assert(cmd != null);
        cmd.Resolve(rc);
      }
      rc.PopVarContext();
    }

    public override void AddAssignedVariables(VariableSeq vars) {
      //Contract.Requires(vars != null);
      VariableSeq/*!*/ vs = new VariableSeq();
      foreach (Cmd/*!*/ cmd in this.Cmds) {
        Contract.Assert(cmd != null);
        cmd.AddAssignedVariables(vs);
      }
      System.Collections.Hashtable/*!*/ localsSet = new System.Collections.Hashtable();
      foreach (Variable/*!*/ local in this.Locals) {
        Contract.Assert(local != null);
        localsSet[local] = bool.TrueString;
      }
      foreach (Variable/*!*/ v in vs) {
        Contract.Assert(v != null);
        if (!localsSet.ContainsKey(v)) {
          vars.Add(v);
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      foreach (Cmd/*!*/ cmd in Cmds) {
        Contract.Assert(cmd != null);
        cmd.Typecheck(tc);
      }
    }

    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.WriteLine(this, level, "{");
      foreach (Variable/*!*/ v in Locals) {
        Contract.Assert(v != null);
        v.Emit(stream, level + 1);
      }
      foreach (Cmd/*!*/ c in Cmds) {
        Contract.Assert(c != null);
        c.Emit(stream, level + 1);
      }
      stream.WriteLine(level, "}");
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitStateCmd(this);
    }
  }
  [ContractClass(typeof(SugaredCmdContracts))]
  abstract public class SugaredCmd : Cmd {
    private Cmd desugaring;  // null until desugared

    public SugaredCmd(IToken/*!*/ tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }

    public Cmd/*!*/ Desugaring {
      get {
        Contract.Ensures(Contract.Result<Cmd>() != null);

        if (desugaring == null) {
          desugaring = ComputeDesugaring();
        }
        return desugaring;
      }
    }
    protected abstract Cmd/*!*/ ComputeDesugaring();

    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      if (CommandLineOptions.Clo.PrintDesugarings) {
        stream.WriteLine(this, level, "/*** desugaring:");
        Desugaring.Emit(stream, level);
        stream.WriteLine(level, "**** end desugaring */");
      }
    }
  }
  [ContractClassFor(typeof(SugaredCmd))]
  public abstract class SugaredCmdContracts : SugaredCmd {
    public SugaredCmdContracts() :base(null){

    }
    protected override Cmd ComputeDesugaring() {
      Contract.Ensures(Contract.Result<Cmd>() != null);

      throw new NotImplementedException();
    }
  }

  public abstract class CallCommonality : SugaredCmd {
    public QKeyValue Attributes;

    protected CallCommonality(IToken tok, QKeyValue kv)
      : base(tok) {
      Contract.Requires(tok != null);
      //base(tok);
      Attributes = kv;
    }

    protected enum TempVarKind {
      Formal,
      Old,
      Bound
    }

    // We have to give the type explicitly, because the type of the formal "likeThisOne" can contain type variables
    protected Variable CreateTemporaryVariable(VariableSeq tempVars, Variable likeThisOne, Type ty, TempVarKind kind) {
      Contract.Requires(ty != null);
      Contract.Requires(likeThisOne != null);
      Contract.Requires(tempVars != null);
      Contract.Ensures(Contract.Result<Variable>() != null);
      string/*!*/ tempNamePrefix;
      switch (kind) {
        case TempVarKind.Formal:
          tempNamePrefix = "formal@";
          break;
        case TempVarKind.Old:
          tempNamePrefix = "old@";
          break;
        case TempVarKind.Bound:
          tempNamePrefix = "forall@";
          break;
        default: {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          }  // unexpected kind
      }
      TypedIdent ti = likeThisOne.TypedIdent;
      TypedIdent newTi = new TypedIdent(ti.tok, "call" + UniqueId + tempNamePrefix + ti.Name, ty);
      Variable/*!*/ v;
      if (kind == TempVarKind.Bound) {
        v = new BoundVariable(likeThisOne.tok, newTi);
      } else {
        v = new LocalVariable(likeThisOne.tok, newTi);
        tempVars.Add(v);
      }
      return v;
    }
  }

  public class CallCmd : CallCommonality, IPotentialErrorNode {
    public string/*!*/ callee { get; private set; }
    public Procedure Proc;

    // Element of the following lists can be null, which means that
    // the call happens with * as these parameters
    public List<Expr>/*!*/ Ins;
    public List<IdentifierExpr>/*!*/ Outs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(callee != null);
      Contract.Invariant(Ins != null);
      Contract.Invariant(Outs != null);
    }

    //public Lattice.Element StateAfterCall;

    // The instantiation of type parameters that is determined during
    // type checking
    public TypeParamInstantiation TypeParameters = null;

    // TODO: convert to use generics
    private object errorData;
    public object ErrorData {
      get {
        return errorData;
      }
      set {
        errorData = value;
      }
    }
    public static List<T> toList<T>(PureCollections.Sequence seq) {
      List<T> toRet = new List<T>();
      foreach (T t in seq)
        if (t != null)
          toRet.Add(t);
      return toRet;
    }
    public CallCmd(IToken tok, string callee, ExprSeq ins, IdentifierExprSeq outs)
      : this(tok, callee, toList<Expr>(ins), toList<IdentifierExpr>(outs)) {
      Contract.Requires(outs != null);
      Contract.Requires(ins != null);
      Contract.Requires(callee != null);
      Contract.Requires(tok != null);
      //List<Expr>/*!*/ insList = new List<Expr>();
      //List<IdentifierExpr>/*!*/ outsList = new List<IdentifierExpr>();
      //foreach (Expr e in ins)
      //  if(e!=null)
      //  insList.Add(e);
      //foreach (IdentifierExpr e in outs)
      //  if(e!=null)
      //  outsList.Add(e);
      //this(tok, callee, insList, outsList);

    }
    public CallCmd(IToken tok, string callee, List<Expr> ins, List<IdentifierExpr> outs)
      : base(tok, null) {//BASEMOVE DANGER
      Contract.Requires(outs != null);
      Contract.Requires(ins != null);
      Contract.Requires(callee != null);
      Contract.Requires(tok != null);
      //base(tok, null);
      this.callee = callee;
      this.Ins = ins;
      this.Outs = outs;
    }
    public CallCmd(IToken tok, string callee, List<Expr> ins, List<IdentifierExpr> outs, QKeyValue kv)
      : base(tok, kv) {//BASEMOVE DANGER
      Contract.Requires(outs != null);
      Contract.Requires(ins != null);
      Contract.Requires(callee != null);
      Contract.Requires(tok != null);
      //base(tok, kv);
      this.callee = callee;
      this.Ins = ins;
      this.Outs = outs;
    }

    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "call ");
      EmitAttributes(stream, Attributes);
      string sep = "";
      if (Outs.Count > 0) {
        foreach (Expr arg in Outs) {
          stream.Write(sep);
          sep = ", ";
          if (arg == null) {
            stream.Write("*");
          } else {
            arg.Emit(stream);
          }
        }
        stream.Write(" := ");
      }
      stream.Write(TokenTextWriter.SanitizeIdentifier(callee));
      stream.Write("(");
      sep = "";
      foreach (Expr arg in Ins) {
        stream.Write(sep);
        sep = ", ";
        if (arg == null) {
          stream.Write("*");
        } else {
          arg.Emit(stream);
        }
      }
      stream.WriteLine(");");
      base.Emit(stream, level);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      if (Proc != null) {
        // already resolved
        return;
      }
      ResolveAttributes(Attributes, rc);
      Proc = rc.LookUpProcedure(callee) as Procedure;
      if (Proc == null) {
        rc.Error(this, "call to undeclared procedure: {0}", callee);
      }
      foreach (Expr e in Ins) {
        if (e != null) {
          e.Resolve(rc);
        }
      }
      Set/*<Variable>*/ actualOuts = new Set/*<Variable>*/ (Outs.Count);
      foreach (IdentifierExpr ide in Outs) {
        if (ide != null) {
          ide.Resolve(rc);
          if (ide.Decl != null) {
            if (actualOuts[ide.Decl]) {
              rc.Error(this, "left-hand side of call command contains variable twice: {0}", ide.Name);
            } else {
              actualOuts.Add(ide.Decl);
            }
          }
        }
      }

      if (Proc == null)
        return;

      // first make sure that the right number of parameters is given
      // (a similar check is in CheckArgumentTypes, but we are not
      // able to call this method because it cannot cope with Ins/Outs
      // that are null)
      if (Ins.Count != Proc.InParams.Length) {
        rc.Error(this.tok,
                 "wrong number of arguments in call to {0}: {1}",
                 callee, Ins.Count);
        return;
      }
      if (Outs.Count != Proc.OutParams.Length) {
        rc.Error(this.tok,
                 "wrong number of result variables in call to {0}: {1}",
                 callee, Outs.Count);
        return;
      }
      if (QKeyValue.FindBoolAttribute(this.Attributes, "async")) {
        if (Proc.OutParams.Length > 1) {
          rc.Error(this.tok, "a procedure called asynchronously can have at most one output parameter");
          return;
        }
      }

      // Check that type parameters can be determined using the given
      // actual i/o arguments. This is done already during resolution
      // because CheckBoundVariableOccurrences needs a resolution
      // context
      TypeSeq/*!*/ formalInTypes = new TypeSeq();
      TypeSeq/*!*/ formalOutTypes = new TypeSeq();
      for (int i = 0; i < Ins.Count; ++i)
        if (Ins[i] != null)
          formalInTypes.Add(cce.NonNull(Proc.InParams[i]).TypedIdent.Type);
      for (int i = 0; i < Outs.Count; ++i)
        if (Outs[i] != null)
          formalOutTypes.Add(cce.NonNull(Proc.OutParams[i]).TypedIdent.Type);

      // we need to bind the type parameters for this
      // (this is expected by CheckBoundVariableOccurrences)
      int previousTypeBinderState = rc.TypeBinderState;
      try {
        foreach (TypeVariable/*!*/ v in Proc.TypeParameters) {
          Contract.Assert(v != null);
          rc.AddTypeBinder(v);
        }
        Type.CheckBoundVariableOccurrences(Proc.TypeParameters,
                                           formalInTypes, formalOutTypes,
                                           this.tok, "types of given arguments",
                                           rc);
      } finally {
        rc.TypeBinderState = previousTypeBinderState;
      }
    }

    public override void AddAssignedVariables(VariableSeq vars) {
      //Contract.Requires(vars != null);
      foreach (IdentifierExpr e in Outs) {
        if (e != null) {
          vars.Add(e.Decl);
        }
      }
      Contract.Assume(this.Proc != null);
      foreach (IdentifierExpr/*!*/ e in this.Proc.Modifies) {
        Contract.Assert(e != null);
        vars.Add(e.Decl);
      }
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      Contract.Assume(this.Proc != null);  // we assume the CallCmd has been successfully resolved before calling this Typecheck method

      TypecheckAttributes(Attributes, tc);

      // typecheck in-parameters
      foreach (Expr e in Ins)
        if (e != null)
          e.Typecheck(tc);
      foreach (Expr e in Outs)
        if (e != null)
          e.Typecheck(tc);
      this.CheckAssignments(tc);

      TypeSeq/*!*/ formalInTypes = new TypeSeq();
      TypeSeq/*!*/ formalOutTypes = new TypeSeq();
      ExprSeq/*!*/ actualIns = new ExprSeq();
      IdentifierExprSeq/*!*/ actualOuts = new IdentifierExprSeq();
      for (int i = 0; i < Ins.Count; ++i) {
        if (Ins[i] != null) {
          formalInTypes.Add(cce.NonNull(Proc.InParams[i]).TypedIdent.Type);
          actualIns.Add(Ins[i]);
        }
      }
      for (int i = 0; i < Outs.Count; ++i) {
        if (Outs[i] != null) {
          formalOutTypes.Add(cce.NonNull(Proc.OutParams[i]).TypedIdent.Type);
          actualOuts.Add(Outs[i]);
        }
      }

      if (QKeyValue.FindBoolAttribute(this.Attributes, "async") && Outs.Count > 0) {
        Type returnType = cce.NonNull(Outs[0]).ShallowType;
        if (!returnType.Equals(Type.Int) && !returnType.Equals(Type.GetBvType(32))) {
          tc.Error(this.tok, "the return from an asynchronous call should be either int or bv32");
          return;
        }
      }

      // match actuals with formals
      List<Type/*!*/>/*!*/ actualTypeParams;
      Type.CheckArgumentTypes(Proc.TypeParameters,
                              out actualTypeParams,
                              formalInTypes, actualIns,
                              formalOutTypes, actualOuts,
                              this.tok,
                              "call to " + callee,
                              tc);
      Contract.Assert(cce.NonNullElements(actualTypeParams));
      TypeParameters = SimpleTypeParamInstantiation.From(Proc.TypeParameters,
                                                         actualTypeParams);
    }

    private IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ TypeParamSubstitution() {
      Contract.Ensures(cce.NonNullDictionaryAndValues(Contract.Result<IDictionary<TypeVariable, Type>>()));
      Contract.Assume(TypeParameters != null);
      IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ res = new Dictionary<TypeVariable/*!*/, Type/*!*/>();
      foreach (TypeVariable/*!*/ v in TypeParameters.FormalTypeParams) {
        Contract.Assert(v != null);
        res.Add(v, TypeParameters[v]);
      }
      return res;
    }

    protected override Cmd ComputeDesugaring() {
      Contract.Ensures(Contract.Result<Cmd>() != null);
      CmdSeq newBlockBody = new CmdSeq();
      Hashtable /*Variable -> Expr*/ substMap = new Hashtable/*Variable -> Expr*/();
      Hashtable /*Variable -> Expr*/ substMapOld = new Hashtable/*Variable -> Expr*/();
      Hashtable /*Variable -> Expr*/ substMapBound = new Hashtable/*Variable -> Expr*/();
      VariableSeq/*!*/ tempVars = new VariableSeq();

      // proc P(ins) returns (outs)
      //   requires Pre
      //   //modifies frame
      //   ensures Post
      //
      // call aouts := P(ains)

      // ins    : formal in parameters of procedure
      // frame  : a list of global variables from the modifies clause
      // outs   : formal out parameters of procedure
      // ains   : actual in arguments passed to call
      // aouts  : actual variables assigned to from call
      // cins   : new variables created just for this call, one per ains
      // cframe : new variables created just for this call, to keep track of OLD values
      // couts  : new variables created just for this call, one per aouts
      // WildcardVars : new variables created just for this call, one per null in ains

      #region Create cins; each one is an incarnation of the corresponding in parameter
      VariableSeq/*!*/ cins = new VariableSeq();
      VariableSeq wildcardVars = new VariableSeq();
      Contract.Assume(this.Proc != null);
      for (int i = 0; i < this.Proc.InParams.Length; ++i) {
        Variable/*!*/ param = cce.NonNull(this.Proc.InParams[i]);
        bool isWildcard = this.Ins[i] == null;

        Type/*!*/ actualType;
        if (isWildcard)
          actualType = param.TypedIdent.Type.Substitute(TypeParamSubstitution());
        else
          // during type checking, we have ensured that the type of the actual
          // parameter Ins[i] is correct, so we can use it here
          actualType = cce.NonNull(cce.NonNull(Ins[i]).Type);

        Variable cin = CreateTemporaryVariable(tempVars, param, actualType,
                                               TempVarKind.Formal);
        cins.Add(cin);
        IdentifierExpr ie = new IdentifierExpr(cin.tok, cin);
        substMap.Add(param, ie);
        if (isWildcard) {
          cin = CreateTemporaryVariable(tempVars, param,
                                        actualType, TempVarKind.Bound);
          wildcardVars.Add(cin);
          ie = new IdentifierExpr(cin.tok, cin);
        }
        substMapBound.Add(param, ie);
      }
      #endregion
      #region call aouts := P(ains) becomes: (open outlining one level to see)
      #region cins := ains (or havoc cin when ain is null)
      for (int i = 0, n = this.Ins.Count; i < n; i++) {
        IdentifierExpr/*!*/ cin_exp = new IdentifierExpr(cce.NonNull(cins[i]).tok, cce.NonNull(cins[i]));
        Contract.Assert(cin_exp != null);
        if (this.Ins[i] != null) {
          AssignCmd assign = Cmd.SimpleAssign(Token.NoToken, cin_exp, cce.NonNull(this.Ins[i]));
          newBlockBody.Add(assign);
        } else {
          IdentifierExprSeq/*!*/ ies = new IdentifierExprSeq();
          ies.Add(cin_exp);
          HavocCmd havoc = new HavocCmd(Token.NoToken, ies);
          newBlockBody.Add(havoc);
        }
      }
      #endregion

      #region assert (exists wildcardVars :: Pre[ins := cins])
      Substitution s = Substituter.SubstitutionFromHashtable(substMapBound);
      bool hasWildcard = (wildcardVars.Length != 0);
      Expr preConjunction = null;
      for (int i = 0; i < this.Proc.Requires.Length; i++) {
        Requires/*!*/ req = cce.NonNull(this.Proc.Requires[i]);
        if (!req.Free) {
          if (hasWildcard) {
            Expr pre = Substituter.Apply(s, req.Condition);
            if (preConjunction == null) {
              preConjunction = pre;
            } else {
              preConjunction = Expr.And(preConjunction, pre);
            }
          } else {
            Requires/*!*/ reqCopy = (Requires/*!*/)cce.NonNull(req.Clone());
            reqCopy.Condition = Substituter.Apply(s, req.Condition);
            AssertCmd/*!*/ a = new AssertRequiresCmd(this, reqCopy);
            Contract.Assert(a != null);
            a.ErrorDataEnhanced = reqCopy.ErrorDataEnhanced;
            newBlockBody.Add(a);
          }
        }
      }
      if (hasWildcard) {
        if (preConjunction == null) {
          preConjunction = Expr.True;
        }
        Expr/*!*/ expr = new ExistsExpr(tok, wildcardVars, preConjunction);
        Contract.Assert(expr != null);
        AssertCmd/*!*/ a = new AssertCmd(tok, expr);
        Contract.Assert(a != null);
        a.ErrorDataEnhanced = AssertCmd.GenerateBoundVarMiningStrategy(expr);
        newBlockBody.Add(a);
      }
      #endregion

      #region assume Pre[ins := cins] with formal paramters
      if (hasWildcard) {
        s = Substituter.SubstitutionFromHashtable(substMap);
        for (int i = 0; i < this.Proc.Requires.Length; i++) {
          Requires/*!*/ req = cce.NonNull(this.Proc.Requires[i]);
          if (!req.Free) {
            Requires/*!*/ reqCopy = (Requires/*!*/)cce.NonNull(req.Clone());
            reqCopy.Condition = Substituter.Apply(s, req.Condition);
            AssumeCmd/*!*/ a = new AssumeCmd(tok, reqCopy.Condition);
            Contract.Assert(a != null);
            newBlockBody.Add(a);
          }
        }
      }
      #endregion

      #region cframe := frame (to hold onto frame values in case they are referred to in the postcondition)
      IdentifierExprSeq havocVarExprs = new IdentifierExprSeq();

      foreach (IdentifierExpr/*!*/ f in this.Proc.Modifies) {
        Contract.Assert(f != null);
        Contract.Assume(f.Decl != null);
        Contract.Assert(f.Type != null);
        Variable v = CreateTemporaryVariable(tempVars, f.Decl, f.Type, TempVarKind.Old);
        IdentifierExpr v_exp = new IdentifierExpr(v.tok, v);
        substMapOld.Add(f.Decl, v_exp);  // this assumes no duplicates in this.Proc.Modifies
        AssignCmd assign = Cmd.SimpleAssign(f.tok, v_exp, f);
        newBlockBody.Add(assign);

        // fra
        if (!havocVarExprs.Has(f))
          havocVarExprs.Add(f);
      }
      #endregion
      #region Create couts
      VariableSeq/*!*/ couts = new VariableSeq();
      for (int i = 0; i < this.Proc.OutParams.Length; ++i) {
        Variable/*!*/ param = cce.NonNull(this.Proc.OutParams[i]);
        bool isWildcard = this.Outs[i] == null;

        Type/*!*/ actualType;
        if (isWildcard)
          actualType = param.TypedIdent.Type.Substitute(TypeParamSubstitution());
        else
          // during type checking, we have ensured that the type of the actual
          // out parameter Outs[i] is correct, so we can use it here
          actualType = cce.NonNull(cce.NonNull(Outs[i]).Type);

        Variable cout = CreateTemporaryVariable(tempVars, param, actualType,
                                                TempVarKind.Formal);
        couts.Add(cout);
        IdentifierExpr ie = new IdentifierExpr(cout.tok, cout);
        substMap.Add(param, ie);

        if (!havocVarExprs.Has(ie))
          havocVarExprs.Add(ie);
      }
      // add the where clauses, now that we have the entire substitution map
      foreach (Variable/*!*/ param in this.Proc.OutParams) {
        Contract.Assert(param != null);
        Expr w = param.TypedIdent.WhereExpr;
        if (w != null) {
          IdentifierExpr ie = (IdentifierExpr/*!*/)cce.NonNull(substMap[param]);
          Contract.Assert(ie.Decl != null);
          ie.Decl.TypedIdent.WhereExpr = Substituter.Apply(Substituter.SubstitutionFromHashtable(substMap), w);
        }
      }
      #endregion

      #region havoc frame, couts
      // pass on this's token
      HavocCmd hc = new HavocCmd(this.tok, havocVarExprs);
      newBlockBody.Add(hc);
      #endregion

      #region assume Post[ins, outs, old(frame) := cins, couts, cframe]
      Substitution s2 = Substituter.SubstitutionFromHashtable(substMap);
      Substitution s2old = Substituter.SubstitutionFromHashtable(substMapOld);
      foreach (Ensures/*!*/ e in this.Proc.Ensures) {
        Contract.Assert(e != null);
        Expr copy = Substituter.ApplyReplacingOldExprs(s2, s2old, e.Condition);
        AssumeCmd assume = new AssumeCmd(this.tok, copy);
        #region stratified inlining support
        if (QKeyValue.FindBoolAttribute(e.Attributes, "si_fcall"))
        {
            assume.Attributes = Attributes;
        }
        #endregion
        newBlockBody.Add(assume);
      }
      #endregion

      #region aouts := couts
      for (int i = 0, n = this.Outs.Count; i < n; i++) {
        if (this.Outs[i] != null) {
          Variable/*!*/ param_i = cce.NonNull(this.Proc.OutParams[i]);
          Expr/*!*/ cout_exp = new IdentifierExpr(cce.NonNull(couts[i]).tok, cce.NonNull(couts[i]));
          Contract.Assert(cout_exp != null);
          AssignCmd assign = Cmd.SimpleAssign(param_i.tok, cce.NonNull(this.Outs[i]), cout_exp);
          newBlockBody.Add(assign);
        }
      }
      #endregion
      #endregion

      return new StateCmd(this.tok, tempVars, newBlockBody);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitCallCmd(this);
    }
  }

  public class CallForallCmd : CallCommonality {
    string/*!*/ callee;
    public Procedure Proc;
    public List<Expr>/*!*/ Ins;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(callee != null);
      Contract.Invariant(Ins != null);
    }


    // the types of the formal in-parameters after instantiating all
    // type variables whose value could be inferred using the given
    // actual non-wildcard arguments
    public TypeSeq InstantiatedTypes;

    public CallForallCmd(IToken tok, string callee, List<Expr> ins)
      : base(tok, null) {//BASEMOVEA
      Contract.Requires(ins != null);
      Contract.Requires(callee != null);
      Contract.Requires(tok != null);
      //:base(tok, null);
      this.callee = callee;
      this.Ins = ins;
    }
    public CallForallCmd(IToken tok, string callee, List<Expr> ins, QKeyValue kv)
      : base(tok, kv) {//BASEMOVEA
      Contract.Requires(ins != null);
      Contract.Requires(callee != null);
      Contract.Requires(tok != null);
      //:base(tok, kv);
      this.callee = callee;
      this.Ins = ins;
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "call ");
      EmitAttributes(stream, Attributes);
      stream.Write("forall ");
      stream.Write(TokenTextWriter.SanitizeIdentifier(callee));
      stream.Write("(");
      string sep = "";
      foreach (Expr arg in Ins) {
        stream.Write(sep);
        sep = ", ";
        if (arg == null) {
          stream.Write("*");
        } else {
          arg.Emit(stream);
        }
      }
      stream.WriteLine(");");
      base.Emit(stream, level);
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      if (Proc != null) {
        // already resolved
        return;
      }
      ResolveAttributes(Attributes, rc);
      Proc = rc.LookUpProcedure(callee) as Procedure;
      if (Proc == null) {
        rc.Error(this, "call to undeclared procedure: {0}", callee);
      }
      foreach (Expr e in Ins) {
        if (e != null) {
          e.Resolve(rc);
        }
      }
    }
    public override void AddAssignedVariables(VariableSeq vars) {
      //Contract.Requires(vars != null);
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      TypecheckAttributes(Attributes, tc);
      // typecheck in-parameters
      foreach (Expr e in Ins) {
        if (e != null) {
          e.Typecheck(tc);
        }
      }

      if (this.Proc == null) {
        // called procedure didn't resolve, so bug out
        return;
      }

      // match actuals with formals
      if (Ins.Count != Proc.InParams.Length) {
        tc.Error(this, "wrong number of in-parameters in call: {0}", callee);
      } else {
        // determine the lists of formal and actual arguments that need
        // to be matched (stars are left out)
        TypeSeq/*!*/ formalTypes = new TypeSeq();
        ExprSeq/*!*/ actualArgs = new ExprSeq();
        for (int i = 0; i < Ins.Count; i++)
          if (Ins[i] != null) {
            formalTypes.Add(cce.NonNull(Proc.InParams[i]).TypedIdent.Type);
            actualArgs.Add(Ins[i]);
          }
        IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ subst =
          Type.MatchArgumentTypes(Proc.TypeParameters,
                                  formalTypes, actualArgs, null, null,
                                  "call forall to " + callee, tc);
        Contract.Assert(cce.NonNullDictionaryAndValues(subst));

        InstantiatedTypes = new TypeSeq();
        foreach (Variable/*!*/ var in Proc.InParams) {
          Contract.Assert(var != null);
          InstantiatedTypes.Add(var.TypedIdent.Type.Substitute(subst));
        }
      }

      //      if (Proc.OutParams.Length != 0)
      //      {
      //        tc.Error(this, "call forall is allowed only on procedures with no out-parameters: {0}", callee);
      //      }

      if (Proc.Modifies.Length != 0) {
        tc.Error(this, "call forall is allowed only on procedures with no modifies clause: {0}", callee);
      }
    }

    protected override Cmd ComputeDesugaring() {
      Contract.Ensures(Contract.Result<Cmd>() != null);
      CmdSeq newBlockBody = new CmdSeq();
      Hashtable /*Variable -> Expr*/ substMap = new Hashtable/*Variable -> Expr*/();
      VariableSeq/*!*/ tempVars = new VariableSeq();

      // proc P(ins) returns ()
      //   requires Pre;
      //   //modifies ;
      //   ensures Post;
      //
      // call forall P(ains);

      // ins    : formal in-parameters of procedure
      // ains   : actual in-arguments passed to call
      // cins   : new variables created just for this call, one per ains
      // wildcardVars : the bound variables to be wrapped up in a quantification

      #region Create cins; each one is an incarnation of the corresponding in parameter
      VariableSeq cins = new VariableSeq();
      VariableSeq wildcardVars = new VariableSeq();
      Contract.Assume(this.Proc != null);
      for (int i = 0, n = this.Proc.InParams.Length; i < n; i++) {
        Variable param = cce.NonNull(this.Proc.InParams[i]);
        Type/*!*/ paramType = cce.NonNull(this.InstantiatedTypes)[i]; // might contain type variables
        bool isWildcard = this.Ins[i] == null;
        Variable cin = CreateTemporaryVariable(tempVars, param, paramType,
                                               isWildcard ? TempVarKind.Bound : TempVarKind.Formal);
        if (isWildcard) {
          cins.Add(null);
          wildcardVars.Add(cin);
        } else {
          cins.Add(cin);
        }
        IdentifierExpr ie = new IdentifierExpr(cin.tok, cin);
        substMap.Add(param, ie);
      }
      #endregion

      #region call forall P(ains) becomes: (open outlining one level to see)
      #region cins := ains
      for (int i = 0, n = this.Ins.Count; i < n; i++) {
        if (this.Ins[i] != null) {
          IdentifierExpr/*!*/ cin_exp = new IdentifierExpr(cce.NonNull(cins[i]).tok, cce.NonNull(cins[i]));
          AssignCmd assign = Cmd.SimpleAssign(Token.NoToken, cin_exp, cce.NonNull(this.Ins[i]));
          newBlockBody.Add(assign);
        }
      }
      #endregion

      #region assert Pre[ins := cins]
      Substitution s = Substituter.SubstitutionFromHashtable(substMap);
      Expr preConjunction = null;
      for (int i = 0; i < this.Proc.Requires.Length; i++) {
        Requires/*!*/ req = cce.NonNull(this.Proc.Requires[i]);
        if (!req.Free) {
          Expr pre = Substituter.Apply(s, req.Condition);
          if (preConjunction == null) {
            preConjunction = pre;
          } else {
            preConjunction = Expr.And(preConjunction, pre);
          }
        }
      }
      if (preConjunction == null) {
        preConjunction = Expr.True;
      }
      #endregion

      #region Create couts
      VariableSeq/*!*/ couts = new VariableSeq();
      foreach (Variable/*!*/ param in this.Proc.OutParams) {
        Contract.Assert(param != null);
        Variable cout = CreateTemporaryVariable(tempVars, param,
                                                param.TypedIdent.Type, TempVarKind.Bound);
        couts.Add(cout);
        IdentifierExpr ie = new IdentifierExpr(cout.tok, cout);
        substMap.Add(param, ie);
      }
      // add the where clauses, now that we have the entire substitution map
      foreach (Variable/*!*/ param in this.Proc.OutParams) {
        Contract.Assert(param != null);
        Expr w = param.TypedIdent.WhereExpr;
        if (w != null) {
          IdentifierExpr ie = (IdentifierExpr)cce.NonNull(substMap[param]);
          Contract.Assert(ie.Decl != null);
          ie.Decl.TypedIdent.WhereExpr = Substituter.Apply(Substituter.SubstitutionFromHashtable(substMap), w);
        }
      }
      #endregion

      #region assume Post[ins := cins]
      s = Substituter.SubstitutionFromHashtable(substMap);
      Expr postConjunction = null;
      foreach (Ensures/*!*/ e in this.Proc.Ensures) {
        Contract.Assert(e != null);
        Expr post = Substituter.Apply(s, e.Condition);
        if (postConjunction == null) {
          postConjunction = post;
        } else {
          postConjunction = Expr.And(postConjunction, post);
        }
      }
      if (postConjunction == null) {
        postConjunction = Expr.True;
      }
      #endregion

      #region assume (forall wildcardVars :: Pre ==> Post);
      Expr body = postConjunction;
      if (couts.Length > 0) {
        body = new ExistsExpr(tok, couts, body);
      }
      body = Expr.Imp(preConjunction, body);
      if (wildcardVars.Length != 0) {
        TypeVariableSeq/*!*/ typeParams = Type.FreeVariablesIn(cce.NonNull(InstantiatedTypes));
        body = new ForallExpr(tok, typeParams, wildcardVars, body);
      }
      newBlockBody.Add(new AssumeCmd(tok, body));
      #endregion
      #endregion

      return new StateCmd(this.tok, tempVars, newBlockBody);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitCallForallCmd(this);
    }
  }

  public abstract class PredicateCmd : Cmd {
    public QKeyValue Attributes;
    public /*readonly--except in StandardVisitor*/ Expr/*!*/ Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public PredicateCmd(IToken/*!*/ tok, Expr/*!*/ expr)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
    }
    public PredicateCmd(IToken/*!*/ tok, Expr/*!*/ expr, QKeyValue kv)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
      Attributes = kv;
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      Expr.Resolve(rc);
    }
    public override void AddAssignedVariables(VariableSeq vars) {
      //Contract.Requires(vars != null);
    }
  }

  public abstract class MiningStrategy {
    // abstract class to bind all MiningStrategys, i.e., all types of enhanced error data
    // types together
  }

  public class ListOfMiningStrategies : MiningStrategy {
    public List<MiningStrategy>/*!*/ msList;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(msList != null);
    }


    public ListOfMiningStrategies(List<MiningStrategy> l) {
      Contract.Requires(l != null);
      this.msList = l;
    }
  }

  public class EEDTemplate : MiningStrategy {
    public string/*!*/ reason;
    public List<Expr/*!*/>/*!*/ exprList;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(reason != null);
      Contract.Invariant(cce.NonNullElements(exprList));
    }


    public EEDTemplate(string reason, List<Expr/*!*/>/*!*/ exprList) {
      Contract.Requires(reason != null);
      Contract.Requires(cce.NonNullElements(exprList));
      this.reason = reason;
      this.exprList = exprList;
    }
  }

  public class AssertCmd : PredicateCmd, IPotentialErrorNode {
    public Expr OrigExpr;
    public Hashtable /*Variable -> Expr*/ IncarnationMap;

    // TODO: convert to use generics
    private object errorData;
    public object ErrorData {
      get {
        return errorData;
      }
      set {
        errorData = value;
      }
    }

    public string ErrorMessage {
      get {
        return QKeyValue.FindStringAttribute(Attributes, "msg");
      }
    }

    private MiningStrategy errorDataEnhanced;
    public MiningStrategy ErrorDataEnhanced {
      get {
        return errorDataEnhanced;
      }
      set {
        errorDataEnhanced = value;
      }
    }

    public AssertCmd(IToken/*!*/ tok, Expr/*!*/ expr)
      : base(tok, expr) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      errorDataEnhanced = GenerateBoundVarMiningStrategy(expr);
    }

    public AssertCmd(IToken/*!*/ tok, Expr/*!*/ expr, QKeyValue kv)
      : base(tok, expr, kv) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      errorDataEnhanced = GenerateBoundVarMiningStrategy(expr);
    }

    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "assert ");
      EmitAttributes(stream, Attributes);
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      ResolveAttributes(Attributes, rc);
      base.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      TypecheckAttributes(Attributes, tc);
      Expr.Typecheck(tc);
      Contract.Assert(Expr.Type != null);  // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool)) {
        tc.Error(this, "an asserted expression must be of type bool (got: {0})", Expr.Type);
      }
    }

    public static MiningStrategy GenerateBoundVarMiningStrategy(Expr expr) {
      Contract.Requires(expr != null);
      List<MiningStrategy> l = new List<MiningStrategy>();
      if (expr != null) {
        l = GenerateBoundVarListForMining(expr, l);
      }
      return new ListOfMiningStrategies(l);
    }

    public static List<MiningStrategy>/*!*/ GenerateBoundVarListForMining(Expr expr, List<MiningStrategy> l) {
      Contract.Requires(l != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<MiningStrategy>>() != null);

      // go through the origExpr and identify all bound variables in the AST.
      if (expr is LiteralExpr || expr is IdentifierExpr) {
        //end recursion
      } else if (expr is NAryExpr) {
        NAryExpr e = (NAryExpr)expr;
        foreach (Expr/*!*/ arg in e.Args) {
          Contract.Assert(arg != null);
          l = GenerateBoundVarListForMining(arg, l);
        }
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        l = GenerateBoundVarListForMining(e.Expr, l);
      } else if (expr is QuantifierExpr) {
        QuantifierExpr qe = (QuantifierExpr)expr;
        VariableSeq vs = qe.Dummies;
        foreach (Variable/*!*/ x in vs) {
          Contract.Assert(x != null);
          string name = x.Name;
          if (name.StartsWith("^")) {
            name = name.Substring(1);
            List<Expr> exprList = new List<Expr>();
            exprList.Add(new IdentifierExpr(Token.NoToken, x.ToString(), x.TypedIdent.Type));
            MiningStrategy eed = new EEDTemplate("The bound variable " + name + " has the value {0}.", exprList);
            l.Add(eed);
          }
        }
        l = GenerateBoundVarListForMining(qe.Body, l);
      }
      return l;
    }


    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAssertCmd(this);
    }
  }

  // An AssertCmd that is a loop invariant check before the loop iteration starts
  public class LoopInitAssertCmd : AssertCmd {
    public LoopInitAssertCmd(IToken/*!*/ tok, Expr/*!*/ expr)
      : base(tok, expr) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }
  }

  // An AssertCmd that is a loop invariant check to maintain the invariant after iteration
  public class LoopInvMaintainedAssertCmd : AssertCmd {
    public LoopInvMaintainedAssertCmd(IToken/*!*/ tok, Expr/*!*/ expr)
      : base(tok, expr) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }
  }

  /// <summary>
  /// An AssertCmd that is introduced in translation from the requires on a call.
  /// </summary>
  public class AssertRequiresCmd : AssertCmd {
    public CallCmd/*!*/ Call;
    public Requires/*!*/ Requires;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Call != null);
      Contract.Invariant(Requires != null);
    }


    public AssertRequiresCmd(CallCmd/*!*/ call, Requires/*!*/ requires)
      : base(call.tok, requires.Condition) {
      Contract.Requires(call != null);
      Contract.Requires(requires != null);
      this.Call = call;
      this.Requires = requires;
      // base(call.tok, @requires.Condition);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAssertRequiresCmd(this);
    }
  }

  /// <summary>
  /// An AssertCmd that is introduced in translation from an ensures
  /// declaration.
  /// </summary>
  public class AssertEnsuresCmd : AssertCmd {
    public Ensures/*!*/ Ensures;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Ensures != null);
    }

    public AssertEnsuresCmd(Ensures/*!*/ ens)
      : base(ens.tok, ens.Condition) {
      Contract.Requires(ens != null);
      this.Ensures = ens;
      // base(ens.tok, ens.Condition);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAssertEnsuresCmd(this);
    }
  }

  public class AssumeCmd : PredicateCmd {
    public AssumeCmd(IToken/*!*/ tok, Expr/*!*/ expr)
      : base(tok, expr) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }
    public AssumeCmd(IToken/*!*/ tok, Expr/*!*/ expr, QKeyValue kv)
      : base(tok, expr, kv) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "assume ");
      EmitAttributes(stream, Attributes);
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      Expr.Typecheck(tc);
      Contract.Assert(Expr.Type != null);  // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool)) {
        tc.Error(this, "an assumed expression must be of type bool (got: {0})", Expr.Type);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAssumeCmd(this);
    }
  }

  public class ReturnExprCmd : ReturnCmd {
    public Expr/*!*/ Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public ReturnExprCmd(IToken/*!*/ tok, Expr/*!*/ expr)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "return ");
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      Expr.Typecheck(tc);
      Contract.Assert(Expr.Type != null);  // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool)) {
        tc.Error(this, "a return expression must be of type bool (got: {0})", Expr.Type);
      }
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      Expr.Resolve(rc);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitReturnExprCmd(this);
    }
  }

  public class HavocCmd : Cmd {
    public IdentifierExprSeq/*!*/ Vars;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Vars != null);
    }

    public HavocCmd(IToken/*!*/ tok, IdentifierExprSeq/*!*/ vars)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(vars != null);
      Vars = vars;
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "havoc ");
      Vars.Emit(stream, true);
      stream.WriteLine(";");
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      foreach (IdentifierExpr/*!*/ ide in Vars) {
        Contract.Assert(ide != null);
        ide.Resolve(rc);
      }
    }
    public override void AddAssignedVariables(VariableSeq vars) {
      //Contract.Requires(vars != null);
      foreach (IdentifierExpr/*!*/ e in this.Vars) {
        Contract.Assert(e != null);
        vars.Add(e.Decl);
      }
    }
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      this.CheckAssignments(tc);
    }


    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitHavocCmd(this);
    }
  }

  //---------------------------------------------------------------------
  // Transfer commands
  [ContractClass(typeof(TransferCmdContracts))]
  public abstract class TransferCmd : Absy {
    internal TransferCmd(IToken/*!*/ tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
    public abstract void Emit(TokenTextWriter/*!*/ stream, int level);
    public override void Typecheck(TypecheckingContext tc) {
      //Contract.Requires(tc != null);
      // nothing to typecheck
    }
  }
  [ContractClassFor(typeof(TransferCmd))]
  public abstract class TransferCmdContracts : TransferCmd {
    public TransferCmdContracts() :base(null){

    }
    public override void Emit(TokenTextWriter stream, int level) {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }
  }

  public class ReturnCmd : TransferCmd {
    public ReturnCmd(IToken/*!*/ tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      stream.WriteLine(this, level, "return;");
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      // nothing to resolve
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitReturnCmd(this);
    }
  }

  public class GotoCmd : TransferCmd {
    [Rep]
    public StringSeq labelNames;
    [Rep]
    public BlockSeq labelTargets;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(labelNames == null || labelTargets == null || labelNames.Length == labelTargets.Length);
    }

    [NotDelayed]
    public GotoCmd(IToken/*!*/ tok, StringSeq/*!*/ labelSeq)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(labelSeq != null);
      this.labelNames = labelSeq;
    }
    public GotoCmd(IToken/*!*/ tok, StringSeq/*!*/ labelSeq, BlockSeq/*!*/ blockSeq)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(labelSeq != null);
      Contract.Requires(blockSeq != null);
      Debug.Assert(labelSeq.Length == blockSeq.Length);
      for (int i = 0; i < labelSeq.Length; i++) {
        Debug.Assert(Equals(labelSeq[i], cce.NonNull(blockSeq[i]).Label));
      }

      this.labelNames = labelSeq;
      this.labelTargets = blockSeq;
    }
    public GotoCmd(IToken/*!*/ tok, BlockSeq/*!*/ blockSeq)
      : base(tok) { //requires (blockSeq[i] != null ==> blockSeq[i].Label != null);
      Contract.Requires(tok != null);
      Contract.Requires(blockSeq != null);
      StringSeq labelSeq = new StringSeq();
      for (int i = 0; i < blockSeq.Length; i++)
        labelSeq.Add(cce.NonNull(blockSeq[i]).Label);
      this.labelNames = labelSeq;
      this.labelTargets = blockSeq;
    }
    public void AddTarget(Block b) {
      Contract.Requires(b != null);
      Contract.Requires(b.Label != null);
      Contract.Requires(this.labelTargets != null);
      Contract.Requires(this.labelNames != null);
      this.labelTargets.Add(b);
      this.labelNames.Add(b.Label);
    }
    public override void Emit(TokenTextWriter stream, int level) {
      //Contract.Requires(stream != null);
      Contract.Assume(this.labelNames != null);
      stream.Write(this, level, "goto ");
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
        if (labelTargets == null) {
          string sep = "";
          foreach (string name in labelNames) {
            stream.Write("{0}{1}^^{2}", sep, "NoDecl", name);
            sep = ", ";
          }
        } else {
          string sep = "";
          foreach (Block/*!*/ b in labelTargets) {
            Contract.Assert(b != null);
            stream.Write("{0}h{1}^^{2}", sep, b.GetHashCode(), b.Label);
            sep = ", ";
          }
        }
      } else {
        labelNames.Emit(stream);
      }
      stream.WriteLine(";");
    }
    public override void Resolve(ResolutionContext rc) {
      //Contract.Requires(rc != null);
      Contract.Ensures(labelTargets != null);
      if (labelTargets != null) {
        // already resolved
        return;
      }
      Contract.Assume(this.labelNames != null);
      labelTargets = new BlockSeq();
      foreach (string/*!*/ lbl in labelNames) {
        Contract.Assert(lbl != null);
        Block b = rc.LookUpBlock(lbl);
        if (b == null) {
          rc.Error(this, "goto to unknown block: {0}", lbl);
        } else {
          labelTargets.Add(b);
        }
      }
      Debug.Assert(rc.ErrorCount > 0 || labelTargets.Length == labelNames.Length);
    }

    public override Absy StdDispatch(StandardVisitor visitor) {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitGotoCmd(this);
    }
  }
}