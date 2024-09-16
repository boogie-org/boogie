using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class IfCmd : StructuredCmd
{
  public Expr Guard;

  private StmtList /*!*/
    _thn;

  public StmtList /*!*/ thn
  {
    get
    {
      Contract.Ensures(Contract.Result<StmtList>() != null);
      return this._thn;
    }
    set
    {
      Contract.Requires(value != null);
      this._thn = value;
    }
  }

  private IfCmd _elseIf;

  public IfCmd elseIf
  {
    get { return this._elseIf; }
    set
    {
      Contract.Requires(value == null || this.elseBlock == null);
      this._elseIf = value;
    }
  }

  private StmtList _elseBlock;

  public StmtList elseBlock
  {
    get { return this._elseBlock; }
    set
    {
      Contract.Requires(value == null || this.elseIf == null);
      this._elseBlock = value;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(this._thn != null);
    Contract.Invariant(this._elseIf == null || this._elseBlock == null);
  }

  public IfCmd(IToken /*!*/ tok, Expr guard, StmtList /*!*/ thn, IfCmd elseIf, StmtList elseBlock)
    : base(tok)
  {
    Contract.Requires(tok != null);
    Contract.Requires(thn != null);
    Contract.Requires(elseIf == null || elseBlock == null);
    this.Guard = guard;
    this._thn = thn;
    this._elseIf = elseIf;
    this._elseBlock = elseBlock;
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    stream.Write(level, "if (");
    IfCmd /*!*/
      ifcmd = this;
    while (true)
    {
      if (ifcmd.Guard == null)
      {
        stream.Write("*");
      }
      else
      {
        ifcmd.Guard.Emit(stream);
      }

      stream.WriteLine(")");

      stream.WriteLine(level, "{");
      ifcmd.thn.Emit(stream, level + 1);
      stream.WriteLine(level, "}");

      if (ifcmd.elseIf != null)
      {
        stream.Write(level, "else if (");
        ifcmd = ifcmd.elseIf;
        continue;
      }
      else if (ifcmd.elseBlock != null)
      {
        stream.WriteLine(level, "else");
        stream.WriteLine(level, "{");
        ifcmd.elseBlock.Emit(stream, level + 1);
        stream.WriteLine(level, "}");
      }

      break;
    }
  }

  public override void InjectEmptyBigBlockInsideWhileLoopBody(BigBlocksResolutionContext context)
  {
    context.InjectEmptyBigBlockInsideWhileLoopBody(thn);
    if (elseBlock != null)
    {
      context.InjectEmptyBigBlockInsideWhileLoopBody(elseBlock);
    }

    if (elseIf != null)
    {
      elseIf.InjectEmptyBigBlockInsideWhileLoopBody(context);
    }
  }

  public override void CheckLegalLabels(BigBlocksResolutionContext context, StmtList stmtList, BigBlock bigBlock)
  {
    for (IfCmd ifcmd = this; ifcmd != null; ifcmd = ifcmd.elseIf)
    {
      context.CheckLegalLabels(ifcmd.thn, stmtList, bigBlock);
      if (ifcmd.elseBlock != null)
      {
        context.CheckLegalLabels(ifcmd.elseBlock, stmtList, bigBlock);
      }
    }
  }

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock bigBlock, List<Cmd> theSimpleCmds,
    string runOffTheEndLabel)
  {
    IfCmd ifcmd = (IfCmd) bigBlock.ec;
    string predLabel = bigBlock.LabelName;
    List<Cmd> predCmds = theSimpleCmds;

    for (; ifcmd != null; ifcmd = ifcmd.elseIf)
    {
      var prefix = context.FreshPrefix();
      string thenLabel = prefix + "_Then";
      Contract.Assert(thenLabel != null);
      string elseLabel = prefix + "_Else";
      Contract.Assert(elseLabel != null);

      List<Cmd> ssThen = new List<Cmd>();
      List<Cmd> ssElse = new List<Cmd>();
      if (ifcmd.Guard != null)
      {
        var ac = new AssumeCmd(ifcmd.tok, ifcmd.Guard);
        ac.Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null);
        ssThen.Add(ac);

        ac = new AssumeCmd(ifcmd.tok, Expr.Not(ifcmd.Guard));
        ac.Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null);
        ssElse.Add(ac);
      }

      // Try to squeeze in ssThen/ssElse into the first block of ifcmd.thn/ifcmd.elseBlock
      bool thenGuardTakenCareOf = ifcmd.thn.PrefixFirstBlock(ssThen, ref thenLabel);
      bool elseGuardTakenCareOf = false;
      if (ifcmd.elseBlock != null)
      {
        elseGuardTakenCareOf = ifcmd.elseBlock.PrefixFirstBlock(ssElse, ref elseLabel);
      }

      // ... goto Then, Else;
      var jumpBlock = new Block(bigBlock.tok, predLabel, predCmds,
        new GotoCmd(ifcmd.tok, new List<String> {thenLabel, elseLabel}));
      context.AddBlock(jumpBlock);

      if (!thenGuardTakenCareOf)
      {
        // Then: assume guard; goto firstThenBlock;
        var thenJumpBlock = new Block(ifcmd.tok, thenLabel, ssThen,
          new GotoCmd(ifcmd.tok, new List<String> {ifcmd.thn.BigBlocks[0].LabelName}));
        context.AddBlock(thenJumpBlock);
      }

      // recurse to create the blocks for the then branch
      context.CreateBlocks(ifcmd.thn, runOffTheEndLabel);

      if (ifcmd.elseBlock != null)
      {
        Contract.Assert(ifcmd.elseIf == null);
        if (!elseGuardTakenCareOf)
        {
          // Else: assume !guard; goto firstElseBlock;
          var elseJumpBlock = new Block(ifcmd.tok, elseLabel, ssElse,
            new GotoCmd(ifcmd.tok, new List<String> {ifcmd.elseBlock.BigBlocks[0].LabelName}));
          context.AddBlock(elseJumpBlock);
        }

        // recurse to create the blocks for the else branch
        context.CreateBlocks(ifcmd.elseBlock, runOffTheEndLabel);
      }
      else if (ifcmd.elseIf != null)
      {
        // this is an "else if"
        predLabel = elseLabel;
        predCmds = new List<Cmd>();
        if (ifcmd.Guard != null)
        {
          var ac = new AssumeCmd(ifcmd.tok, Expr.Not(ifcmd.Guard));
          ac.Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null);
          predCmds.Add(ac);
        }
      }
      else
      {
        // no else alternative is specified, so else branch is just "skip"
        // Else: assume !guard; goto ifSuccessor;
        TransferCmd trCmd;
        if (runOffTheEndLabel != null)
        {
          // goto the given label instead of the textual successor block
          trCmd = new GotoCmd(ifcmd.tok, new List<String> {runOffTheEndLabel});
        }
        else
        {
          trCmd = BigBlocksResolutionContext.GotoSuccessor(ifcmd.tok, bigBlock);
        }

        var block = new Block(ifcmd.tok, elseLabel, ssElse, trCmd);
        context.AddBlock(block);
      }
    }
  }

  public override IEnumerable<StmtList> StatementLists {
    get
    {
      for (var ifcmd = this; ifcmd != null; ifcmd = ifcmd.elseIf)
      {
        yield return ifcmd.thn;
        if (ifcmd.elseBlock != null)
        {
          yield return ifcmd.elseBlock;
        }
      }
    }
  }

  public override void RecordSuccessors(BigBlocksResolutionContext context, BigBlock bigBlock)
  {
    for (var ifcmd = this; ifcmd != null; ifcmd = ifcmd.elseIf)
    {
      context.RecordSuccessors(ifcmd.thn, bigBlock.successorBigBlock);
      if (ifcmd.elseBlock != null)
      {
        context.RecordSuccessors(ifcmd.elseBlock, bigBlock.successorBigBlock);
      }
    }
  }
}