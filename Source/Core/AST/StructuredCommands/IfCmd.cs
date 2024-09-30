using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class IfCmd : StructuredCmd
{
  public readonly Expr Guard;

  private StmtList /*!*/ _thn;

  public StmtList /*!*/ Thn
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

  private IfCmd elseIf;

  public IfCmd ElseIf
  {
    get => this.elseIf;
    set
    {
      Contract.Requires(value == null || this.ElseBlock == null);
      this.elseIf = value;
    }
  }

  private StmtList elseBlock;

  public StmtList ElseBlock
  {
    get => this.elseBlock;
    set
    {
      Contract.Requires(value == null || this.ElseIf == null);
      this.elseBlock = value;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(this._thn != null);
    Contract.Invariant(this.elseIf == null || this.elseBlock == null);
  }

  public IfCmd(IToken /*!*/ tok, Expr guard, StmtList /*!*/ thn, IfCmd elseIf, StmtList elseBlock)
    : base(tok)
  {
    Contract.Requires(tok != null);
    Contract.Requires(thn != null);
    Contract.Requires(elseIf == null || elseBlock == null);
    this.Guard = guard;
    this._thn = thn;
    this.elseIf = elseIf;
    this.elseBlock = elseBlock;
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
      ifcmd.Thn.Emit(stream, level + 1);
      stream.WriteLine(level, "}");

      if (ifcmd.ElseIf != null)
      {
        stream.Write(level, "else if (");
        ifcmd = ifcmd.ElseIf;
        continue;
      }
      else if (ifcmd.ElseBlock != null)
      {
        stream.WriteLine(level, "else");
        stream.WriteLine(level, "{");
        ifcmd.ElseBlock.Emit(stream, level + 1);
        stream.WriteLine(level, "}");
      }

      break;
    }
  }

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock bigBlock, List<Cmd> incomingCommands,
    string runOffTheEndLabel)
  {
    var ifcmd = this;
    string previousLabel = bigBlock.LabelName;
    var previousCommands = incomingCommands;

    for (; ifcmd != null; ifcmd = ifcmd.ElseIf)
    {
      var prefix = context.FreshPrefix();
      string thenLabel = prefix + "_Then";
      string elseLabel = prefix + "_Else";

      var ssThen = new List<Cmd>();
      var ssElse = new List<Cmd>();
      if (ifcmd.Guard != null)
      {
        var ac = new AssumeCmd(ifcmd.tok, ifcmd.Guard)
        {
          Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null)
        };
        ssThen.Add(ac);

        ac = new AssumeCmd(ifcmd.tok, Expr.Not(ifcmd.Guard))
        {
          Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null)
        };
        ssElse.Add(ac);
      }

      // Try to squeeze in ssThen/ssElse into the first block of ifcmd.thn/ifcmd.elseBlock
      bool thenGuardTakenCareOf = ifcmd.Thn.PrefixFirstBlock(ssThen, ref thenLabel);
      bool elseGuardTakenCareOf = false;
      if (ifcmd.ElseBlock != null)
      {
        elseGuardTakenCareOf = ifcmd.ElseBlock.PrefixFirstBlock(ssElse, ref elseLabel);
      }

      // ... goto Then, Else;
      var jumpBlock = new Block(bigBlock.tok, previousLabel, previousCommands,
        new GotoCmd(ifcmd.tok, new List<string> {thenLabel, elseLabel}));
      context.AddBlock(jumpBlock);

      if (!thenGuardTakenCareOf)
      {
        // Then: assume guard; goto firstThenBlock;
        var thenJumpBlock = new Block(ifcmd.tok, thenLabel, ssThen,
          new GotoCmd(ifcmd.tok, new List<string> {ifcmd.Thn.BigBlocks[0].LabelName}));
        context.AddBlock(thenJumpBlock);
      }

      // recurse to create the blocks for the then branch
      context.CreateBlocks(ifcmd.Thn, runOffTheEndLabel);

      if (ifcmd.ElseBlock != null)
      {
        Contract.Assert(ifcmd.ElseIf == null);
        if (!elseGuardTakenCareOf)
        {
          // Else: assume !guard; goto firstElseBlock;
          var elseJumpBlock = new Block(ifcmd.tok, elseLabel, ssElse,
            new GotoCmd(ifcmd.tok, new List<String> {ifcmd.ElseBlock.BigBlocks[0].LabelName}));
          context.AddBlock(elseJumpBlock);
        }

        // recurse to create the blocks for the else branch
        context.CreateBlocks(ifcmd.ElseBlock, runOffTheEndLabel);
      }
      else if (ifcmd.ElseIf != null)
      {
        // this is an "else if"
        previousLabel = elseLabel;
        previousCommands = new List<Cmd>();
        if (ifcmd.Guard != null)
        {
          var ac = new AssumeCmd(ifcmd.tok, Expr.Not(ifcmd.Guard))
          {
            Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null)
          };
          previousCommands.Add(ac);
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
          trCmd = new GotoCmd(ifcmd.tok, new List<string> {runOffTheEndLabel});
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
      for (var ifcmd = this; ifcmd != null; ifcmd = ifcmd.ElseIf)
      {
        yield return ifcmd.Thn;
        if (ifcmd.ElseBlock != null)
        {
          yield return ifcmd.ElseBlock;
        }
      }
    }
  }

  public override void RecordSuccessors(BigBlocksResolutionContext context, BigBlock bigBlock)
  {
    for (var ifcmd = this; ifcmd != null; ifcmd = ifcmd.ElseIf)
    {
      context.RecordSuccessors(ifcmd.Thn, bigBlock.Successor);
      if (ifcmd.ElseBlock != null)
      {
        context.RecordSuccessors(ifcmd.ElseBlock, bigBlock.Successor);
      }
    }
  }
}