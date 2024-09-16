using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class WhileCmd : StructuredCmd
{
  [Peer] public Expr Guard;

  public List<PredicateCmd> Invariants;

  public List<CallCmd> Yields;

  public StmtList Body;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Body != null);
    Contract.Invariant(cce.NonNullElements(Invariants));
  }

  public WhileCmd(IToken tok, [Captured] Expr guard, List<PredicateCmd> invariants, List<CallCmd> yields, StmtList body)
    : base(tok)
  {
    Contract.Requires(cce.NonNullElements(invariants));
    Contract.Requires(body != null);
    Contract.Requires(tok != null);
    this.Guard = guard;
    this.Invariants = invariants;
    this.Yields = yields;
    this.Body = body;
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    stream.Write(level, "while (");
    if (Guard == null)
    {
      stream.Write("*");
    }
    else
    {
      Guard.Emit(stream);
    }

    stream.WriteLine(")");

    foreach (var yield in Yields)
    {
      stream.Write(level + 1, "invariant");
      yield.Emit(stream, level + 1);
    }
    foreach (var inv in Invariants)
    {
      if (inv is AssumeCmd)
      {
        stream.Write(level + 1, "free invariant ");
      }
      else
      {
        stream.Write(level + 1, "invariant ");
      }

      Cmd.EmitAttributes(stream, inv.Attributes);
      inv.Expr.Emit(stream);
      stream.WriteLine(";");
    }

    stream.WriteLine(level, "{");
    Body.Emit(stream, level + 1);
    stream.WriteLine(level, "}");
  }

  public override void InjectEmptyBigBlockInsideWhileLoopBody(BigBlocksResolutionContext context)
  {
    context.InjectEmptyBigBlockInsideWhileLoopBody(Body);
    if (Body.BigBlocks.Count <= 0 || Body.BigBlocks.Last().ec is not WhileCmd)
    {
      return;
    }

    var newBigBlocks = new List<BigBlock>(Body.BigBlocks);
    newBigBlocks.Add(new BigBlock(Token.NoToken, null, new List<Cmd>(), null, null));
    Body = new StmtList(newBigBlocks, Body.EndCurly);
  }

  public override void CheckLegalLabels(BigBlocksResolutionContext context, StmtList stmtList, BigBlock bigBlock)
  {
    context.CheckLegalLabels(Body, stmtList, bigBlock);
  }

  public override void ComputeAllLabels(BigBlocksResolutionContext context)
  {
    context.ComputeAllLabels(Body);
  }

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock b, List<Cmd> theSimpleCmds,
    StmtList stmtList,
    string runOffTheEndLabel)
  {
      WhileCmd wcmd = (WhileCmd) this;
      var prefix = context.FreshPrefix();
      string loopHeadLabel = prefix + "_LoopHead";
      string /*!*/ loopBodyLabel = prefix + "_LoopBody";
      string loopDoneLabel = prefix + "_LoopDone";

      List<Cmd> ssBody = new List<Cmd>();
      List<Cmd> ssDone = new List<Cmd>();
      if (wcmd.Guard != null)
      {
        var ac = new AssumeCmd(wcmd.tok, wcmd.Guard);
        ac.Attributes = new QKeyValue(wcmd.tok, "partition", new List<object>(), null);
        ssBody.Add(ac);

        ac = new AssumeCmd(wcmd.tok, Expr.Not(wcmd.Guard));
        ac.Attributes = new QKeyValue(wcmd.tok, "partition", new List<object>(), null);
        ssDone.Add(ac);
      }

      // Try to squeeze in ssBody into the first block of wcmd.Body
      bool bodyGuardTakenCareOf = wcmd.Body.PrefixFirstBlock(ssBody, ref loopBodyLabel);

      // ... goto LoopHead;
      Block block = new Block(b.tok, b.LabelName, theSimpleCmds,
        new GotoCmd(wcmd.tok, new List<String> {loopHeadLabel}));
      context.AddBlock(block);

      // LoopHead: assert/assume loop_invariant; goto LoopDone, LoopBody;
      List<Cmd> ssHead = new List<Cmd>();
      foreach (CallCmd yield in wcmd.Yields)
      {
        ssHead.Add(yield);
      }
      foreach (PredicateCmd inv in wcmd.Invariants)
      {
        ssHead.Add(inv);
      }

      block = new Block(wcmd.tok, loopHeadLabel, ssHead,
        new GotoCmd(wcmd.tok, new List<String> {loopDoneLabel, loopBodyLabel}));
      context.AddBlock(block);

      if (!bodyGuardTakenCareOf)
      {
        // LoopBody: assume guard; goto firstLoopBlock;
        block = new Block(wcmd.tok, loopBodyLabel, ssBody,
          new GotoCmd(wcmd.tok, new List<String> {wcmd.Body.BigBlocks[0].LabelName}));
        context.AddBlock(block);
      }

      // recurse to create the blocks for the loop body
      context.CreateBlocks(wcmd.Body, loopHeadLabel);

      // LoopDone: assume !guard; goto loopSuccessor;
      TransferCmd trCmd;
      if (runOffTheEndLabel != null)
      {
        // goto the given label instead of the textual successor block
        trCmd = new GotoCmd(wcmd.tok, new List<String> {runOffTheEndLabel});
      }
      else
      {
        trCmd = BigBlocksResolutionContext.GotoSuccessor(wcmd.tok, b);
      }

      block = new Block(wcmd.tok, loopDoneLabel, ssDone, trCmd);
      context.AddBlock(block);
  }
}