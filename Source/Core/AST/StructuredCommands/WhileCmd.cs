using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

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
    Guard = guard;
    Invariants = invariants;
    Yields = yields;
    Body = body;
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

  public override void CreateBlocks(BigBlocksResolutionContext context, BigBlock bigBlock, List<Cmd> incomingCommands,
    string runOffTheEndLabel)
  {
    var prefix = context.FreshPrefix();
    string loopHeadLabel = prefix + "_LoopHead";
    string /*!*/ loopBodyLabel = prefix + "_LoopBody";
    string loopDoneLabel = prefix + "_LoopDone";

    List<Cmd> ssBody = new List<Cmd>();
    List<Cmd> ssDone = new List<Cmd>();
    if (Guard != null)
    {
      var ac = new AssumeCmd(tok, Guard);
      ac.Attributes = new QKeyValue(tok, "partition", new List<object>(), null);
      ssBody.Add(ac);

      ac = new AssumeCmd(tok, Expr.Not(Guard));
      ac.Attributes = new QKeyValue(tok, "partition", new List<object>(), null);
      ssDone.Add(ac);
    }

    // Try to squeeze in ssBody into the first block of wcmd.Body
    bool bodyGuardTakenCareOf = Body.PrefixFirstBlock(ssBody, ref loopBodyLabel);

    // ... goto LoopHead;
    Block block = new Block(bigBlock.tok, bigBlock.LabelName, incomingCommands,
      new GotoCmd(tok, new List<String> {loopHeadLabel}));
    context.AddBlock(block);

    // LoopHead: assert/assume loop_invariant; goto LoopDone, LoopBody;
    List<Cmd> ssHead = new List<Cmd>();
    foreach (CallCmd yield in Yields)
    {
      ssHead.Add(yield);
    }
    foreach (PredicateCmd inv in Invariants)
    {
      ssHead.Add(inv);
    }

    block = new Block(tok, loopHeadLabel, ssHead,
      new GotoCmd(tok, new List<String> {loopDoneLabel, loopBodyLabel}));
    context.AddBlock(block);

    if (!bodyGuardTakenCareOf)
    {
      // LoopBody: assume guard; goto firstLoopBlock;
      block = new Block(tok, loopBodyLabel, ssBody,
        new GotoCmd(tok, new List<String> {Body.BigBlocks[0].LabelName}));
      context.AddBlock(block);
    }

    // recurse to create the blocks for the loop body
    context.CreateBlocks(Body, loopHeadLabel);

    // LoopDone: assume !guard; goto loopSuccessor;
    TransferCmd trCmd;
    if (runOffTheEndLabel != null)
    {
      // goto the given label instead of the textual successor block
      trCmd = new GotoCmd(tok, new List<String> {runOffTheEndLabel});
    }
    else
    {
      trCmd = BigBlocksResolutionContext.GotoSuccessor(tok, bigBlock);
    }

    block = new Block(tok, loopDoneLabel, ssDone, trCmd);
    context.AddBlock(block);
  }

  public override IEnumerable<StmtList> StatementLists => new[] { Body };
  public override void RecordSuccessors(BigBlocksResolutionContext context, BigBlock bigBlock)
  {
    context.RecordSuccessors(Body, bigBlock);
  }
}