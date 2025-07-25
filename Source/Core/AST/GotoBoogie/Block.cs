using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public sealed class Block : Absy
{

  public string Label { get; set; } // Note, Label is mostly readonly, but it can change to the name of a nearby block during block coalescing and empty-block removal

  [Rep]
  [ElementsPeer]
  public List<Cmd> Cmds { get; set; }

  public IEnumerable<Block> Exits()
  {
    if (TransferCmd is GotoCmd g)
    {
      return Cce.NonNull(g.LabelTargets);
    }
    return new List<Block>();
  }

  [Rep] //PM: needed to verify Traverse.Visit
  public TransferCmd TransferCmd; // maybe null only because we allow deferred initialization (necessary for cyclic structures)

  public byte[] Checksum;

  public enum VisitState
  {
    ToVisit,
    BeingVisited,
    AlreadyVisited
  } // used by WidenPoints.Compute

  public VisitState TraversingStatus;

  public int AiId; // block ID used by the abstract interpreter, which may change these numbers with each AI run
  public bool WidenBlock;

  public int Iterations; // Count the number of time we visited the block during fixpoint computation. Used to decide if we widen or not

  // VC generation and SCC computation
  public List<Block> Predecessors;

  // This field is used during passification to null-out entries in block2Incarnation dictionary early
  public int SuccCount;

  private HashSet<Variable> liveVarsBefore;
  public IEnumerable<Variable> LiveVarsBefore
  {
    get
    {
      Contract.Ensures(Cce.NonNullElements(Contract.Result<IEnumerable<Variable>>(), true));
      if (this.liveVarsBefore == null)
      {
        return null;
      }
      else
      {
        return this.liveVarsBefore.AsEnumerable<Variable>();
      }
    }
    set
    {
      Contract.Requires(Cce.NonNullElements(value, true));
      if (value == null)
      {
        this.liveVarsBefore = null;
      }
      else
      {
        this.liveVarsBefore = new HashSet<Variable>(value);
      }
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(this.Label != null);
    Contract.Invariant(this.Cmds != null);
    Contract.Invariant(Cce.NonNullElements(this.liveVarsBefore, true));
  }

  public bool IsLive(Variable v)
  {
    Contract.Requires(v != null);
    if (LiveVarsBefore == null)
    {
      return true;
    }

    return LiveVarsBefore.Contains(v);
  }

  public static Block ShallowClone(Block block)
  {
    return new Block(block.tok, block.Label, block.Cmds, block.TransferCmd);
  }

  public Block(IToken tok, TransferCmd cmd)
    : this(tok, "", new List<Cmd>(), new ReturnCmd(tok))
  {
  }

  public Block(IToken tok, string label, List<Cmd> cmds, TransferCmd transferCmd)
    : base(tok)
  {
    Contract.Requires(label != null);
    Contract.Requires(cmds != null);
    Contract.Requires(tok != null);
    this.Label = label;
    this.Cmds = cmds;
    this.TransferCmd = transferCmd;
    this.Predecessors = new List<Block>();
    this.liveVarsBefore = null;
    this.TraversingStatus = VisitState.ToVisit;
    this.Iterations = 0;
  }

  public void Emit(TokenTextWriter stream, int level)
  {
    Contract.Requires(stream != null);
    stream.WriteLine();
    stream.WriteLine(
      this,
      level,
      "{0}:{1}",
      stream.Options.PrintWithUniqueASTIds
        ? String.Format("h{0}^^{1}", this.GetHashCode(), this.Label)
        : this.Label,
      this.WidenBlock ? "  // cut point" : "");

    foreach (Cmd c in this.Cmds)
    {
      Contract.Assert(c != null);
      c.Emit(stream, level + 1);
    }

    Contract.Assume(this.TransferCmd != null);
    this.TransferCmd.Emit(stream, level + 1);
  }

  public void Register(ResolutionContext rc)
  {
    Contract.Requires(rc != null);
    rc.AddBlock(this);
  }

  public override void Resolve(ResolutionContext rc)
  {
    foreach (Cmd c in Cmds)
    {
      Contract.Assert(c != null);
      c.Resolve(rc);
    }

    Contract.Assume(this.TransferCmd != null);
    TransferCmd.Resolve(rc);
  }

  public override void Typecheck(TypecheckingContext tc)
  {
    foreach (var cmd in Cmds)
    {
      Contract.Assert(cmd != null);
      cmd.Typecheck(tc);
    }

    Contract.Assume(this.TransferCmd != null);
    TransferCmd.Typecheck(tc);
  }

  /// <summary>
  /// Reset the abstract intepretation state of this block. It does this by putting the iterations to 0 and the pre and post states to null
  /// </summary>
  public void ResetAbstractInterpretationState()
  {
    //      this.currentlyTraversed = false;
    this.TraversingStatus = VisitState.ToVisit;
    this.Iterations = 0;
  }

  [Pure]
  public override string ToString()
  {
    Contract.Ensures(Contract.Result<string>() != null);
    return this.Label + (this.WidenBlock ? "[w]" : "");
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitBlock(this);
  }

  public bool HasInvariant()
  {
    return Cmds.Count >= 1 && Cmds[0] is AssertCmd;
  }
  
  public void SubstituteBranchTargets(Dictionary<Block, Block> subst)
  {
    TransferCmd transferCmd = this.TransferCmd;
    if (transferCmd is not GotoCmd)
    {
      return;
    }

    GotoCmd gotoCmd = (GotoCmd)transferCmd;
    foreach (Block currentBlock in gotoCmd.LabelTargets.ToList())
    {
      if (subst.TryGetValue(currentBlock, out Block dupBlock))
      {
        gotoCmd.RemoveTarget(currentBlock);
        gotoCmd.AddTarget(dupBlock);
      }
    }
  }

  public Block DuplicateBlock(Dictionary<Block, int> nextLabels)
  {
    List<Cmd> dupCmds = new List<Cmd>();
    this.Cmds.ForEach(dupCmds.Add);

    TransferCmd splitTransferCmd = this.TransferCmd;
    TransferCmd dupTransferCmd;

    if (splitTransferCmd is not GotoCmd)
    {
      dupTransferCmd = new ReturnCmd(Token.NoToken);
    }
    else
    {
      List<string> dupLabelNames = [.. ((GotoCmd)splitTransferCmd).LabelNames];
      List<Block> dupLabelTargets = new List<Block>();
      ((GotoCmd)splitTransferCmd).LabelTargets.ForEach(dupLabelTargets.Add);

      dupTransferCmd = new GotoCmd(Token.NoToken, dupLabelNames, dupLabelTargets);
    }

    Block dupBlock = new Block(Token.NoToken, this.Label + "_dup_" + nextLabels[this], dupCmds, dupTransferCmd);
    nextLabels[this]++;
    nextLabels.Add(dupBlock, 0);
    return dupBlock;
  }
}