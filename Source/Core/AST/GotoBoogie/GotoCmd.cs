using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class GotoCmd : TransferCmd, ICarriesAttributes
{
  [Rep] public List<string> LabelNames;
  [Rep] public List<Block> LabelTargets;

  public QKeyValue Attributes { get; set; }
    
  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(LabelNames == null || LabelTargets == null || LabelNames.Count == LabelTargets.Count);
  }

  [NotDelayed]
  public GotoCmd(IToken tok, List<string> labels)
    : base(tok)
  {
    Contract.Requires(tok != null);
    Contract.Requires(labels != null);
    this.LabelNames = labels;
  }

  public GotoCmd(IToken tok, List<string> labels, List<Block> blocks)
    : base(tok)
  {
    Contract.Requires(tok != null);
    Contract.Requires(labels != null);
    Contract.Requires(blocks != null);
    Debug.Assert(labels.Count == blocks.Count);
    for (int i = 0; i < labels.Count; i++)
    {
      Debug.Assert(Equals(labels[i], Cce.NonNull(blocks[i]).Label));
    }

    this.LabelNames = labels;
    this.LabelTargets = blocks;
  }

  public GotoCmd(IToken tok, List<Block> blocks)
    : base(tok)
  {
    //requires (blockSeq[i] != null ==> blockSeq[i].Label != null);
    Contract.Requires(tok != null);
    Contract.Requires(blocks != null);
    var labels = new List<string>();
    foreach (var block in blocks)
    {
      labels.Add(block.Label);
    }

    this.LabelNames = labels;
    this.LabelTargets = blocks;
  }

  public void RemoveTarget(Block b) {
    LabelNames.Remove(b.Label);
    LabelTargets.Remove(b);
  }
    
  public void AddTarget(Block b)
  {
    Contract.Requires(b != null);
    Contract.Requires(b.Label != null);
    Contract.Requires(this.LabelTargets != null);
    Contract.Requires(this.LabelNames != null);
    this.LabelTargets.Add(b);
    this.LabelNames.Add(b.Label);
  }

  public void AddTargets(IEnumerable<Block> blocks)
  {
    Contract.Requires(blocks != null);
    Contract.Requires(Cce.NonNullElements(blocks));
    Contract.Requires(this.LabelTargets != null);
    Contract.Requires(this.LabelNames != null);
    foreach (var block in blocks)
    {
      AddTarget(block);
    }
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    Contract.Assume(this.LabelNames != null);
    stream.Write(this, level, "goto ");
    Attributes?.Emit(stream);
    if (stream.Options.PrintWithUniqueASTIds)
    {
      if (LabelTargets == null)
      {
        string sep = "";
        foreach (string name in LabelNames)
        {
          stream.Write("{0}{1}^^{2}", sep, "NoDecl", name);
          sep = ", ";
        }
      }
      else
      {
        string sep = "";
        foreach (Block b in LabelTargets)
        {
          Contract.Assert(b != null);
          stream.Write("{0}h{1}^^{2}", sep, b.GetHashCode(), b.Label);
          sep = ", ";
        }
      }
    }
    else
    {
      LabelNames.Emit(stream);
    }

    stream.WriteLine(";");
  }

  public override void Resolve(ResolutionContext rc)
  {
    Contract.Ensures(LabelTargets != null);
    if (LabelTargets != null)
    {
      // already resolved
      return;
    }

    Contract.Assume(this.LabelNames != null);
    LabelTargets = new List<Block>();
    foreach (string lbl in LabelNames)
    {
      Contract.Assert(lbl != null);
      Block b = rc.LookUpBlock(lbl);
      if (b == null)
      {
        rc.Error(this, "goto to unknown block: {0}", lbl);
      }
      else
      {
        LabelTargets.Add(b);
      }
    }

    Debug.Assert(rc.ErrorCount > 0 || LabelTargets.Count == LabelNames.Count);
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitGotoCmd(this);
  }
}