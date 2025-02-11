using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class StmtList
{
  [Rep] private readonly List<BigBlock /*!*/> /*!*/ bigBlocks;

  public IList<BigBlock /*!*/> /*!*/ BigBlocks
  {
    get
    {
      Contract.Ensures(Contract.Result<IList<BigBlock>>() != null);
      Contract.Ensures(Contract.Result<IList<BigBlock>>().IsReadOnly);
      return this.bigBlocks.AsReadOnly();
    }
  }

  public List<Cmd> PrefixCommands;

  public readonly IToken /*!*/ EndCurly;

  public StmtList ParentContext;
  public BigBlock ParentBigBlock;

  private readonly HashSet<string /*!*/> /*!*/
    labels = new HashSet<string /*!*/>();

  public void AddLabel(string label)
  {
    labels.Add(label);
  }

  public IEnumerable<string /*!*/> /*!*/ Labels
  {
    get
    {
      Contract.Ensures(Cce.NonNullElements(Contract.Result<IEnumerable<string /*!*/> /*!*/>()));
      return this.labels.AsEnumerable<string>();
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(EndCurly != null);
    Contract.Invariant(Cce.NonNullElements(this.bigBlocks));
    Contract.Invariant(Cce.NonNullElements(this.labels));
  }

  public StmtList(IList<BigBlock /*!*/> /*!*/ bigblocks, IToken endCurly)
  {
    Contract.Requires(endCurly != null);
    Contract.Requires(Cce.NonNullElements(bigblocks));
    Contract.Requires(bigblocks.Count > 0);
    this.bigBlocks = new List<BigBlock>(bigblocks);
    this.EndCurly = endCurly;
  }

  // prints the list of statements, not the surrounding curly braces
  public void Emit(TokenTextWriter stream, int level)
  {
    Contract.Requires(stream != null);
    bool needSeperator = false;
    foreach (BigBlock b in BigBlocks)
    {
      Contract.Assert(b != null);
      Contract.Assume(Cce.IsPeerConsistent(b));
      if (needSeperator)
      {
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
  public bool PrefixFirstBlock([Captured] List<Cmd> prefixCmds, ref string suggestedLabel)
  {
    Contract.Requires(suggestedLabel != null);
    Contract.Requires(prefixCmds != null);
    Contract.Ensures(Contract.Result<bool>() ||
                     Cce.Owner.None(prefixCmds)); // "prefixCmds" is captured only on success
    Contract.Assume(PrefixCommands == null); // prefix has not been used

    BigBlock bb0 = BigBlocks[0];
    if (prefixCmds.Count == 0)
    {
      // This is always a success, since there is nothing to insert.  Now, decide
      // which name to use for the first block.
      if (bb0.Anonymous)
      {
        bb0.LabelName = suggestedLabel;
      }
      else
      {
        Contract.Assert(bb0.LabelName != null);
        suggestedLabel = bb0.LabelName;
      }

      return true;
    }
    else
    {
      // There really is something to insert.  We can do this inline only if the first
      // block is anonymous (which implies there is no branch to it from within the block).
      if (bb0.Anonymous)
      {
        PrefixCommands = prefixCmds;
        bb0.LabelName = suggestedLabel;
        return true;
      }
      else
      {
        return false;
      }
    }
  }
}