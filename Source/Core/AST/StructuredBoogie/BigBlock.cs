using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class BigBlock
{
  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(tok != null);
    Contract.Invariant(Anonymous || this.labelName != null);
    Contract.Invariant(this._ec == null || this._tc == null);
    Contract.Invariant(this._simpleCmds != null);
  }

  public readonly IToken /*!*/
    tok;

  public readonly bool Anonymous;

  private string labelName;

  public string LabelName
  {
    get
    {
      Contract.Ensures(Anonymous || Contract.Result<string>() != null);
      return this.labelName;
    }
    set
    {
      Contract.Requires(Anonymous || value != null);
      this.labelName = value;
    }
  }

  [Rep] private List<Cmd> /*!*/ _simpleCmds;

  /// <summary>
  /// These come before the structured command
  /// </summary>
  public List<Cmd> /*!*/ simpleCmds
  {
    get
    {
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      return this._simpleCmds;
    }
    set
    {
      Contract.Requires(value != null);
      this._simpleCmds = value;
    }
  }

  private StructuredCmd _ec;

  public StructuredCmd ec
  {
    get { return this._ec; }
    set
    {
      Contract.Requires(value == null || this.tc == null);
      this._ec = value;
    }
  }

  private TransferCmd _tc;

  public TransferCmd tc
  {
    get { return this._tc; }
    set
    {
      Contract.Requires(value == null || this.ec == null);
      this._tc = value;
    }
  }

  public BigBlock
    successorBigBlock; // semantic successor (may be a back-edge, pointing back to enclosing while statement); null if successor is end of procedure body (or if field has not yet been initialized)

  public BigBlock(IToken tok, string labelName, [Captured] List<Cmd> simpleCmds, StructuredCmd ec, TransferCmd tc)
  {
    Contract.Requires(simpleCmds != null);
    Contract.Requires(tok != null);
    Contract.Requires(ec == null || tc == null);
    this.tok = tok;
    this.Anonymous = labelName == null;
    this.labelName = labelName;
    this._simpleCmds = simpleCmds;
    this._ec = ec;
    this._tc = tc;
  }

  public void Emit(TokenTextWriter stream, int level)
  {
    Contract.Requires(stream != null);
    if (!Anonymous)
    {
      stream.WriteLine(level, "{0}:",
        stream.Options.PrintWithUniqueASTIds
          ? String.Format("h{0}^^{1}", this.GetHashCode(), this.LabelName)
          : this.LabelName);
    }

    foreach (Cmd /*!*/ c in this.simpleCmds)
    {
      Contract.Assert(c != null);
      c.Emit(stream, level + 1);
    }

    if (this.ec != null)
    {
      this.ec.Emit(stream, level + 1);
    }
    else if (this.tc != null)
    {
      this.tc.Emit(stream, level + 1);
    }
  }
}