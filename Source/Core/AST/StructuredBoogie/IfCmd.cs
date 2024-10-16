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
}