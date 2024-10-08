using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class IfCmd : StructuredCmd
{
  public Expr Guard;

  private StmtList /*!*/ thn;

  public StmtList /*!*/ Thn
  {
    get
    {
      Contract.Ensures(Contract.Result<StmtList>() != null);
      return this.thn;
    }
    set
    {
      Contract.Requires(value != null);
      this.thn = value;
    }
  }

  private IfCmd elseIf;

  public IfCmd ElseIf
  {
    get { return this.elseIf; }
    set
    {
      Contract.Requires(value == null || this.ElseBlock == null);
      this.elseIf = value;
    }
  }

  private StmtList elseBlock;

  public StmtList ElseBlock
  {
    get { return this.elseBlock; }
    set
    {
      Contract.Requires(value == null || this.ElseIf == null);
      this.elseBlock = value;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(this.thn != null);
    Contract.Invariant(this.elseIf == null || this.elseBlock == null);
  }

  public IfCmd(IToken /*!*/ tok, Expr guard, StmtList /*!*/ thn, IfCmd elseIf, StmtList elseBlock)
    : base(tok)
  {
    Contract.Requires(tok != null);
    Contract.Requires(thn != null);
    Contract.Requires(elseIf == null || elseBlock == null);
    this.Guard = guard;
    this.thn = thn;
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
}