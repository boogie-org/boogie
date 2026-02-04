using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class IfCmd : StructuredCmd
{
  public QKeyValue Attributes;
  public Expr Guard;

  private StmtList thn;

  public StmtList Thn
  {
    get
    {
      
      return this.thn;
    }
    set
    {
      
      this.thn = value;
    }
  }

  private IfCmd elseIf;

  public IfCmd ElseIf
  {
    get { return this.elseIf; }
    set
    {
      
      this.elseIf = value;
    }
  }

  private StmtList elseBlock;

  public StmtList ElseBlock
  {
    get { return this.elseBlock; }
    set
    {
      
      this.elseBlock = value;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(this.thn != null);
    Contract.Invariant(this.elseIf == null || this.elseBlock == null);
  }

  public IfCmd(IToken tok, Expr guard, StmtList thn, IfCmd elseIf, StmtList elseBlock, 
    QKeyValue attributes = null)
    : base(tok)
  {
    
    
    
    this.Guard = guard;
    this.thn = thn;
    this.elseIf = elseIf;
    this.elseBlock = elseBlock;
    Attributes = attributes;
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    stream.Write(level, "if (");
    var ifcmd = this;
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