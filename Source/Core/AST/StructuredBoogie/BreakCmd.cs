using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class BreakCmd : StructuredCmd
{
  public string Label;
  public BigBlock BreakEnclosure;

  public BreakCmd(IToken tok, string label)
    : base(tok)
  {
    
    this.Label = label;
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    if (Label == null)
    {
      stream.WriteLine(level, "break;");
    }
    else
    {
      stream.WriteLine(level, "break {0};", Label);
    }
  }
}