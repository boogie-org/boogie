namespace Microsoft.Boogie.VCExprAST
{
  public class DiscardOriginalName : KeepOriginalNamer
  {
    private const string controlFlow = "ControlFlow"; // This is a hardcoded name used by Boogie to inspect the SMT model.

    public DiscardOriginalName()
    {
    }

    protected DiscardOriginalName(KeepOriginalNamer namer) : base(namer)
    {
    }

    protected override string NextFreeName(object thingie, string baseName)
    {
      if (baseName != controlFlow) {
        baseName = "b";
      }
      return base.NextFreeName(thingie, baseName);
    }
    
    public override DiscardOriginalName Clone()
    {
      return new DiscardOriginalName(this);
    }
  }
}