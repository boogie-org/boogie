namespace Microsoft.Boogie.VCExprAST
{
  public class DiscardOriginalName : KeepOriginalNamer
  {
    public DiscardOriginalName()
    {
    }

    protected DiscardOriginalName(KeepOriginalNamer namer) : base(namer)
    {
    }

    protected override string NextFreeName(object thingie, string baseName)
    {
      if (baseName != "ControlFlow") {
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