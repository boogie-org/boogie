namespace Microsoft.Boogie.VCExprAST
{
  public class TrashOriginalName : KeepOriginalNamer
  {
    public TrashOriginalName()
    {
    }

    protected TrashOriginalName(KeepOriginalNamer namer) : base(namer)
    {
    }

    protected override string NextFreeName(object thingie, string baseName)
    {
      if (baseName != "ControlFlow") {
        baseName = "b";
      }
      return base.NextFreeName(thingie, baseName);
    }
    
    public override TrashOriginalName Clone()
    {
      return new TrashOriginalName(this);
    }
  }
}