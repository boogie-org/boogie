using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST
{
  public class KeepOriginalNamer : ScopedNamer
  {

    public KeepOriginalNamer()
    {
    }

    private KeepOriginalNamer(KeepOriginalNamer namer) : base(namer)
    {
    }
    
    public override UniqueNamer Clone()
    {
      Contract.Ensures(Contract.Result<Object>() != null);
      return new KeepOriginalNamer(this);
    }

    protected override string GetModifiedName(string uniqueInherentName)
    {
      return uniqueInherentName;
    }
  }
}