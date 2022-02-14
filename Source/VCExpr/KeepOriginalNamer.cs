using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST
{
  public class KeepOriginalNamer : ScopedNamer
  {

    public KeepOriginalNamer()
    {
    }

    public KeepOriginalNamer(ScopedNamer namer) : base(namer)
    {
    }

    public static KeepOriginalNamer Create(ScopedNamer namer = null) {
      return namer != null ? new KeepOriginalNamer(namer) : new KeepOriginalNamer();
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