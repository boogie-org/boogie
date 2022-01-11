using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST
{
  public class NormalizeNamer : ScopedNamer
  {
    public NormalizeNamer() : base()
    {
    }

    private NormalizeNamer(NormalizeNamer namer) : base(namer)
    {
      globalNewToOldName = new(namer.globalNewToOldName);
    }

    protected override string GetModifiedName(string uniqueInherentName)
    {
      return "$generated";
    }

    public override UniqueNamer Clone()
    {
      return new NormalizeNamer(this);
    }
  }
}