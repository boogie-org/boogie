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

    public NormalizeNamer(ScopedNamer namer) : base(namer)
    {
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