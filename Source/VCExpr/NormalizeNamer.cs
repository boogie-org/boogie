using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST {
  public class NormalizeNamer : ScopedNamer {
    public NormalizeNamer() : base() {
    }

    public NormalizeNamer(ScopedNamer namer) : base(namer) {
    }

    public static NormalizeNamer Create(ScopedNamer namer = null) {
      return namer != null ? new NormalizeNamer(namer) : new NormalizeNamer();
    }

    protected override string GetModifiedName(string uniqueInherentName) {
      return "$generated";
    }

    public override UniqueNamer Clone() {
      return new NormalizeNamer(this);
    }
  }
}