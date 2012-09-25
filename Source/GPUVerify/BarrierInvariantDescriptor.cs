using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify {
  abstract class BarrierInvariantDescriptor {

    protected Expr Predicate;
    protected Expr BarrierInvariant;
    protected KernelDualiser Dualiser;

    public BarrierInvariantDescriptor(Expr Predicate, Expr BarrierInvariant, KernelDualiser Dualiser) {
      this.Predicate = Predicate;
      this.BarrierInvariant = BarrierInvariant;
      this.Dualiser = Dualiser;
    }

    internal abstract AssertCmd GetAssertCmd(QKeyValue Attributes);

    internal abstract List<AssumeCmd> GetInstantiationCmds();

    protected Expr NonNegative(Expr e) {
      return Dualiser.verifier.MakeBVSge(
        e, GPUVerifier.ZeroBV());
    }

    protected Expr NotTooLarge(Expr e) {
      return Dualiser.verifier.MakeBVSlt(e,
        new IdentifierExpr(Token.NoToken, 
          Dualiser.verifier.GetGroupSize("X")));
    }

  }
}
