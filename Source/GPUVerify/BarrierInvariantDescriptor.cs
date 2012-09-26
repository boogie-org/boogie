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
    protected QKeyValue SourceLocationInfo;
    protected KernelDualiser Dualiser;
    protected string ProcName;

    public BarrierInvariantDescriptor(Expr Predicate, Expr BarrierInvariant,
          QKeyValue SourceLocationInfo,
          KernelDualiser Dualiser, string ProcName) {
      this.Predicate = Predicate;
      this.BarrierInvariant = BarrierInvariant;
      this.SourceLocationInfo = SourceLocationInfo;
      this.Dualiser = Dualiser;
      this.ProcName = ProcName;
    }

    internal abstract AssertCmd GetAssertCmd();

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
