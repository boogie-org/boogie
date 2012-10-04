using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify {
  class UnaryBarrierInvariantDescriptor : BarrierInvariantDescriptor {
    private List<Expr> InstantiationExprs;

    public UnaryBarrierInvariantDescriptor(Expr Predicate, Expr BarrierInvariant,
        QKeyValue SourceLocationInfo, KernelDualiser Dualiser, string ProcName) : 
      base(Predicate, BarrierInvariant, SourceLocationInfo, Dualiser, ProcName) {
      InstantiationExprs = new List<Expr>();
    }

    public void AddInstantiationExpr(Expr InstantiationExpr) {
      InstantiationExprs.Add(InstantiationExpr);
    }

    internal override AssertCmd GetAssertCmd() {
      var vd = new VariableDualiser(1, Dualiser.verifier.uniformityAnalyser, ProcName);
      return new AssertCmd(
        Token.NoToken,
        vd.VisitExpr(Expr.Imp(Predicate, BarrierInvariant)),
        Dualiser.MakeThreadSpecificAttributes(SourceLocationInfo, 1));
    }

    internal override List<AssumeCmd> GetInstantiationCmds() {
      var result = new List<AssumeCmd>();
      foreach (var Instantiation in InstantiationExprs) {
        foreach (var Thread in new int[] { 1, 2 }) {
          var vd = new VariableDualiser(Thread, Dualiser.verifier.uniformityAnalyser, ProcName);
          var ThreadInstantiationExpr = vd.VisitExpr(Instantiation);
          var ti = new ThreadInstantiator(ThreadInstantiationExpr, Thread, 
            Dualiser.verifier.uniformityAnalyser, ProcName);

          result.Add(new AssumeCmd(
            Token.NoToken,
            Expr.Imp(vd.VisitExpr(Predicate),
              Expr.Imp(Expr.And(
                NonNegative(ThreadInstantiationExpr),
                NotTooLarge(ThreadInstantiationExpr)),
              ti.VisitExpr(BarrierInvariant)))));
        }
      }
      return result;
    }

  }
}
