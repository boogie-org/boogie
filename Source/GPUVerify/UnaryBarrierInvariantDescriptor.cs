using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify {
  class UnaryBarrierInvariantDescriptor : BarrierInvariantDescriptor {
    private List<Expr> InstantiationExprs;

    public UnaryBarrierInvariantDescriptor(Expr Predicate, Expr BarrierInvariant, KernelDualiser Dualiser) : 
      base(Predicate, BarrierInvariant, Dualiser) {
      InstantiationExprs = new List<Expr>();
    }

    public void AddInstantiationExpr(Expr InstantiationExpr) {
      InstantiationExprs.Add(InstantiationExpr);
    }

    internal override AssertCmd GetAssertCmd(QKeyValue Attributes) {
      var vd = new VariableDualiser(1, null, null);
      return new AssertCmd(
        Token.NoToken,
        vd.VisitExpr(Expr.Imp(Predicate, BarrierInvariant)),
        Dualiser.MakeThreadSpecificAttributes(Attributes, 1));
    }

    internal override List<AssumeCmd> GetInstantiationCmds() {
      var result = new List<AssumeCmd>();
      foreach (var Instantiation in InstantiationExprs) {
        foreach (var Thread in new int[] { 1, 2 }) {
          var vd = new VariableDualiser(Thread, null, null);
          var ThreadInstantiationExpr = vd.VisitExpr(Instantiation);
          var ti = new ThreadInstantiator(Dualiser.verifier, ThreadInstantiationExpr, Thread);

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
