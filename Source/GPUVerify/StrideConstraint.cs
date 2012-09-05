using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Basetypes;
using Microsoft.Boogie;

namespace GPUVerify {

class StrideConstraint {

  public static StrideConstraint Bottom(Expr e) {
    int width = e.Type.BvBits;
    return new ModStrideConstraint(new LiteralExpr(Token.NoToken, BigNum.FromInt(1), width),
                                   new LiteralExpr(Token.NoToken, BigNum.FromInt(0), width));
  }

  public bool IsBottom() {
    var msc = this as ModStrideConstraint;
    if (msc == null)
        return false;

    var le = msc.mod as LiteralExpr;
    if (le == null)
        return false;

    var bvc = le.Val as BvConst;
    if (bvc == null)
        return false;

    return bvc.Value.InInt32 && bvc.Value.ToInt == 1;
  }

  private Expr ExprModPow2(GPUVerifier verifier, Expr expr, Expr powerOfTwoExpr) {
    Expr Pow2Minus1 = verifier.MakeBVSub(powerOfTwoExpr, 
                                         new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 32));

    return verifier.MakeBVAnd(Pow2Minus1, expr);
  }

  public Expr MaybeBuildPredicate(GPUVerifier verifier, Expr e) {
    var msc = this as ModStrideConstraint;
    if (msc != null && !msc.IsBottom()) {
      Expr modEqExpr = Expr.Eq(ExprModPow2(verifier, e, msc.mod), ExprModPow2(verifier, msc.modEq, msc.mod));
      return modEqExpr;
    }

    return null;
  }

  private static StrideConstraint BuildAddStrideConstraint(GPUVerifier verifier, Expr e, StrideConstraint lhsc, StrideConstraint rhsc) {
    if (lhsc is EqStrideConstraint && rhsc is EqStrideConstraint) {
      return new EqStrideConstraint(e);
    }

    if (lhsc is EqStrideConstraint && rhsc is ModStrideConstraint)
      return BuildAddStrideConstraint(verifier, e, rhsc, lhsc);

    if (lhsc is ModStrideConstraint && rhsc is EqStrideConstraint) {
      var lhsmc = (ModStrideConstraint)lhsc;
      var rhsec = (EqStrideConstraint)rhsc;

      return new ModStrideConstraint(lhsmc.mod, verifier.MakeBVAdd(lhsmc.modEq, rhsec.eq));
    }

    if (lhsc is ModStrideConstraint && rhsc is ModStrideConstraint) {
      var lhsmc = (ModStrideConstraint)lhsc;
      var rhsmc = (ModStrideConstraint)rhsc;

      if (lhsmc.mod == rhsmc.mod)
        return new ModStrideConstraint(lhsmc.mod, verifier.MakeBVAdd(lhsmc.modEq, rhsmc.modEq));
    }

    return Bottom(e);
  }

  private static StrideConstraint BuildMulStrideConstraint(GPUVerifier verifier, Expr e, StrideConstraint lhsc, StrideConstraint rhsc) {
    if (lhsc is EqStrideConstraint && rhsc is EqStrideConstraint) {
      return new EqStrideConstraint(e);
    }

    if (lhsc is EqStrideConstraint && rhsc is ModStrideConstraint)
      return BuildMulStrideConstraint(verifier, e, rhsc, lhsc);

    if (lhsc is ModStrideConstraint && rhsc is EqStrideConstraint) {
      var lhsmc = (ModStrideConstraint)lhsc;
      var rhsec = (EqStrideConstraint)rhsc;

      return new ModStrideConstraint(verifier.MakeBVMul(lhsmc.mod, rhsec.eq),
                                     verifier.MakeBVMul(lhsmc.modEq, rhsec.eq));
    }

    return Bottom(e);
  }

  public static StrideConstraint FromExpr(GPUVerifier verifier, Implementation impl, Expr e) {
    if (e is LiteralExpr)
      return new EqStrideConstraint(e);

    var ie = e as IdentifierExpr;
    if (ie != null) {
      if(GPUVerifier.IsConstantInCurrentRegion(ie))
        return new EqStrideConstraint(e);

      var rsa = verifier.reducedStrengthAnalyses[impl];
      var sc = rsa.GetStrideConstraint(ie.Decl.Name);
      if (sc == null)
        return Bottom(e);
      return sc;
    }

    Expr lhs, rhs;

    if (GPUVerifier.IsBVAdd(e, out lhs, out rhs)) {
      var lhsc = FromExpr(verifier, impl, lhs);
      var rhsc = FromExpr(verifier, impl, rhs);
      return BuildAddStrideConstraint(verifier, e, lhsc, rhsc);
    }

    if (GPUVerifier.IsBVMul(e, out lhs, out rhs)) {
      var lhsc = FromExpr(verifier, impl, lhs);
      var rhsc = FromExpr(verifier, impl, rhs);
      return BuildMulStrideConstraint(verifier, e, lhsc, rhsc);
    }

    return Bottom(e);
  }

}

class EqStrideConstraint : StrideConstraint {
  public EqStrideConstraint(Expr eq) { this.eq = eq; }
  public Expr eq;
}

class ModStrideConstraint : StrideConstraint {
  public ModStrideConstraint(Expr mod, Expr modEq) { this.mod = mod; this.modEq = modEq; }
  public Expr mod, modEq;
}

}
