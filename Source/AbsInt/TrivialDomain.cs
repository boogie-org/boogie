using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.AbstractInterpretation
{
  class TrivialDomain : NativeLattice
  {
    class E : NativeLattice.Element
    {
      public readonly bool IsTop;
      public E(bool isTop) {
        IsTop = isTop;
      }

      public override Expr ToExpr() {
        return Expr.Literal(IsTop);
      }
    }

    private E top = new E(true);
    private E bottom = new E(false);

    public override Element Top { get { return top; } }
    public override Element Bottom { get { return bottom; } }

    public override bool IsTop(Element element) {
      var e = (E)element;
      return e.IsTop;
    }
    public override bool IsBottom(Element element) {
      var e = (E)element;
      return !e.IsTop;
    }

    public override bool Below(Element a, Element b) {
      return IsBottom(a) || IsTop(b);
    }

    public override Element Meet(Element a, Element b) {
      if (IsBottom(b)) {
        return b;
      } else {
        return a;
      }
    }

    public override Element Join(Element a, Element b) {
      if (IsTop(b)) {
        return b;
      } else {
        return a;
      }
    }

    public override Element Widen(Element a, Element b) {
      return Join(a, b);  // it's a finite domain, after all
    }

    public override Element Constrain(Element element, Expr expr) {
      var e = (E)element;
      var lit = expr as LiteralExpr;
      if (lit != null && lit.isBool && !(bool)lit.Val) {
        return bottom;
      } else {
        return e;
      }
    }

    public override Element Update(Element element, AssignCmd cmd) {
      return element;
    }

    public override Element Eliminate(Element element, Variable v) {
      return element;
    }
  }
}
