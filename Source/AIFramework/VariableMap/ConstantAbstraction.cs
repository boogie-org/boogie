//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Diagnostics.Contracts;
namespace Microsoft.AbstractInterpretationFramework {
  using System.Collections;
  using System.Diagnostics;
  //using System.Compiler.Analysis;
  using Microsoft.Basetypes;

  /// <summary>
  /// Represents an invariant over constant variable assignments.
  /// </summary>
  public class ConstantLattice : MicroLattice {
    enum Value {
      Top,
      Bottom,
      Constant
    }

    private class Elt : Element {
      public Value domainValue;
      public BigNum constantValue; // valid iff domainValue == Value.Constant

      public Elt(Value v) {
        this.domainValue = v;
      }

      public Elt(BigNum i) {
        this.domainValue = Value.Constant;
        this.constantValue = i;
      }

      public bool IsConstant {
        get {
          return this.domainValue == Value.Constant;
        }
      }

      public BigNum Constant {
        get {
          return this.constantValue;
        }
      } // only when IsConstant

      [Pure]
      public override System.Collections.Generic.ICollection<IVariable/*!*/>/*!*/ FreeVariables() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<System.Collections.Generic.ICollection<IVariable>>()));
        return cce.NonNull(new System.Collections.Generic.List<IVariable/*!*/>()).AsReadOnly();
      }

      public override Element/*!*/ Clone() {
        Contract.Ensures(Contract.Result<Element>() != null);
        if (this.IsConstant)
          return new Elt(constantValue);
        else
          return new Elt(domainValue);
      }
    }

    readonly IIntExprFactory/*!*/ factory;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(factory != null);
    }


    public ConstantLattice(IIntExprFactory/*!*/ factory) {
      Contract.Requires(factory != null);
      this.factory = factory;
      // base();
    }

    public override Element/*!*/ Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(Value.Top);
      }
    }

    public override Element/*!*/ Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(Value.Bottom);
      }
    }

    public override bool IsTop(Element/*!*/ element) {
      //Contract.Requires(element != null); 
      Elt e = (Elt)element;
      return e.domainValue == Value.Top;
    }

    public override bool IsBottom(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      return e.domainValue == Value.Bottom;
    }

    public override Element/*!*/ NontrivialJoin(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;
      Debug.Assert(a.domainValue == Value.Constant && b.domainValue == Value.Constant);
      return (a.constantValue.Equals(b.constantValue)) ? a : (Elt)Top;
    }

    public override Element/*!*/ NontrivialMeet(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;
      Debug.Assert(a.domainValue == Value.Constant && b.domainValue == Value.Constant);
      return (a.constantValue.Equals(b.constantValue)) ? a : (Elt)Bottom;
    }

    public override Element/*!*/ Widen(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return Join(first, second);
    }

    protected override bool AtMost(Element/*!*/ first, Element/*!*/ second) // this <= that
    {
      //Contract.Requires(first!= null);
      //Contract.Requires(second != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;
      return a.Constant.Equals(b.Constant);
    }

    public override IExpr/*!*/ ToPredicate(IVariable/*!*/ var, Element/*!*/ element) {
      //Contract.Requires(element != null);
      //Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      return factory.Eq(var, cce.NonNull(GetFoldExpr(element)));
    }

    public override IExpr GetFoldExpr(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      Contract.Assert(e.domainValue == Value.Constant);
      return factory.Const(e.constantValue);
    }

    public override bool Understands(IFunctionSymbol/*!*/ f, IList/*<IExpr!>*//*!*/ args) {
      //Contract.Requires(args != null);
      //Contract.Requires(f != null);
      return f.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq);
    }

    public override Element/*!*/ EvaluatePredicate(IExpr/*!*/ e) {
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);

      IFunApp nary = e as IFunApp;
      if (nary != null) {
        if (nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq)) {
          IList/*<IExpr!>*//*!*/ args = nary.Arguments;
          Contract.Assert(args != null);
          Contract.Assert(args.Count == 2);
          IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(args[0]);
          IExpr/*!*/ arg1 = (IExpr/*!*/)cce.NonNull(args[1]);

          // Look for "x == const" or "const == x".
          try {
            if (arg0 is IVariable) {
              BigNum z;
              if (Fold(arg1, out z)) {
                return new Elt(z);
              }
            } else if (arg1 is IVariable) {
              BigNum z;
              if (Fold(arg0, out z)) {
                return new Elt(z);
              }
            }
          } catch (System.ArithmeticException) {
            // fall through and return Top.  (Note, an alternative design may
            // consider returning Bottom.)
          }
        }
      }
      return Top;
    }

    /// <summary>
    /// Returns true if "expr" represents a constant integer expressions, in which case
    /// "z" returns as that integer.  Otherwise, returns false, in which case "z" should
    /// not be used by the caller.
    ///
    /// This method throws an System.ArithmeticException in the event that folding the
    /// constant expression results in an arithmetic overflow or division by zero.
    /// </summary>
    private bool Fold(IExpr/*!*/ expr, out BigNum z) {
      Contract.Requires(expr != null);
      IFunApp e = expr as IFunApp;
      if (e == null) {
        z = BigNum.ZERO;
        return false;
      }

      if (e.FunctionSymbol is IntSymbol) {
        z = ((IntSymbol)e.FunctionSymbol).Value;
        return true;

      } else if (e.FunctionSymbol.Equals(Int.Negate)) {
        IList/*<IExpr!>*//*!*/ args = e.Arguments;
        Contract.Assert(args != null);
        Contract.Assert(args.Count == 1);
        IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(args[0]);

        if (Fold(arg0, out z)) {
          z = z.Neg;
          return true;
        }

      } else if (e.Arguments.Count == 2) {
        IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(e.Arguments[0]);
        IExpr/*!*/ arg1 = (IExpr/*!*/)cce.NonNull(e.Arguments[1]);
        BigNum z0, z1;
        if (Fold(arg0, out z0) && Fold(arg1, out z1)) {
          if (e.FunctionSymbol.Equals(Int.Add)) {
            z = z0 + z1;
          } else if (e.FunctionSymbol.Equals(Int.Sub)) {
            z = z0 - z1;
          } else if (e.FunctionSymbol.Equals(Int.Mul)) {
            z = z0 * z1;
          } else if (e.FunctionSymbol.Equals(Int.Div)) {
            z = z0 / z1;
          } else if (e.FunctionSymbol.Equals(Int.Mod)) {
            z = z0 % z1;
          } else {
            z = BigNum.ZERO;
            return false;
          }
          return true;
        }
      }

      z = BigNum.ZERO;
      return false;
    }
  }
}
