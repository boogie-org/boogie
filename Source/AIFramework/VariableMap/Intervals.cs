//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
//using System.Compiler.Analysis;
using Microsoft.AbstractInterpretationFramework.Collections;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;

/////////////////////////////////////////////////////////////////////////////////
// An implementation of the interval abstract domain
/////////////////////////////////////////////////////////////////////////////////

namespace Microsoft.AbstractInterpretationFramework {
  public class IntervalLattice : MicroLattice {
    readonly ILinearExprFactory/*!*/ factory;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(factory != null);
    }


    public IntervalLattice(ILinearExprFactory/*!*/ factory) {
      Contract.Requires(factory != null);
      this.factory = factory;
      // base();
    }

    public override bool UnderstandsBasicArithmetics {
      get {
        return true;
      }
    }

    public override Element/*!*/ Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);

        return IntervalElement.Top;
      }
    }

    public override Element/*!*/ Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);

        return IntervalElement.Bottom;
      }
    }

    /// <summary>
    /// The paramter is the top?
    /// </summary>
    public override bool IsTop(Element/*!*/ element) {
      //Contract.Requires(element != null);
      IntervalElement interval = (IntervalElement)element;

      return interval.IsTop();
    }

    /// <summary>
    /// The parameter is the bottom?
    /// </summary>
    public override bool IsBottom(Element/*!*/ element) {
      //Contract.Requires(element != null);
      IntervalElement interval = (IntervalElement)element;

      return interval.IsBottom();
    }

    /// <summary>
    /// The classic, pointwise, join of intervals
    /// </summary>
    public override Element/*!*/ NontrivialJoin(Element/*!*/ left, Element/*!*/ right) {
      //Contract.Requires(right != null);
      //Contract.Requires(left != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      IntervalElement/*!*/ leftInterval = (IntervalElement/*!*/)cce.NonNull(left);
      IntervalElement/*!*/ rightInterval = (IntervalElement/*!*/)cce.NonNull(right);

      ExtendedInt inf = ExtendedInt.Inf(leftInterval.Inf, rightInterval.Inf);
      ExtendedInt sup = ExtendedInt.Sup(leftInterval.Sup, rightInterval.Sup);

      IntervalElement/*!*/ join = IntervalElement.Factory(inf, sup);

      return join;
    }

    /// <summary>
    /// The classic, pointwise, meet of intervals
    /// </summary>
    public override Element/*!*/ NontrivialMeet(Element/*!*/ left, Element/*!*/ right) {
      //Contract.Requires(right != null);
      //Contract.Requires(left != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      IntervalElement/*!*/ leftInterval = (IntervalElement/*!*/)cce.NonNull(left);
      IntervalElement/*!*/ rightInterval = (IntervalElement/*!*/)cce.NonNull(right);

      ExtendedInt inf = ExtendedInt.Sup(leftInterval.Inf, rightInterval.Inf);
      ExtendedInt sup = ExtendedInt.Inf(leftInterval.Sup, rightInterval.Sup);

      return IntervalElement.Factory(inf, sup);
    }


    /// <summary>
    /// The very simple widening of intervals, to be improved with thresholds
    /// left is the PREVIOUS value in the iterations and right is the NEW one
    /// </summary>
    public override Element/*!*/ Widen(Element/*!*/ left, Element/*!*/ right) {
      //Contract.Requires(right != null);
      //Contract.Requires(left != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      IntervalElement/*!*/ prevInterval = (IntervalElement/*!*/)cce.NonNull(left);
      IntervalElement/*!*/ nextInterval = (IntervalElement/*!*/)cce.NonNull(right);

      ExtendedInt inf = nextInterval.Inf < prevInterval.Inf ? ExtendedInt.MinusInfinity : prevInterval.Inf;
      ExtendedInt sup = nextInterval.Sup > prevInterval.Sup ? ExtendedInt.PlusInfinity : prevInterval.Sup;

      IntervalElement widening = IntervalElement.Factory(inf, sup);

      return widening;
    }


    /// <summary>
    /// Return true iff the interval left is containted in right
    /// </summary>
    protected override bool AtMost(Element/*!*/ left, Element/*!*/ right) {
      //Contract.Requires(right != null);
      //Contract.Requires(left != null);
      IntervalElement/*!*/ leftInterval = (IntervalElement/*!*/)cce.NonNull(left);
      IntervalElement/*!*/ rightInterval = (IntervalElement/*!*/)cce.NonNull(right);

      if (leftInterval.IsBottom() || rightInterval.IsTop())
        return true;

      return rightInterval.Inf <= leftInterval.Inf && leftInterval.Sup <= rightInterval.Sup;
    }

    /// <summary>
    /// Return just null
    /// </summary>
    public override IExpr GetFoldExpr(Element/*!*/ element) {
      //Contract.Requires(element != null);
      return null;
    }

    /// <summary>
    /// return a predicate inf "\leq x and x "\leq" sup (if inf [or sup] is not oo)
    /// </summary>
    public override IExpr/*!*/ ToPredicate(IVariable/*!*/ var, Element/*!*/ element) {
      //Contract.Requires(element != null);
      //Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      IntervalElement/*!*/ interval = (IntervalElement/*!*/)cce.NonNull(element);
      IExpr lowerBound = null;
      IExpr upperBound = null;

      if (!(interval.Inf is InfinitaryInt)) {
        IExpr constant = this.factory.Const(interval.Inf.Value);
        lowerBound = this.factory.AtMost(constant, var);        // inf <= var 
      }
      if (!(interval.Sup is InfinitaryInt)) {
        IExpr constant = this.factory.Const(interval.Sup.Value);
        upperBound = this.factory.AtMost(var, constant);       // var <= inf
      }

      if (lowerBound != null && upperBound != null)
        return this.factory.And(lowerBound, upperBound);        // inf <= var && var <= sup         
      else
        if (lowerBound != null)
          return lowerBound;
        else
          if (upperBound != null)
            return upperBound;
          else      // If we reach this point, both lowerBound and upperBound are null, i.e. we have no bounds on var, so we return simply true...
            return this.factory.True;
    }

    /// <summary>
    /// For the moment consider just equalities. Other case must be considered
    /// </summary>
    public override bool Understands(IFunctionSymbol/*!*/ f, IList /*<IExpr*//*!*/ args) {
      //Contract.Requires(args != null);
      //Contract.Requires(f != null);
      return f.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq);
    }


    /// <summary>
    /// Evaluate the predicate passed as input according the semantics of intervals
    /// </summary>
    public override Element/*!*/ EvaluatePredicate(IExpr/*!*/ pred) {
      //Contract.Requires(pred != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return this.EvaluatePredicateWithState(pred, null);
    }

    /// <summary>
    /// Evaluate the predicate passed as input according the semantics of intervals and the given state.
    /// Right now just basic arithmetic operations are supported. A future extension may consider an implementation of boolean predicates 
    /// </summary>
    public override Element/*!*/ EvaluatePredicateWithState(IExpr/*!*/ pred, IFunctionalMap/* Var -> Element */ state) {
      //Contract.Requires(pred != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      if (pred is IFunApp) {
        IFunApp fun = (IFunApp)pred;
        if (fun.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq)) // if it is a symbol of equality
        {
          IExpr/*!*/ leftArg = (IExpr/*!*/)cce.NonNull(fun.Arguments[0]);
          IExpr/*!*/ rightArg = (IExpr/*!*/)cce.NonNull(fun.Arguments[1]);
          if (leftArg is IVariable) {
            return Eval(rightArg, state);
          } else if (rightArg is IVariable) {
            return Eval(leftArg, state);
          }
        }
      }
      // otherwise we simply return Top
      return IntervalElement.Top;
    }

    /// <summary>
    /// Evaluate the expression (that is assured to be an arithmetic expression, in the state passed as a parameter
    /// </summary>
    private IntervalElement/*!*/ Eval(IExpr/*!*/ exp, IFunctionalMap/* Var -> Element */ state) {
      Contract.Requires((exp != null));
      Contract.Ensures(Contract.Result<IntervalElement>() != null);

      IntervalElement/*!*/ retVal = (IntervalElement/*!*/)cce.NonNull(Top);

      // Eval the expression by structural induction


      if (exp is IVariable && state != null) // A variable
      {
        object lookup = state[exp];
        if (lookup is IntervalElement)
          retVal = (IntervalElement)lookup;
        else {
          retVal = (IntervalElement)Top;
        }
      } else if (exp is IFunApp) {
        IFunApp fun = (IFunApp)exp;

        if (fun.FunctionSymbol is IntSymbol)   // An integer
        {
          IntSymbol intSymb = (IntSymbol)fun.FunctionSymbol;
          BigNum val = intSymb.Value;

          retVal = IntervalElement.Factory(val);
        } else if (fun.FunctionSymbol.Equals(Int.Negate)) // An unary minus
        {
          IExpr/*!*/ arg = (IExpr/*!*/)cce.NonNull(fun.Arguments[0]);
          IntervalElement/*!*/ argEval = Eval(arg, state);
          Contract.Assert(argEval != null);
          IntervalElement/*!*/ zero = IntervalElement.Factory(BigNum.ZERO);
          Contract.Assert(zero != null);

          retVal = zero - argEval;
        } else if (fun.Arguments.Count == 2) {
          IExpr/*!*/ left = (IExpr/*!*/)cce.NonNull(fun.Arguments[0]);
          IExpr/*!*/ right = (IExpr/*!*/)cce.NonNull(fun.Arguments[1]);

          IntervalElement/*!*/ leftVal = Eval(left, state);
          Contract.Assert(leftVal != null);
          IntervalElement/*!*/ rightVal = Eval(right, state);
          Contract.Assert(rightVal != null);

          if (fun.FunctionSymbol.Equals(Int.Add))
            retVal = leftVal + rightVal;
          else if (fun.FunctionSymbol.Equals(Int.Sub))
            retVal = leftVal - rightVal;
          else if (fun.FunctionSymbol.Equals(Int.Mul))
            retVal = leftVal * rightVal;
          else if (fun.FunctionSymbol.Equals(Int.Div))
            retVal = leftVal / rightVal;
          else if (fun.FunctionSymbol.Equals(Int.Mod))
            retVal = leftVal % rightVal;
        }
      }

      return retVal;
    }

    /// <summary> 
    /// Inner class standing for an interval on integers, possibly unbounded
    /// </summary>
    private class IntervalElement : Element {
      protected static readonly IntervalElement/*!*/ TopInterval = new IntervalElement(new MinusInfinity(), new PlusInfinity());    // Top    = [-oo , +oo]
      protected static readonly IntervalElement/*!*/ BottomInterval = new IntervalElement(new PlusInfinity(), new MinusInfinity()); // Bottom = [+oo, -oo] 

      private readonly ExtendedInt/*!*/ inf;
      private readonly ExtendedInt/*!*/ sup;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(inf != null);
        Contract.Invariant(sup != null);
      }

      public ExtendedInt/*!*/ Inf {
        get {
          Contract.Ensures(Contract.Result<ExtendedInt>() != null);

          return inf;
        }
      }

      public ExtendedInt/*!*/ Sup {
        get {
          Contract.Ensures(Contract.Result<ExtendedInt>() != null);

          return sup;
        }
      }

      // Construct the inteval [val, val]
      protected IntervalElement(BigNum val) {
        this.inf = this.sup = ExtendedInt.Factory(val);
        // base();
      }

      // Construct the interval [inf, sup]
      protected IntervalElement(BigNum infInt, BigNum supInt) {
        this.inf = ExtendedInt.Factory(infInt);
        this.sup = ExtendedInt.Factory(supInt);
        // base();   // to please the compiler...
      }

      protected IntervalElement(ExtendedInt/*!*/ inf, ExtendedInt/*!*/ sup) {
        Contract.Requires(sup != null);
        Contract.Requires(inf != null);
        this.inf = inf;
        this.sup = sup;
        // base();
      }

      // Construct an Interval
      public static IntervalElement/*!*/ Factory(ExtendedInt/*!*/ inf, ExtendedInt/*!*/ sup) {
        Contract.Requires((sup != null));
        Contract.Requires((inf != null));
        Contract.Ensures(Contract.Result<IntervalElement>() != null);
        if (inf is MinusInfinity && sup is PlusInfinity)
          return Top;
        if (inf > sup)
          return Bottom;
        // otherwise...
        return new IntervalElement(inf, sup);
      }

      public static IntervalElement/*!*/ Factory(BigNum i) {
        Contract.Ensures(Contract.Result<IntervalElement>() != null);
        return new IntervalElement(i);
      }

      public static IntervalElement/*!*/ Factory(BigNum inf, BigNum sup) {
        Contract.Ensures(Contract.Result<IntervalElement>() != null);
        ExtendedInt/*!*/ i = ExtendedInt.Factory(inf);
        ExtendedInt/*!*/ s = ExtendedInt.Factory(sup);

        return Factory(i, s);
      }

      static public IntervalElement/*!*/ Top {
        get {
          Contract.Ensures(Contract.Result<IntervalElement>() != null);

          return TopInterval;
        }
      }

      static public IntervalElement/*!*/ Bottom {
        get {
          Contract.Ensures(Contract.Result<IntervalElement>() != null);

          return BottomInterval;
        }
      }

      public bool IsTop() {
        return this.inf is MinusInfinity && this.sup is PlusInfinity;
      }

      public bool IsBottom() {
        return this.inf > this.sup;
      }

      #region Below are the arithmetic operations lifted to intervals

      // Addition
      public static IntervalElement/*!*/ operator +(IntervalElement/*!*/ a, IntervalElement/*!*/ b) {
        Contract.Requires(b != null);
        Contract.Requires(a != null);
        Contract.Ensures(Contract.Result<IntervalElement>() != null);
        ExtendedInt/*!*/ inf = a.inf + b.inf;
        Contract.Assert(inf != null);
        ExtendedInt/*!*/ sup = a.sup + b.sup;
        Contract.Assert(sup != null);

        return Factory(inf, sup);
      }

      // Subtraction
      public static IntervalElement/*!*/ operator -(IntervalElement/*!*/ a, IntervalElement/*!*/ b) {
        Contract.Requires(b != null);
        Contract.Requires(a != null);
        Contract.Ensures(Contract.Result<IntervalElement>() != null);
        ExtendedInt/*!*/ inf = a.inf - b.sup;
        Contract.Assert(inf != null);

        ExtendedInt/*!*/ sup = a.sup - b.inf;
        Contract.Assert(sup != null);
        IntervalElement/*!*/ sub = Factory(inf, sup);
        Contract.Assert(sub != null);

        return sub;
      }

      // Multiplication
      public static IntervalElement/*!*/ operator *(IntervalElement/*!*/ a, IntervalElement/*!*/ b) {
        Contract.Requires(b != null);
        Contract.Requires(a != null);
        Contract.Ensures(Contract.Result<IntervalElement>() != null);
        ExtendedInt/*!*/ infinf = a.inf * b.inf;
        Contract.Assert(infinf != null);
        ExtendedInt/*!*/ infsup = a.inf * b.sup;
        Contract.Assert(infsup != null);
        ExtendedInt/*!*/ supinf = a.sup * b.inf;
        Contract.Assert(supinf != null);
        ExtendedInt/*!*/ supsup = a.sup * b.sup;
        Contract.Assert(supsup != null);

        ExtendedInt/*!*/ inf = ExtendedInt.Inf(infinf, infsup, supinf, supsup);
        Contract.Assert(inf != null);
        ExtendedInt/*!*/ sup = ExtendedInt.Sup(infinf, infsup, supinf, supsup);
        Contract.Assert(sup != null);

        return Factory(inf, sup);
      }

      // Division
      public static IntervalElement/*!*/ operator /(IntervalElement/*!*/ a, IntervalElement/*!*/ b) {
        Contract.Requires(b != null);
        Contract.Requires(a != null);
        Contract.Ensures(Contract.Result<IntervalElement>() != null);
        if (b.inf.IsZero && b.sup.IsZero)   //  Check division by zero
          return IntervalElement.Top;

        ExtendedInt/*!*/ infinf = a.inf / b.inf;
        Contract.Assert(infinf != null);
        ExtendedInt/*!*/ infsup = a.inf / b.sup;
        Contract.Assert(infsup != null);
        ExtendedInt/*!*/ supinf = a.sup / b.inf;
        Contract.Assert(supinf != null);
        ExtendedInt/*!*/ supsup = a.sup / b.sup;
        Contract.Assert(supsup != null);

        ExtendedInt/*!*/ inf = ExtendedInt.Inf(infinf, infsup, supinf, supsup);
        Contract.Assert(inf != null);
        ExtendedInt/*!*/ sup = ExtendedInt.Sup(infinf, infsup, supinf, supsup);
        Contract.Assert(sup != null);

        return Factory(inf, sup);
      }

      // Division
      public static IntervalElement/*!*/ operator %(IntervalElement/*!*/ a, IntervalElement/*!*/ b) {
        Contract.Requires(b != null);
        Contract.Requires(a != null);
        Contract.Ensures(Contract.Result<IntervalElement>() != null);
        if (b.inf.IsZero && b.sup.IsZero)   //  Check division by zero
          return IntervalElement.Top;

        ExtendedInt/*!*/ infinf = a.inf % b.inf;
        Contract.Assert(infinf != null);
        ExtendedInt/*!*/ infsup = a.inf % b.sup;
        Contract.Assert(infsup != null);
        ExtendedInt/*!*/ supinf = a.sup % b.inf;
        Contract.Assert(supinf != null);
        ExtendedInt/*!*/ supsup = a.sup % b.sup;
        Contract.Assert(supsup != null);

        ExtendedInt inf = ExtendedInt.Inf(infinf, infsup, supinf, supsup);
        ExtendedInt sup = ExtendedInt.Sup(infinf, infsup, supinf, supsup);

        return Factory(inf, sup);
      }

      #endregion

      #region Overriden methods

      public override Element/*!*/ Clone() {
        Contract.Ensures(Contract.Result<Element>() != null);
        // Real copying should not be needed because intervals are immutable?
        return this;
        /*
            int valInf = this.inf.Value;
            int valSup = this.sup.Value;

            ExtendedInt clonedInf = ExtendedInt.Factory(valInf);
            ExtendedInt clonedSup = ExtendedInt.Factory(valSup);

            return Factory(clonedInf, clonedSup);
            */
      }

      [Pure]
      public override System.Collections.Generic.ICollection<IVariable/*!*/>/*!*/ FreeVariables() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<System.Collections.Generic.ICollection<IVariable>>()));
        return cce.NonNull(new System.Collections.Generic.List<IVariable/*!*/>()).AsReadOnly();
      }

      [Pure]
      public override string/*!*/ ToString() {
        Contract.Ensures(Contract.Result<string>() != null);
        return "[" + this.inf + ", " + this.sup + "]";
      }

      #endregion
    }
  }


  /// The interface for an extended integer
  /// 
  [ContractClass(typeof(ExtendedIntContracts))]
  abstract class ExtendedInt {
    private static readonly PlusInfinity/*!*/ cachedPlusInf = new PlusInfinity();
    private static readonly MinusInfinity/*!*/ cachedMinusInf = new MinusInfinity();

    static public ExtendedInt/*!*/ PlusInfinity {
      get {
        Contract.Ensures(Contract.Result<ExtendedInt>() != null);

        return cachedPlusInf;
      }
    }

    static public ExtendedInt/*!*/ MinusInfinity {
      get {
        Contract.Ensures(Contract.Result<ExtendedInt>() != null);

        return cachedMinusInf;
      }
    }

    public abstract BigNum Value {
      get;
    }

    public abstract int Signum {
      get;
    }

    public bool IsZero {
      get {
        return Signum == 0;
      }
    }

    public bool IsPositive {
      get {
        return Signum > 0;
      }
    }

    public bool IsNegative {
      get {
        return Signum < 0;
      }
    }


    #region Below are the extensions of arithmetic operations on extended integers

    // Addition
    public static ExtendedInt/*!*/ operator +(ExtendedInt/*!*/ a, ExtendedInt/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      if (a is InfinitaryInt) {
        return a;
      } else if (b is InfinitaryInt) {
        return b;
      } else {
        return ExtendedInt.Factory(a.Value + b.Value);
      }
    }

    // Subtraction
    public static ExtendedInt/*!*/ operator -(ExtendedInt/*!*/ a, ExtendedInt/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      if (a is InfinitaryInt) {
        return a;
      } else if (b is InfinitaryInt) {
        return UnaryMinus(b);
      } else {
        return ExtendedInt.Factory(a.Value - b.Value);
      }
    }

    // Unary minus
    public static ExtendedInt/*!*/ operator -(ExtendedInt/*!*/ a) {
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      // BUGBUG: Some compiler error prevents the unary minus operator from being used
      return UnaryMinus(a);
    }

    // Unary minus
    public static ExtendedInt/*!*/ UnaryMinus(ExtendedInt/*!*/ a) {
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      if (a is PlusInfinity)
        return cachedMinusInf;
      if (a is MinusInfinity)
        return cachedPlusInf;
      else // a is a PureInteger
        return new PureInteger(-a.Value);
    }

    // Multiplication
    public static ExtendedInt/*!*/ operator *(ExtendedInt/*!*/ a, ExtendedInt/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      if (a.IsZero) {
        return a;
      } else if (b.IsZero) {
        return b;
      } else if (a is InfinitaryInt) {
        if (b.IsPositive) {
          return a;
        } else {
          return UnaryMinus(a);
        }
      } else if (b is InfinitaryInt) {
        if (a.IsPositive) {
          return b;
        } else {
          return UnaryMinus(b);
        }
      } else {
        return ExtendedInt.Factory(a.Value * b.Value);
      }
    }

    // Division
    public static ExtendedInt/*!*/ operator /(ExtendedInt/*!*/ a, ExtendedInt/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      if (b.IsZero) {
        return a.IsPositive ? (ExtendedInt)cachedPlusInf : cachedMinusInf;
      }
      if (a is InfinitaryInt) {
        return a;
      } else if (b is InfinitaryInt) {
        return b;
      } else {
        return ExtendedInt.Factory(a.Value / b.Value);
      }
    }

    // Modulo
    public static ExtendedInt/*!*/ operator %(ExtendedInt/*!*/ a, ExtendedInt/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      if (b.IsZero) {
        return a.IsPositive ? (ExtendedInt)cachedPlusInf : cachedMinusInf;
      }
      if (a is InfinitaryInt) {
        return a;
      } else if (b is InfinitaryInt) {
        return b;
      } else {
        return ExtendedInt.Factory(a.Value % b.Value);
      }
    }

    #endregion

    #region Inf and Sup operations

    public abstract int CompareTo(ExtendedInt/*!*/ that);

    public static bool operator <(ExtendedInt/*!*/ inf, ExtendedInt/*!*/ sup) {
      Contract.Requires(sup != null);
      Contract.Requires(inf != null);
      return inf.CompareTo(sup) < 0;
    }

    public static bool operator >(ExtendedInt/*!*/ inf, ExtendedInt/*!*/ sup) {
      Contract.Requires(sup != null);
      Contract.Requires(inf != null);
      return inf.CompareTo(sup) > 0;
    }

    public static bool operator <=(ExtendedInt/*!*/ inf, ExtendedInt/*!*/ sup) {
      Contract.Requires(sup != null);
      Contract.Requires(inf != null);
      return inf.CompareTo(sup) <= 0;
    }

    public static bool operator >=(ExtendedInt/*!*/ inf, ExtendedInt/*!*/ sup) {
      Contract.Requires(sup != null);
      Contract.Requires(inf != null);
      Contract.Requires(inf != null && sup != null);
      return inf.CompareTo(sup) >= 0;
    }

    public static ExtendedInt/*!*/ Inf(ExtendedInt/*!*/ inf, ExtendedInt/*!*/ sup) {
      Contract.Requires(sup != null);
      Contract.Requires(inf != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      if (inf < sup)
        return inf;
      else
        return sup;
    }

    public static ExtendedInt/*!*/ Inf(ExtendedInt/*!*/ a, ExtendedInt/*!*/ b, ExtendedInt/*!*/ c, ExtendedInt/*!*/ d) {
      Contract.Requires(d != null);
      Contract.Requires(c != null);
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      ExtendedInt/*!*/ infab = Inf(a, b);
      Contract.Assert(infab != null);
      ExtendedInt/*!*/ infcd = Inf(c, d);
      Contract.Assert(infcd != null);

      return Inf(infab, infcd);
    }

    public static ExtendedInt/*!*/ Sup(ExtendedInt/*!*/ inf, ExtendedInt/*!*/ sup) {
      Contract.Requires(sup != null);
      Contract.Requires(inf != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      if (inf > sup)
        return inf;
      else
        return sup;
    }

    public static ExtendedInt/*!*/ Sup(ExtendedInt/*!*/ a, ExtendedInt/*!*/ b, ExtendedInt/*!*/ c, ExtendedInt/*!*/ d) {
      Contract.Requires(d != null);
      Contract.Requires(c != null);
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      ExtendedInt/*!*/ supab = Sup(a, b);
      Contract.Assert(supab != null);
      ExtendedInt/*!*/ supcd = Sup(c, d);
      Contract.Assert(supcd != null);

      return Sup(supab, supcd);
    }

    #endregion

    // Return the ExtendedInt corresponding to the value
    public static ExtendedInt/*!*/ Factory(BigNum val) {
      Contract.Ensures(Contract.Result<ExtendedInt>() != null);
      return new PureInteger(val);
    }
  }
  [ContractClassFor(typeof(ExtendedInt))]
  abstract class ExtendedIntContracts : ExtendedInt {
    public override int CompareTo(ExtendedInt that) {
      Contract.Requires(that != null);
      throw new NotImplementedException();
    }
  }

  // Stands for a normal (finite) integer x
  class PureInteger : ExtendedInt {
    public PureInteger(BigNum i) {
      this.val = i;
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return this.Value.ToString();
    }

    private BigNum val;
    public override BigNum Value {
      get {
        return this.val;
      }
    }

    public override int Signum {
      get {
        return val.Signum;
      }
    }

    public override int CompareTo(ExtendedInt/*!*/ that) {
      //Contract.Requires(that != null);
      if (that is PlusInfinity)
        return -1;
      else if (that is PureInteger)
        return this.Value.CompareTo(that.Value);
      else // then that is a MinusInfinity
        return 1;
    }
  }

  abstract class InfinitaryInt : ExtendedInt {
    public override BigNum Value {
      get {
        throw new InvalidOperationException();
      }
    }
  }

  class PlusInfinity : InfinitaryInt {
    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return "+oo";
    }

    public override int Signum {
      get {
        return 1;
      }
    }

    public override int CompareTo(ExtendedInt/*!*/ that) {
      //Contract.Requires(that != null);
      if (that is PlusInfinity)
        return 0;
      else
        return 1;
    }
  }

  class MinusInfinity : InfinitaryInt {
    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return "-oo";
    }

    public override int Signum {
      get {
        return -1;
      }
    }

    public override int CompareTo(ExtendedInt/*!*/ that) {
      //Contract.Requires(that != null);
      if (that is MinusInfinity)
        return 0;
      else
        return -1;
    }
  }
}
