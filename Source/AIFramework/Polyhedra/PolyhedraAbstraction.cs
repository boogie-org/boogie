//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework {
  using System;
  using System.Collections;
  using System.Collections.Generic;
  using System.Diagnostics;
  using System.Diagnostics.Contracts;
  using Microsoft.Basetypes;

  using ISet = Microsoft.Boogie.GSet<object>;
  using HashSet = Microsoft.Boogie.GSet<object>;

  /// <summary>
  /// Represents an invariant over linear variable constraints, represented by a polyhedron.
  /// </summary>
  public class PolyhedraLattice : Lattice {
    private static readonly Logger/*!*/ log = new Logger("Polyhedra");

    private class PolyhedraLatticeElement : Element {

      public LinearConstraintSystem/*!*/ lcs;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(lcs != null);
      }


      /// <summary>
      /// Creates a top or bottom elements, according to parameter "top".
      /// </summary>
      public PolyhedraLatticeElement(bool top) {
        if (top) {
          lcs = new LinearConstraintSystem(new ArrayList /*LinearConstraint*/ ());
        } else {
          lcs = new LinearConstraintSystem();
        }
      }

      [Pure]
      public override string/*!*/ ToString() {
        Contract.Ensures(Contract.Result<string>() != null);
        return lcs.ToString();
      }

      public override void Dump(string/*!*/ msg) {
        //Contract.Requires(msg != null);
        System.Console.WriteLine("PolyhedraLatticeElement.Dump({0}):", msg);
        lcs.Dump();
      }

      [Pure]
      public override ICollection<IVariable/*!*/>/*!*/ FreeVariables() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<ICollection<IVariable>>()));
        return lcs.FreeVariables();
      }

      public PolyhedraLatticeElement(LinearConstraintSystem/*!*/ lcs) {
        Contract.Requires(lcs != null);
        this.lcs = lcs;
      }

      public override Element/*!*/ Clone() {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new PolyhedraLatticeElement(cce.NonNull(lcs.Clone()));
      }

    } // class

    readonly ILinearExprFactory/*!*/ factory;
    readonly IPropExprFactory/*!*/ propFactory;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(log != null);
      Contract.Invariant(factory != null);
      Contract.Invariant(propFactory != null);
    }


    public PolyhedraLattice(ILinearExprFactory/*!*/ linearFactory, IPropExprFactory/*!*/ propFactory)
      : base(linearFactory) {
      Contract.Requires(propFactory != null);
      Contract.Requires(linearFactory != null);
      log.Enabled = Lattice.LogSwitch;
      this.factory = linearFactory;
      this.propFactory = propFactory;
      // base(linearFactory);
    }

    public override Element/*!*/ Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new PolyhedraLatticeElement(true);
      }
    }

    public override Element/*!*/ Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);

        return new PolyhedraLatticeElement(false);
      }
    }

    public override bool IsBottom(Element/*!*/ element) {
      //Contract.Requires(element != null);
      PolyhedraLatticeElement e = (PolyhedraLatticeElement)element;
      return e.lcs.IsBottom();
    }

    public override bool IsTop(Element/*!*/ element) {
      //Contract.Requires(element != null);
      PolyhedraLatticeElement e = (PolyhedraLatticeElement)element;
      return e.lcs.IsTop();
    }


    /// <summary>
    /// Returns true iff a is a subset of this.
    /// </summary>
    /// <param name="a"></param>
    /// <returns></returns>
    protected override bool AtMost(Element/*!*/ first, Element/*!*/ second)  // this <= that
    {
      //Contract.Requires(first != null);
      //Contract.Requires(second != null);
      PolyhedraLatticeElement a = (PolyhedraLatticeElement)first;
      PolyhedraLatticeElement b = (PolyhedraLatticeElement)second;
      return b.lcs.IsSubset(a.lcs);
    }


    public override string/*!*/ ToString(Element/*!*/ e) {
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<string>() != null);
      return ((PolyhedraLatticeElement)e).lcs.ToString();
    }

    public override IExpr/*!*/ ToPredicate(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      PolyhedraLatticeElement e = (PolyhedraLatticeElement)element;
      return e.lcs.ConvertToExpression(factory);
    }



    public override Lattice.Element/*!*/ NontrivialJoin(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Lattice.Element>() != null);
      log.DbgMsg("Joining ...");
      log.DbgMsgIndent();
      PolyhedraLatticeElement aa = (PolyhedraLatticeElement)first;
      PolyhedraLatticeElement bb = (PolyhedraLatticeElement)second;
      PolyhedraLatticeElement result = new PolyhedraLatticeElement(aa.lcs.Join(bb.lcs));
      log.DbgMsg(string.Format("{0} |_| {1} --> {2}", this.ToString(first), this.ToString(second), this.ToString(result)));
      log.DbgMsgUnindent();
      return result;
    }


    public override Lattice.Element/*!*/ NontrivialMeet(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Lattice.Element>() != null);
      PolyhedraLatticeElement aa = (PolyhedraLatticeElement)first;
      PolyhedraLatticeElement bb = (PolyhedraLatticeElement)second;
      return new PolyhedraLatticeElement(aa.lcs.Meet(bb.lcs));
    }


    public override Lattice.Element/*!*/ Widen(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Lattice.Element>() != null);
      log.DbgMsg("Widening ...");
      log.DbgMsgIndent();
      PolyhedraLatticeElement aa = (PolyhedraLatticeElement)first;
      PolyhedraLatticeElement bb = (PolyhedraLatticeElement)second;

      LinearConstraintSystem lcs = aa.lcs.Widen(bb.lcs);
      PolyhedraLatticeElement result = new PolyhedraLatticeElement(lcs);
      log.DbgMsg(string.Format("{0} |_| {1} --> {2}", this.ToString(first), this.ToString(second), this.ToString(result)));
      log.DbgMsgUnindent();
      return result;
    }


    public override Element/*!*/ Eliminate(Element/*!*/ e, IVariable/*!*/ variable) {
      //Contract.Requires(variable != null);
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      log.DbgMsg(string.Format("Eliminating {0} ...", variable));

      PolyhedraLatticeElement ple = (PolyhedraLatticeElement)e;
      if (ple.lcs.IsBottom()) {
        return ple;
      }
      return new PolyhedraLatticeElement(ple.lcs.Project(variable));
    }


    public override Element/*!*/ Rename(Element/*!*/ e, IVariable/*!*/ oldName, IVariable/*!*/ newName) {
      //Contract.Requires(newName != null);
      //Contract.Requires(oldName != null);
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      log.DbgMsg(string.Format("Renaming {0} to {1} in {2} ...", oldName, newName, this.ToString(e)));

      PolyhedraLatticeElement ple = (PolyhedraLatticeElement)e;
      if (ple.lcs.IsBottom()) {
        return ple;
      }
      return new PolyhedraLatticeElement(ple.lcs.Rename(oldName, newName));
    }

    public override bool Understands(IFunctionSymbol/*!*/ f, IList/*<IExpr!>*//*!*/ args) {
      //Contract.Requires(args != null);
      //Contract.Requires(f != null);
      return f is IntSymbol ||
          f.Equals(Int.Add) ||
          f.Equals(Int.Sub) ||
          f.Equals(Int.Negate) ||
          f.Equals(Int.Mul) ||
          f.Equals(Int.Eq) ||
          f.Equals(Int.Neq) ||
          f.Equals(Prop.Not) ||
          f.Equals(Int.AtMost) ||
          f.Equals(Int.Less) ||
          f.Equals(Int.Greater) ||
          f.Equals(Int.AtLeast);
    }

    public override Answer CheckVariableDisequality(Element/*!*/ e, IVariable/*!*/ var1, IVariable/*!*/ var2) {
      //Contract.Requires(var2 != null);
      //Contract.Requires(var1 != null);
      //Contract.Requires(e != null);
      PolyhedraLatticeElement/*!*/ ple = (PolyhedraLatticeElement)cce.NonNull(e);
      Contract.Assume(ple.lcs.Constraints != null);
      ArrayList /*LinearConstraint!*//*!*/ clist = (ArrayList /*LinearConstraint!*/)cce.NonNull(ple.lcs.Constraints.Clone());
      LinearConstraint/*!*/ lc = new LinearConstraint(LinearConstraint.ConstraintRelation.EQ);
      Contract.Assert(lc != null);
      lc.SetCoefficient(var1, Rational.ONE);
      lc.SetCoefficient(var2, Rational.MINUS_ONE);
      clist.Add(lc);
      LinearConstraintSystem newLcs = new LinearConstraintSystem(clist);
      if (newLcs.IsBottom()) {
        return Answer.Yes;
      } else {
        return Answer.Maybe;
      }
    }

    public override Answer CheckPredicate(Element/*!*/ e, IExpr/*!*/ pred) {
      //Contract.Requires(pred != null);
      //Contract.Requires(e != null);
      PolyhedraLatticeElement/*!*/ ple = (PolyhedraLatticeElement)Constrain(e, pred);
      Contract.Assert(ple != null);
      if (ple.lcs.IsBottom()) {
        return Answer.No;
      }

      // Note, "pred" may contain expressions that are not understood by the propFactory (in
      // particular, this may happen because--currently, and perhaps is a design we'll want
      // to change in the future--propFactory deals with BoogiePL expressions whereas "pred"
      // may also refer to Equivalences.UninterpFun expressions).  Thus, we cannot just
      // call propFactory.Not(pred) to get the negation of "pred".
      pred = new PolyhedraLatticeNegation(pred);
      ple = (PolyhedraLatticeElement)Constrain(e, pred);
      if (ple.lcs.IsBottom()) {
        return Answer.Yes;
      } else {
        return Answer.Maybe;
      }
    }

    class PolyhedraLatticeNegation : IFunApp {
      IExpr/*!*/ arg;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(arg != null);
      }


      public PolyhedraLatticeNegation(IExpr/*!*/ arg) {
        Contract.Requires(arg != null);
        this.arg = arg;
        // base();
      }

      [Pure]
      public object DoVisit(ExprVisitor/*!*/ visitor) {
        //Contract.Requires(visitor != null);
        return visitor.VisitFunApp(this);
      }

      public IFunctionSymbol/*!*/ FunctionSymbol {
        get {
          Contract.Ensures(Contract.Result<IFunctionSymbol>() != null);
          return Prop.Not;
        }
      }

      public IList/*<IExpr!>*//*!*/ Arguments {
        get {
          Contract.Ensures(Contract.Result<IList>() != null);

          IExpr[] args = new IExpr[] { arg };
          return ArrayList.ReadOnly(args);
        }
      }

      public IFunApp/*!*/ CloneWithArguments(IList/*<IExpr!>*//*!*/ args) {
        //Contract.Requires(args != null);
        Contract.Ensures(Contract.Result<IFunApp>() != null);
        Contract.Assert(args.Count == 1);
        return new PolyhedraLatticeNegation((IExpr/*!*/)cce.NonNull(args[0]));
      }
    }

    public override IExpr/*?*/ EquivalentExpr(Element/*!*/ e, IQueryable/*!*/ q, IExpr/*!*/ expr, IVariable/*!*/ var, ISet/*<IVariable!>*//*!*/ prohibitedVars) {
      //Contract.Requires(prohibitedVars != null);
      //Contract.Requires(var != null);
      //Contract.Requires(expr != null);
      //Contract.Requires(q != null);
      //Contract.Requires(e != null);
      // BUGBUG: TODO: this method can be implemented in a more precise way
      return null;
    }


    public override Element/*!*/ Constrain(Element/*!*/ e, IExpr/*!*/ expr) {
      //Contract.Requires(expr != null);
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      log.DbgMsg(string.Format("Constraining with {0} into {1} ...", expr, this.ToString(e)));

      PolyhedraLatticeElement ple = (PolyhedraLatticeElement)e;
      if (ple.lcs.IsBottom()) {
        return ple;
      }
      LinearCondition le = LinearExpressionBuilder.AsCondition(expr);
      if (le != null) {
        // update the polyhedron according to the linear expression
        Contract.Assume(ple.lcs.Constraints != null);
        ArrayList /*LinearConstraint*/ clist = (ArrayList/*!*/ /*LinearConstraint*/)cce.NonNull(ple.lcs.Constraints.Clone());
        le.AddToConstraintSystem(clist);
        LinearConstraintSystem newLcs = new LinearConstraintSystem(clist);

        return new PolyhedraLatticeElement(newLcs);
      }
      return ple;
    }

  } // class


  /// <summary>
  /// A LinearCondition follows this grammar:
  ///     LinearCondition ::=  unsatisfiable
  ///                       |  LinearConstraint
  ///                       |  ! LinearConstraint
  /// Note that negations are distributed to the leaves.
  /// </summary>
  /// 
  [ContractClass(typeof(LinearConditionContracts))]
  abstract class LinearCondition {
    /// <summary>
    /// Adds constraints to the list "clist".  If "this"
    /// entails some disjunctive constraints, they may not be added.
    /// </summary>
    /// <param name="clist"></param>
    public abstract void AddToConstraintSystem(ArrayList/*!*/ /*LinearConstraint*/ clist);
  }
  [ContractClassFor(typeof(LinearCondition))]
  abstract class LinearConditionContracts : LinearCondition {
    public override void AddToConstraintSystem(ArrayList clist) {
      Contract.Requires(clist != null);
      throw new NotImplementedException();
    }
  }

  class LCBottom : LinearCondition {
    public override void AddToConstraintSystem(ArrayList/*!*/ /*LinearConstraint*/ clist) {
      //Contract.Requires(clist != null);
      // make an unsatisfiable constraint
      LinearConstraint lc = new LinearConstraint(LinearConstraint.ConstraintRelation.EQ);
      lc.rhs = Rational.FromInt(1);
      clist.Add(lc);
    }
  }

  class LinearConditionLiteral : LinearCondition {
    public readonly bool positive;
    public readonly LinearConstraint/*!*/ constraint;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(constraint != null);
    }

    /// <summary>
    /// Precondition:  positive || constraint.Relation == LinearConstraint.ConstraintRelation.EQ
    /// </summary>
    /// <param name="positive"></param>
    /// <param name="constraint"></param>
    public LinearConditionLiteral(bool positive, LinearConstraint/*!*/ constraint) {
      Contract.Requires(constraint != null);
      Contract.Requires(positive || constraint.Relation == LinearConstraint.ConstraintRelation.EQ);
      this.positive = positive;
      this.constraint = constraint;
    }
    public override void AddToConstraintSystem(ArrayList/*!*/ /*LinearConstraint*/ clist) {
      //Contract.Requires(clist != null);
      if (positive) {
        clist.Add(constraint);
      } else {
        Contract.Assert(constraint.Relation == LinearConstraint.ConstraintRelation.EQ);
        // the constraint is disjunctive, so just ignore it
      }
    }
  }

  class LinearExpressionBuilder {
    /// <summary>
    /// Builds a linear condition from "e", if possible; returns null if not possible.
    /// </summary>
    /// <param name="e"></param>
    /// <returns></returns>
    public static /*maybe null*/ LinearCondition AsCondition(IExpr e) /* throws ArithmeticException */
    {
      return GetCond(e, true);
    }

    static /*maybe null*/ LinearCondition GetCond(IExpr e, bool positive) /* throws ArithmeticException */
    {
      IFunApp funapp = e as IFunApp;
      if (funapp == null) {
        return null;
      }
      IFunctionSymbol/*!*/ s = funapp.FunctionSymbol;
      Contract.Assert(s != null);
      if ((positive && s.Equals(Prop.False)) ||
          (!positive && s.Equals(Prop.True))) {
        return new LCBottom();
      } else if (s.Equals(Prop.Not)) {
        Contract.Assert(funapp.Arguments.Count == 1);
        return GetCond((IExpr/*!*/)cce.NonNull(funapp.Arguments[0]), !positive);
      } else if (funapp.Arguments.Count == 2) {
        IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(funapp.Arguments[0]);
        IExpr/*!*/ arg1 = (IExpr/*!*/)cce.NonNull(funapp.Arguments[1]);
        LinearExpr le0 = AsExpr(arg0);
        if (le0 == null) {
          return null;
        }
        LinearExpr le1 = AsExpr(arg1);
        if (le1 == null) {
          return null;
        }

        LinearConstraint constraint = null;
        bool sense = true;
        if ((positive && s.Equals(Int.Less)) || (!positive && s.Equals(Int.AtLeast))) {
          constraint = MakeConstraint(le0, le1, LinearConstraint.ConstraintRelation.LE, BigNum.ONE);
        } else if ((positive && s.Equals(Int.AtMost)) || (!positive && s.Equals(Int.Greater))) {
          constraint = MakeConstraint(le0, le1, LinearConstraint.ConstraintRelation.LE, BigNum.ZERO);
        } else if ((positive && s.Equals(Int.AtLeast)) || (!positive && s.Equals(Int.Less))) {
          constraint = MakeConstraint(le1, le0, LinearConstraint.ConstraintRelation.LE, BigNum.ZERO);
        } else if ((positive && s.Equals(Int.Greater)) || (!positive && s.Equals(Int.AtMost))) {
          constraint = MakeConstraint(le1, le0, LinearConstraint.ConstraintRelation.LE, BigNum.ONE);
        } else if (s.Equals(Int.Eq)) {
          constraint = MakeConstraint(le0, le1, LinearConstraint.ConstraintRelation.EQ, BigNum.ZERO);
          sense = positive;
        } else if (s.Equals(Int.Neq)) {
          constraint = MakeConstraint(le0, le1, LinearConstraint.ConstraintRelation.EQ, BigNum.ZERO);
          sense = !positive;
        }
        if (constraint != null) {
          if (constraint.coefficients.Count != 0) {
            return new LinearConditionLiteral(sense, constraint);
          } else if (constraint.IsConstantSatisfiable()) {
            return null;
          } else {
            return new LCBottom();
          }
        }
      }
      return null;
    }

    public static LinearConstraint MakeConstraint(LinearExpr/*!*/ le0, LinearExpr/*!*/ le1,
        LinearConstraint.ConstraintRelation rel, BigNum constantOffset) /* throws ArithmeticException */
    {
      Contract.Requires(le0 != null);
      Contract.Requires(le1 != null);
      le1.Negate();
      le0.Add(le1);
      le0.AddConstant(constantOffset);
      return le0.ToConstraint(rel);
    }

    /// <summary>
    /// Builds a linear expression from "e", if possible; returns null if not possible.
    /// </summary>
    /// <param name="e"></param>
    /// <returns></returns>
    public static /*maybe null*/ LinearExpr AsExpr(IExpr/*!*/ e) /* throws ArithmeticException */
    {
      Contract.Requires(e != null);
      if (e is IVariable) {
        // Note, without a type for the variable, we don't know if the identifier is intended to hold an integer value.
        // However, it seems that no harm can be caused by here treating the identifier as if it held an
        // integer value, because other parts of this method will reject the expression as a linear expression
        // if non-numeric operations other than equality are applied to the identifier.
        return new LinearExpr((IVariable)e);
      } else if (e is IFunApp) {
        IFunApp/*!*/ funapp = (IFunApp)e;
        Contract.Assert(funapp != null);
        IFunctionSymbol/*!*/ s = funapp.FunctionSymbol;
        Contract.Assert(s != null);

        if (s is IntSymbol) {
          return new LinearExpr(((IntSymbol)s).Value);
        } else if (s.Equals(Int.Negate)) {
          Contract.Assert(funapp.Arguments.Count == 1);
          LinearExpr le = AsExpr((IExpr/*!*/)cce.NonNull(funapp.Arguments[0]));
          if (le != null) {
            le.Negate();
            return le;
          }
        } else if (s.Equals(Int.Add) || s.Equals(Int.Sub) || s.Equals(Int.Mul)) {
          Contract.Assert(funapp.Arguments.Count == 2);
          IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(funapp.Arguments[0]);
          IExpr/*!*/ arg1 = (IExpr/*!*/)cce.NonNull(funapp.Arguments[1]);
          LinearExpr le0 = AsExpr(arg0);
          if (le0 == null) {
            return null;
          }
          LinearExpr le1 = AsExpr(arg1);
          if (le1 == null) {
            return null;
          }

          if (s.Equals(Int.Add)) {
            le0.Add(le1);
            return le0;
          } else if (s.Equals(Int.Sub)) {
            le1.Negate();
            le0.Add(le1);
            return le0;
          } else if (s.Equals(Int.Mul)) {
            BigNum x;
            if (le0.AsConstant(out x)) {
              le1.Multiply(x);
              return le1;
            } else if (le1.AsConstant(out x)) {
              le0.Multiply(x);
              return le0;
            }
          }
        }
      }
      return null;
    }
  }

  class LinearExpr {
    BigNum constant;
    Term terms;

    class Term {
      public BigNum coeff;  // non-0, if the node is used
      public IVariable/*!*/ var;
      public Term next;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(var != null);
      }

      public Term(BigNum coeff, IVariable/*!*/ var) {
        Contract.Requires(var != null);
        this.coeff = coeff;
        this.var = var;
        // base();
      }
    }

    public LinearExpr(BigNum x) {
      constant = x;
    }

    public LinearExpr(IVariable/*!*/ var) {
      Contract.Requires(var != null);
      constant = BigNum.ZERO;
      terms = new Term(BigNum.ONE, var);
    }

    public ISet /*IVariable!*/ GetDefinedDimensions() {
      HashSet /*IVariable!*//*!*/ dims = new HashSet /*IVariable!*/ ();
      for (Term current = terms; current != null; current = current.next) {
        dims.Add(current.var);
      }
      return dims;
    }

    public BigNum TermCoefficient(/*MayBeNull*/ IVariable/*!*/ var) {
      Contract.Requires(var != null);
      BigNum z = BigNum.ZERO;
      if (var == null) {
        z = this.constant;
      } else if (terms != null) {
        Term current = terms;
        while (current != null) {
          if (current.var == var) {
            break;
          }
          current = current.next;
        }
        if (current != null) {
          z = current.coeff;
        }
      }
      return z;
    }

    public bool AsConstant(out BigNum x) {
      if (terms == null) {
        x = constant;
        return true;
      } else {
        x = BigNum.FromInt(-70022);  // to please complier
        return false;
      }
    }

    public void Negate() /* throws ArithmeticException */
    {
      checked {
        constant = -constant;
      }

      for (Term t = terms; t != null; t = t.next) {
        checked {
          t.coeff = -t.coeff;
        }
      }
    }

    /// <summary>
    /// Adds "x" to "this".
    /// </summary>
    /// <param name="x"></param>
    public void AddConstant(BigNum x) /* throws ArithmeticException */
    {
      checked {
        constant += x;
      }
    }

    /// <summary>
    /// Adds "le" to "this".  Afterwards, "le" should not be used, because it will have been destroyed.
    /// </summary>
    /// <param name="le"></param>
    public void Add(LinearExpr/*!*/ le) /* throws ArithmeticException */
        {
      Contract.Requires(le != null);
      Contract.Requires(le != this);
      checked {
        constant += le.constant;
      }
      le.constant = BigNum.FromInt(-70029);  // "le" should no longer be used; assign it a strange value so that misuse is perhaps more easily detected

      // optimization:
      if (le.terms == null) {
        return;
      } else if (terms == null) {
        terms = le.terms;
        le.terms = null;
        return;
      }

      // merge the two term lists
      // Use a nested loop, which is quadratic in time complexity, but we hope the lists will be small
      Term newTerms = null;
      while (le.terms != null) {
        // take off next term from "le"
        Term t = le.terms;
        le.terms = t.next;
        t.next = null;

        for (Term u = terms; u != null; u = u.next) {
          if (u.var == t.var) {
            checked {
              u.coeff += t.coeff;
            }
            goto NextOuter;
          }
        }
        t.next = newTerms;
        newTerms = t;

      NextOuter:
        ;
      }

      // finally, include all non-0 terms
      while (terms != null) {
        // take off next term from "this"
        Term t = terms;
        terms = t.next;

        if (!t.coeff.IsZero) {
          t.next = newTerms;
          newTerms = t;
        }
      }
      terms = newTerms;
    }

    public void Multiply(BigNum x) /* throws ArithmeticException */
    {
      if (x.IsZero) {
        constant = BigNum.ZERO;
        terms = null;
      } else {
        for (Term t = terms; t != null; t = t.next) {
          checked {
            t.coeff *= x;
          }
        }
        checked {
          constant *= x;
        }
      }
    }

    public bool IsInvertible(IVariable/*!*/ var) {
      Contract.Requires(var != null);
      for (Term t = terms; t != null; t = t.next) {
        if (t.var == var) {
          System.Diagnostics.Debug.Assert(!t.coeff.IsZero);
          return true;
        }
      }
      return false;
    }

    public LinearConstraint ToConstraint(LinearConstraint.ConstraintRelation rel) /* throws ArithmeticException */
    {
      LinearConstraint constraint = new LinearConstraint(rel);
      for (Term t = terms; t != null; t = t.next) {
        constraint.SetCoefficient(t.var, t.coeff.ToRational);
      }
      BigNum rhs = -constant;
      constraint.rhs = rhs.ToRational;
      return constraint;
    }
  }
}
