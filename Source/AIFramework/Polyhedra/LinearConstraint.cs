//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Diagnostics.Contracts;
namespace Microsoft.AbstractInterpretationFramework {
  using System;
  //using System.Compiler;
  using System.Collections;
  using Microsoft.Basetypes;
  using Set = Microsoft.Boogie.GSet<object>;
  using IMutableSet = Microsoft.Boogie.GSet<object>; 
  using HashSet = Microsoft.Boogie.GSet<object>;
  using ISet = Microsoft.Boogie.GSet<object>;


  /// <summary>
  /// Represents a single linear constraint, coefficients are stored as Rationals.
  /// </summary>
  public class LinearConstraint {

    public enum ConstraintRelation {
      EQ,    // equal
      LE,    // less-than or equal
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(coefficients != null);
    }

    public readonly ConstraintRelation Relation;
    internal Hashtable /*IVariable->Rational*//*!*/ coefficients = new Hashtable /*IVariable->Rational*/ ();
    internal Rational rhs;

    public LinearConstraint(ConstraintRelation rel) {
      Relation = rel;
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      string s = null;
      foreach (DictionaryEntry /*IVariable->Rational*/ entry in coefficients) {
        if (s == null) {
          s = "";
        } else {
          s += " + ";
        }
        s += String.Format("{0}*{1}", entry.Value, entry.Key);
      }
      System.Diagnostics.Debug.Assert(s != null, "malformed LinearConstraint: no variables");
      s += String.Format(" {0} {1}", Relation == ConstraintRelation.EQ ? "==" : "<=", rhs);
      return s;
    }


#if DONT_KNOW_HOW_TO_TAKE_THE_TYPE_OF_AN_IVARIABLE_YET
        public bool IsOverIntegers 
        {
            get
            {
                foreach (DictionaryEntry /*IVariable->Rational*/ entry in coefficients) 
                {
                    IVariable var = (IVariable)entry.Key;
                    if ( ! var.TypedIdent.Type.IsInt) { return false; }
                }
                return true;
            }
        }
#endif


    /// <summary>
    /// Note: This method requires that all dimensions are of type Variable, something that's
    /// not required elsewhere in this class.
    /// </summary>
    /// <returns></returns>
    public IExpr/*!*/ ConvertToExpression(ILinearExprFactory/*!*/ factory) {
      Contract.Requires(factory != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      IExpr leftSum = null;
      IExpr rightSum = null;
      foreach (DictionaryEntry /*object->Rational*/ entry in coefficients) {
        IVariable var = (IVariable)entry.Key;
        Rational coeff = (Rational)(cce.NonNull(entry.Value));
        if (coeff.IsPositive) {
          leftSum = AddTerm(factory, leftSum, coeff, var);
        } else if (coeff.IsNegative) {
          rightSum = AddTerm(factory, rightSum, -coeff, var);
        } else {
          // ignore the term is coeff==0
        }
      }

      if (leftSum == null && rightSum == null) {
        // there are no variables in this constraint
        if (Relation == ConstraintRelation.EQ ? rhs.IsZero : rhs.IsNonNegative) {
          return factory.True;
        } else {
          return factory.False;
        }
      }

      if (leftSum == null || (rightSum != null && rhs.IsNegative)) {
        // show the constant on the left side
        leftSum = AddTerm(factory, leftSum, -rhs, null);
      } else if (rightSum == null || rhs.IsPositive) {
        // show the constant on the right side
        rightSum = AddTerm(factory, rightSum, rhs, null);
      }

      Contract.Assert(leftSum != null);
      Contract.Assert(rightSum != null);
      return Relation == ConstraintRelation.EQ ? factory.Eq(leftSum, rightSum) : factory.AtMost(leftSum, rightSum);
    }

    /// <summary>
    /// Returns an expression that denotes sum + r*x.
    /// If sum==null, drops the "sum +".
    /// If x==null, drops the "*x".
    /// if x!=null and r==1, drops the "r*".
    /// </summary>
    /// <param name="factory"></param>
    /// <param name="sum"></param>
    /// <param name="r"></param>
    /// <param name="x"></param>
    static IExpr/*!*/ AddTerm(ILinearExprFactory/*!*/ factory, /*MayBeNull*/ IExpr sum, Rational r, /*MayBeNull*/ IVariable x) {
      Contract.Requires(factory != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      IExpr/*!*/ product = factory.Term(r, x);
      Contract.Assert(product != null);
      if (sum == null) {
        return product;
      } else {
        return factory.Add(sum, product);
      }
    }
    public System.Collections.Generic.IEnumerable<IVariable> GetDefinedDimensionsGeneric() {
      Contract.Ensures(Contract.Result<System.Collections.Generic.IEnumerable<IVariable>>() != null);
      foreach (IVariable/*!*/ dim in coefficients.Keys) {
        Contract.Assert(dim != null);
        yield return dim;
      }
    }
    public ISet /*IVariable!*//*!*/ GetDefinedDimensions() {
      Contract.Ensures(Contract.Result<ISet>() != null);
      HashSet /*IVariable!*/ dims = new HashSet /*IVariable!*/ (coefficients.Count);
      int j = 0;
      foreach (IVariable/*!*/ dim in coefficients.Keys) {
        Contract.Assert(dim != null);
        dims.Add(dim);
        j++;
      }
      System.Diagnostics.Debug.Assert(j == coefficients.Count);
      return dims;
    }

    /// <summary>
    /// Returns true iff all of the coefficients in the constraint are 0.  In that
    /// case, the constraint has the form 0 &lt;= C for some constant C; hence, the
    /// constraint is either unsatisfiable or trivially satisfiable.
    /// </summary>
    /// <returns></returns>
    public bool IsConstant() {
      foreach (Rational coeff in coefficients.Values) {
        if (coeff.IsNonZero) {
          return false;
        }
      }
      return true;
    }

    /// <summary>
    /// For an equality constraint, returns 0 == rhs.
    /// For an inequality constraint, returns 0 &lt;= rhs.
    /// </summary>
    public bool IsConstantSatisfiable() {
      if (Relation == ConstraintRelation.EQ) {
        return rhs.IsZero;
      } else {
        return rhs.IsNonNegative;
      }
    }

    /// <summary>
    /// Returns 0 if "this" and "c" are not equivalent constraints.  If "this" and "c"
    /// are equivalent constraints, the non-0 return value "m" satisfies "this == m*c".
    /// </summary>
    /// <param name="c"></param>
    /// <returns></returns>
    public Rational IsEquivalent(LinearConstraint/*!*/ c) {
      Contract.Requires(c != null);
      // "m" is the scale factor.  If it is 0, it hasn't been used yet.  If it
      // is non-0, it will remain that value throughout, and it then says that
      // for every dimension "d", "this[d] == m * c[d]".
      Rational m = Rational.ZERO;

      ArrayList /*IVariable*/ dd = new ArrayList /*IVariable*/ ();
      foreach (IVariable/*!*/ d in this.GetDefinedDimensions()) {
        Contract.Assert(d != null);
        if (!dd.Contains(d)) {
          dd.Add(d);
        }
      }
      foreach (IVariable/*!*/ d in c.GetDefinedDimensions()) {
        Contract.Assert(d != null);
        if (!dd.Contains(d)) {
          dd.Add(d);
        }
      }

      foreach (IVariable/*!*/ d in dd) {
        Contract.Assert(d != null);
        Rational a = this[d];
        Rational b = c[d];

        if (a.IsZero || b.IsZero) {
          if (a.IsNonZero || b.IsNonZero) {
            return Rational.ZERO;  // not equivalent
          }
        } else if (m.IsZero) {
          m = a / b;
        } else if (a != m * b) {
          return Rational.ZERO;  // not equivalent
        }
      }

      // we expect there to have been some non-zero coefficient, so "m" should have been used by now
      System.Diagnostics.Debug.Assert(m.IsNonZero);

      // finally, check the rhs
      if (this.rhs == m * c.rhs) {
        return m;  // equivalent
      } else {
        return Rational.ZERO;  // not equivalent
      }
    }

    /// <summary>
    /// Splits an equality constraint into two inequality constraints, the conjunction of
    /// which equals the equality constraint.  Assumes "this" is a equality constraint.
    /// </summary>
    /// <param name="a"></param>
    /// <param name="b"></param>
    public void GenerateInequalityConstraints(out LinearConstraint a, out LinearConstraint b) {
      System.Diagnostics.Debug.Assert(this.Relation == ConstraintRelation.EQ);

      a = new LinearConstraint(ConstraintRelation.LE);
      a.coefficients = (Hashtable)this.coefficients.Clone();
      a.rhs = this.rhs;

      b = new LinearConstraint(ConstraintRelation.LE);
      b.coefficients = new Hashtable /*IVariable->Rational*/ ();
      foreach (DictionaryEntry entry in this.coefficients) {
        b.coefficients[entry.Key] = -(Rational)(cce.NonNull(entry.Value));
      }
      b.rhs = -this.rhs;
    }

    public void SetCoefficient(IVariable/*!*/ dimension, Rational coefficient) {
      Contract.Requires(dimension != null);
      coefficients[dimension] = coefficient;
    }

    /// <summary>
    /// Removes dimension "dim" from the constraint.  Only dimensions with coefficient 0 can
    /// be removed.
    /// </summary>
    /// <param name="dim"></param>
    public void RemoveDimension(IVariable/*!*/ dim) {
      Contract.Requires(dim != null);
      object val = coefficients[dim];
      if (val != null) {
#if FIXED_SERIALIZER            
                Contract.Assert(((Rational)val).IsZero);
#endif
        coefficients.Remove(dim);
      }
    }

    /// <summary>
    /// The getter returns 0 if the dimension is not present.
    /// </summary>
    public Rational this[IVariable/*!*/ dimension] {
      get {
        Contract.Requires(dimension != null);


        object z = coefficients[dimension];
        if (z == null) {
          return Rational.ZERO;
        } else {
          return (Rational)z;
        }
      }
      set {
        SetCoefficient(dimension, value);
      }
    }

    public LinearConstraint Rename(IVariable/*!*/ oldName, IVariable/*!*/ newName) {
      Contract.Requires(newName != null);
      Contract.Requires(oldName != null);
      object /*Rational*/ z = coefficients[oldName];
      if (z == null) {
        return this;
      } else {
        System.Diagnostics.Debug.Assert(z is Rational);
        Hashtable /*IVariable->Rational*/ newCoeffs = (Hashtable/*!*/ /*IVariable->Rational*/)cce.NonNull(coefficients.Clone());
        newCoeffs.Remove(oldName);
        newCoeffs.Add(newName, z);

        LinearConstraint lc = new LinearConstraint(this.Relation);
        lc.coefficients = newCoeffs;
        lc.rhs = this.rhs;
        return lc;
      }
    }

    public LinearConstraint Clone() {
      LinearConstraint z = new LinearConstraint(Relation);
      z.coefficients = (Hashtable /*IVariable->Rational*/)this.coefficients.Clone();
      z.rhs = this.rhs;
      return z;
    }

    /// <summary>
    /// Returns a constraint like "this", but with the given relation "r".
    /// </summary>
    /// <returns></returns>
    public LinearConstraint/*!*/ ChangeRelation(ConstraintRelation rel) {
      Contract.Ensures(Contract.Result<LinearConstraint>() != null);
      if (Relation == rel) {
        return this;
      } else {
        LinearConstraint z = new LinearConstraint(rel);
        z.coefficients = (Hashtable)this.coefficients.Clone();
        z.rhs = this.rhs;
        return z;
      }
    }

    /// <summary>
    /// Returns a constraint like "this", but, conceptually, with the inequality relation >=.
    /// </summary>
    /// <returns></returns>
    public LinearConstraint/*!*/ ChangeRelationToAtLeast() {
      Contract.Ensures(Contract.Result<LinearConstraint>() != null);
      LinearConstraint z = new LinearConstraint(ConstraintRelation.LE);
      foreach (DictionaryEntry /*IVariable->Rational*/ entry in this.coefficients) {
        z.coefficients.Add(entry.Key, -(Rational)(cce.NonNull(entry.Value)));
      }
      z.rhs = -this.rhs;
      return z;
    }

    /// <summary>
    /// Returns the left-hand side of the constraint evaluated at the point "v".
    /// Any coordinate not present in "v" is treated as if it were 0.
    /// Stated differently, this routine treats the left-hand side of the constraint
    /// as a row vector and "v" as a column vector, and then returns the dot-product
    /// of the two.
    /// </summary>
    /// <param name="v"></param>
    /// <returns></returns>
    public Rational EvaluateLhs(FrameElement/*!*/ v) {
      Contract.Requires(v != null);
      Rational q = Rational.ZERO;
      foreach (DictionaryEntry /*IVariable,Rational*/ term in coefficients) {
        IVariable dim = (IVariable/*!*/)cce.NonNull(term.Key);
        Rational a = (Rational)(cce.NonNull(term.Value));
        Rational x = v[dim];
        q += a * x;
      }
      return q;
    }

    /// <summary>
    /// Determines whether or not a given vertex or ray saturates the constraint.
    /// </summary>
    /// <param name="fe"></param>
    /// <param name="vertex">true if "fe" is a vertex; false if "fe" is a ray</param>
    /// <returns></returns>
    public bool IsSaturatedBy(FrameElement/*!*/ fe, bool vertex) {
      Contract.Requires(fe != null);
      Rational lhs = EvaluateLhs(fe);
      Rational rhs = vertex ? this.rhs : Rational.ZERO;
      return lhs == rhs;
    }

    /// <summary>
    /// Changes the current constraint A*X &lt;= B into (A + m*aa)*X &lt;= B + m*bb,
    /// where "cc" is the constraint aa*X &lt;= bb.
    /// </summary>
    /// <param name="m"></param>
    /// <param name="cc"></param>
    /// <returns></returns>
    public void AddMultiple(Rational m, LinearConstraint/*!*/ cc) {
      Contract.Requires(cc != null);
      foreach (DictionaryEntry /*IVariable->Rational*/ entry in cc.coefficients) {
        IVariable dim = (IVariable)entry.Key;
        Rational d = m * (Rational)(cce.NonNull(entry.Value));
        if (d.IsNonZero) {
          object prev = coefficients[dim];
          if (prev == null) {
            coefficients[dim] = d;
          } else {
            coefficients[dim] = (Rational)prev + d;
          }
        }
      }
      rhs += m * cc.rhs;
    }

    /// <summary>
    /// Try to reduce the magnitude of the coefficients used.
    /// Has a side effect on the coefficients, but leaves the meaning of the linear constraint
    /// unchanged.
    /// </summary>
    public void Normalize() {
      // compute the gcd of the numerators and the gcd of the denominators
      Rational gcd = rhs;
      foreach (Rational r in coefficients.Values) {
        gcd = Rational.Gcd(gcd, r);
      }
      // Change all coefficients, to divide their numerators with gcdNum and to
      // divide their denominators with gcdDen.
      Hashtable /*IVariable->Rational*/ newCoefficients = new Hashtable /*IVariable->Rational*/ (coefficients.Count);
      foreach (DictionaryEntry /*IVarianble->Rational*/ e in coefficients) {
        Rational r = (Rational)(cce.NonNull(e.Value));
        if (r.IsNonZero) {
          newCoefficients.Add(e.Key, Rational.FromBignums(r.Numerator / gcd.Numerator, r.Denominator / gcd.Denominator));
        } else {
          newCoefficients.Add(e.Key, r);
        }
      }

      coefficients = newCoefficients;
      rhs = rhs.IsNonZero ? Rational.FromBignums(rhs.Numerator / gcd.Numerator, rhs.Denominator / gcd.Denominator) : rhs;
    }
  }

  /// <summary>
  /// Represents a frame element (vector of dimension/value tuples).  Used only
  /// internally in class LinearConstraintSystem and its communication with class
  /// LinearConstraint.
  /// </summary>
  public class FrameElement {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(terms != null);
    }

    Hashtable /*IVariable->Rational*//*!*/ terms = new Hashtable /*IVariable->Rational*/ ();

    /// <summary>
    /// Constructs an empty FrameElement.  To add dimensions, call AddCoordinate after construction.
    /// </summary>
    public FrameElement() {
    }

    /// <summary>
    /// This method is to be thought of as being part of the FrameElement object's construction process.
    /// Assumes "dimension" is not already in FrameElement.
    /// </summary>
    /// <param name="dimension"></param>
    /// <param name="value"></param>
    public void AddCoordinate(IVariable/*!*/ dimension, Rational value) {
      Contract.Requires(dimension != null);
      terms.Add(dimension, value);
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      string s = null;
      foreach (DictionaryEntry item in terms) {
        if (s == null) {
          s = "(";
        } else {
          s += ", ";
        }
        s += String.Format("<{0},{1}>", item.Key, (Rational)(cce.NonNull(item.Value)));
      }
      if (s == null) {
        s = "(";
      }
      return s + ")";
    }

    public IMutableSet /*IVariable!*//*!*/ GetDefinedDimensions() {
      Contract.Ensures(Contract.Result<IMutableSet>() != null);
      HashSet /*IVariable!*//*!*/ dims = new HashSet /*IVariable!*/ (terms.Count);
      foreach (IVariable/*!*/ dim in terms.Keys) {
        Contract.Assert(dim != null);
        dims.Add(dim);
      }
      System.Diagnostics.Debug.Assert(dims.Count == terms.Count);
      return dims;
    }

    /// <summary>
    /// The getter returns the value at the given dimension, or 0 if that dimension is not defined.
    /// </summary>
    public Rational this[IVariable/*!*/ dimension] {
      get {
        //Contract.Ensures(Contract.Result<Rational>() != null);
        object z = terms[dimension];
        if (z == null) {
          return Rational.ZERO;
        } else {
          return (Rational)z;
        }
      }
      set {
        terms[dimension] = value;
      }
    }

    public FrameElement Rename(IVariable/*!*/ oldName, IVariable/*!*/ newName) {
      Contract.Requires(newName != null);
      Contract.Requires(oldName != null);
      object /*Rational*/ z = terms[oldName];
      if (z == null) {
        return this;
      } else {
        System.Diagnostics.Debug.Assert(z is Rational);
        Hashtable /*IVariable->Rational*/ newTerms = (Hashtable/*!*/ /*IVariable->Rational*/)cce.NonNull(terms.Clone());
        newTerms.Remove(oldName);
        newTerms.Add(newName, z);

        FrameElement fe = new FrameElement();
        fe.terms = newTerms;
        return fe;
      }
    }

    public FrameElement Clone() {
      FrameElement z = new FrameElement();
      z.terms = (Hashtable /*IVariable->Rational*/)this.terms.Clone();
      return z;
    }
  }
}
