//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework {
  using System.Collections;
  using System.Collections.Generic;
  using System.Diagnostics;
  using System;
  //using Microsoft.SpecSharp.Collections;
  using System.Diagnostics.Contracts;
  using Microsoft.Basetypes;

  using IMutableSet = Microsoft.Boogie.GSet<object>;
  using ISet = Microsoft.Boogie.GSet<object>;
  using HashSet = Microsoft.Boogie.GSet<object>;

  /// <summary>
  /// Represents a system of linear constraints (constraint/frame representations).
  /// </summary>
  public class LinearConstraintSystem {
    // --------------------------------------------------------------------------------------------------------
    // ------------------ Data structure ----------------------------------------------------------------------
    // --------------------------------------------------------------------------------------------------------

    public /*maybe null*/ ArrayList /*LinearConstraint!*/ Constraints;
    /*maybe null*/
    ArrayList /*FrameElement!*/ FrameVertices;
    /*maybe null*/
    ArrayList /*FrameElement!*/ FrameRays;
    IMutableSet/*IVariable!*//*!*/ FrameDimensions;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FrameDimensions != null);
    }

    /*maybe null*/
    ArrayList /*FrameElement!*/ FrameLines;
    // Invariant:  Either all of Constraints, FrameVertices, FrameRays, and FrameLines are
    // null, or all are non-null.
    // Invariant:  Any dimension mentioned in Constraints, FrameVertices, FrameRays, or
    // FrameLines is mentioned in FrameDimensions.
    // The meaning of FrameDimensions is that for any dimension x not in FrameDimensions,
    // there is an implicit line along dimension x (that is, (<x,1>)).

    void CheckInvariant() {
      if (Constraints == null) {
        System.Diagnostics.Debug.Assert(FrameVertices == null);
        System.Diagnostics.Debug.Assert(FrameRays == null);
        System.Diagnostics.Debug.Assert(FrameLines == null);
        System.Diagnostics.Debug.Assert(FrameDimensions.Count == 0);
      } else {
        System.Diagnostics.Debug.Assert(FrameVertices != null);
        System.Diagnostics.Debug.Assert(FrameRays != null);
        System.Diagnostics.Debug.Assert(FrameLines != null);

        foreach (LinearConstraint/*!*/ cc in Constraints) {
          Contract.Assert(cc != null);
#if FIXED_DESERIALIZER        
          Contract.Assert(Contract.ForAll(cc.GetDefinedDimensions() , var=> FrameDimensions.Contains(var)));
#endif
          Contract.Assert(cc.coefficients.Count != 0);
        }
        foreach (ArrayList /*FrameElement*//*!*/ FrameComponent in new ArrayList /*FrameElement*/ [] { FrameVertices, FrameRays, FrameLines }) {
          Contract.Assert(FrameComponent != null);
          foreach (FrameElement fe in FrameComponent) {
            if (fe == null)
              continue;
#if FIXED_DESERIALIZER        
            Contract.Assert(Contract.ForAll(fe.GetDefinedDimensions() , var=> FrameDimensions.Contains(var)));
#endif
          }
        }
      }
    }

    // --------------------------------------------------------------------------------------------------------
    // ------------------ Constructors ------------------------------------------------------------------------
    // --------------------------------------------------------------------------------------------------------

    /// <summary>
    /// Creates a LinearConstraintSystem representing the bottom element, that is, representing
    /// an unsatisfiable system of constraints.
    /// </summary>
    [NotDelayed]
    public LinearConstraintSystem() {
      FrameDimensions = new HashSet /*IVariable!*/ ();
      //:base();
      CheckInvariant();
    }

    /// <summary>
    /// Constructs a linear constraint system with constraints "cs".
    /// The constructor captures all constraints in "cs".
    /// </summary>
    /// <param name="cs"></param>
    [NotDelayed]
    public LinearConstraintSystem(ArrayList /*LinearConstraint!*//*!*/ cs) {
      Contract.Requires(cs != null);
#if BUG_159_HAS_BEEN_FIXED
      Contract.Requires(Contract.ForAll(cs) , cc=> cc.coefficients.Count != 0);
#endif

      ArrayList constraints = new ArrayList /*LinearConstraint!*/ (cs.Count);
      foreach (LinearConstraint/*!*/ cc in cs) {
        Contract.Assert(cc != null);
        constraints.Add(cc);
      }
      Constraints = constraints;
      FrameDimensions = new HashSet /*IVariable!*/ ();  // to please compiler; this value will be overridden in the call to GenerateFrameConstraints below
      //:base();

      GenerateFrameFromConstraints();
      SimplifyConstraints();
      CheckInvariant();
#if DEBUG_PRINT
      Console.WriteLine("LinearConstraintSystem: constructor produced:");
      Dump();
#endif
    }

    /// <summary>
    /// Constructs a linear constraint system corresponding to given vertex.  This constructor
    /// is only used in the test harness--it is not needed for abstract interpretation.
    /// </summary>
    /// <param name="v"></param>
    [NotDelayed]
    LinearConstraintSystem(FrameElement/*!*/ v) {
      Contract.Requires(v != null);
      IMutableSet/*!*/ frameDims = v.GetDefinedDimensions();
      Contract.Assert(frameDims != null);
      ArrayList /*LinearConstraint!*/ constraints = new ArrayList /*LinearConstraint!*/ ();
      foreach (IVariable/*!*/ dim in frameDims) {
        Contract.Assert(dim != null);
        LinearConstraint lc = new LinearConstraint(LinearConstraint.ConstraintRelation.EQ);
        lc.SetCoefficient(dim, Rational.ONE);
        lc.rhs = v[dim];
        constraints.Add(lc);
      }
      FrameDimensions = frameDims;
      Constraints = constraints;

      ArrayList /*FrameElement*/ frameVertices = new ArrayList /*FrameElement*/ ();
      frameVertices.Add(v);
      FrameVertices = frameVertices;

      FrameRays = new ArrayList /*FrameElement*/ ();
      FrameLines = new ArrayList /*FrameElement*/ ();

      //:base();
      CheckInvariant();
    }

    void ChangeIntoBottom() {
      Constraints = null;
      FrameVertices = null;
      FrameRays = null;
      FrameLines = null;
      FrameDimensions.Clear();  // no implicit lines
    }

    // --------------------------------------------------------------------------------------------------------
    // ------------------ Public operations and their support routines ----------------------------------------
    // --------------------------------------------------------------------------------------------------------

    public bool IsBottom() {
      return Constraints == null;
    }

    public bool IsTop() {
      return Constraints != null && Constraints.Count == 0;
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      if (Constraints == null) {
        return "<bottom>";
      } else if (Constraints.Count == 0) {
        return "<top>";
      } else {
        string z = null;
        foreach (LinearConstraint/*!*/ lc in Constraints) {
          Contract.Assert(lc != null);
          string s = lc.ToString();
          if (z == null) {
            z = s;
          } else {
            z += " AND " + s;
          }
        }
        Contract.Assert(z != null);
        return z;
      }
    }


    public ICollection<IVariable/*!*/>/*!*/ FreeVariables() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<ICollection<IVariable>>()));
      Contract.Ensures(Contract.Result<ICollection<IVariable>>().IsReadOnly);
      List<IVariable/*!*/> list = new List<IVariable/*!*/>();
      foreach (IVariable/*!*/ v in FrameDimensions) {
        Contract.Assert(v != null);
        list.Add(v);
      }
      return cce.NonNull(list.AsReadOnly());
    }

    /// <summary>
    /// Note: This method requires that all dimensions are of type Variable, something that's
    /// not required elsewhere in this class.
    /// </summary>
    /// <returns></returns>
    public IExpr/*!*/ ConvertToExpression(ILinearExprFactory/*!*/ factory) {
      Contract.Requires(factory != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      if (this.Constraints == null) {
        return factory.False;
      }
      if (this.Constraints.Count == 0) {
        return factory.True;
      }

      IExpr result = null;
      foreach (LinearConstraint/*!*/ lc in Constraints) {
        Contract.Assert(lc != null);
        IExpr conjunct = lc.ConvertToExpression(factory);
        result = (result == null) ? conjunct : (IExpr)factory.And(conjunct, result);
      }
      Contract.Assert(result != null);
      return result;
    }


    /* IsSubset(): determines if 'lcs' is a subset of 'this'
     * -- See Cousot/Halbwachs 1978, section 
     */
    public bool IsSubset(LinearConstraintSystem/*!*/ lcs) {
      Contract.Requires(lcs != null);
      if (lcs.IsBottom()) {
        return true;
      } else if (this.IsBottom()) {
        return false;
#if DEBUG
#else
      } else if (this.IsTop()) {  // optimization -- this case not needed for correctness
        return true;
      } else if (lcs.IsTop()) {  // optimization -- this case not needed for correctness
        return false;
#endif
      } else {
        // phase 0: check if frame dimensions are a superset of the constraint dimensions
        ISet /*IVariable!*//*!*/ frameDims = lcs.GetDefinedDimensions();
        Contract.Assert(frameDims != null);
#if DEBUG_PRINT
        Console.WriteLine("DEBUG: IsSubset:");
        Console.WriteLine("  --- this:");
        this.Dump();
        Console.WriteLine("  --- lcs:");
        lcs.Dump();
        Console.WriteLine("  ---");
#endif
        foreach (LinearConstraint/*!*/ cc in cce.NonNull(this.Constraints)) {
          Contract.Assert(cc != null);
#if DEBUG_PRINT
          Console.WriteLine("   cc: {0}", cc);
          Console.WriteLine("   cc.GetDefinedDimensions(): {0}", cc.GetDefinedDimensions());
#endif

          if (!Contract.ForAll(cc.GetDefinedDimensionsGeneric(), var => frameDims.Contains(var))) {
#if DEBUG_PRINT
            Console.WriteLine("  ---> phase 0 subset violated, return false from IsSubset");
#endif
            return false;
          }
        }
      }

      // phase 1: check frame vertices against each constraint...
      foreach (FrameElement/*!*/ v in cce.NonNull(lcs.FrameVertices)) {
        Contract.Assert(v != null);
        foreach (LinearConstraint/*!*/ cc in this.Constraints) {
          Contract.Assert(cc != null);
          Rational q = cc.EvaluateLhs(v);
          if (cc.Relation == LinearConstraint.ConstraintRelation.LE) {
            if (!(q <= cc.rhs)) {
#if DEBUG_PRINT
              Console.WriteLine("  ---> phase 1a subset violated, return false from IsSubset");
#endif
              return false;
            }
          } else {
            if (!(q == cc.rhs)) {
#if DEBUG_PRINT
              Console.WriteLine("  ---> phase 1b subset violated, return false from IsSubset");
#endif
              return false;
            }
          }
        }
      }

      // phase 2: check frame rays against each constraint...
      // To check if a ray "r" falls within a constraint "cc", we add the vector "r" to
      // any point "p" on the side of the half-space or plane described by constraint, and
      // then check if the resulting point satisfies the constraint.  That is, we check (for
      // an inequality constraint with coefficients a1,a2,...,an and right-hand side
      // constant C):
      //     a1*(r1+p1) + a2*(r2+p2) + ... + an*(rn+pn) <= C
      // Equivalently:
      //     a1*r1 + a2*r2 + ... + an*rn + a1*p1 + a2*p2 + ... + an*pn <= C
      // To find a point "p", we can pick out a coordinate, call it 1, with a non-zero
      // coefficient in the constraint, and then choose "p" as the point that has the
      // value C/a1 in coordinate 1 and has 0 in all other coordinates.  We then check:
      //     a1*r1 + a2*r2 + ... + an*rn + a1*(C/a1) + a2*0 + ... + an*0 <= C
      // which simplifies to:
      //     a1*r1 + a2*r2 + ... + an*rn + C <= C
      // which in turn simplifies to:
      //     a1*r1 + a2*r2 + ... + an*rn <= 0
      // If the constraint is an equality constraint, we simply replace "<=" with "=="
      // above.
      foreach (FrameElement/*!*/ r in cce.NonNull(lcs.FrameRays)) {
        Contract.Assert(r != null);
        System.Diagnostics.Debug.Assert(r != null, "encountered a null ray...");
        foreach (LinearConstraint/*!*/ cc in this.Constraints) {
          Contract.Assert(cc != null);
          System.Diagnostics.Debug.Assert(cc != null, "encountered an null constraint...");
          Rational q = cc.EvaluateLhs(r);
          if (cc.Relation == LinearConstraint.ConstraintRelation.LE) {
            if (q.IsPositive) {
#if DEBUG_PRINT
              Console.WriteLine("  ---> phase 2a subset violated, return false from IsSubset");
#endif
              return false;
            }
          } else {
            if (q.IsNonZero) {
#if DEBUG_PRINT
              Console.WriteLine("  ---> phase 2b subset violated, return false from IsSubset");
#endif
              return false;
            }
          }
        }
      }

      // phase 3: check frame lines against each constraint...
      // To check if a line "L" falls within a constraint "cc", we check if both the
      // vector "L" and "-L", interpreted as rays, fall within the constraint.  From
      // the discussion above, this means we check the following two properties:
      //     a1*L1 + a2*L2 + ... + an*Ln <= 0                 (*)
      //     a1*(-L1) + a2*(-L2) + ... + an*(-Ln) <= 0
      // The second of these lines can be rewritten as:
      //     - a1*L1 - a2*L2 - ... - an*Ln <= 0
      // which is equivalent to:
      //     -1 * (a1*L1 + a2*L2 + ... + an*Ln) <= 0
      // Multiplying both sides by -1 and flipping the direction of the inequality,
      // we have:
      //     a1*L1 + a2*L2 + ... + an*Ln >= 0                 (**)
      // Putting (*) and (**) together, we conclude that we need to check:
      //     a1*L1 + a2*L2 + ... + an*Ln == 0
      // If the constraint is an equality constraint, we end up with the same equation.
      foreach (FrameElement/*!*/ line in cce.NonNull(lcs.FrameLines)) {
        Contract.Assert(line != null);
        System.Diagnostics.Debug.Assert(line != null, "encountered a null line...");
        foreach (LinearConstraint/*!*/ cc in this.Constraints) {
          Contract.Assert(cc != null);
          System.Diagnostics.Debug.Assert(cc != null, "encountered an null constraint...");
          Rational q = cc.EvaluateLhs(line);
          if (q.IsNonZero) {
#if DEBUG_PRINT
            Console.WriteLine("  ---> phase 3 subset violated, return false from IsSubset");
#endif
            return false;
          }
        }
      }

#if DEBUG_PRINT
      Console.WriteLine("  ---> IsSubset returns true");
#endif
      return true;
    }

    public LinearConstraintSystem/*!*/ Meet(LinearConstraintSystem/*!*/ lcs) {
      Contract.Requires(lcs != null);
      Contract.Requires((this.Constraints != null));
      Contract.Requires((lcs.Constraints != null));
      Contract.Ensures(Contract.Result<LinearConstraintSystem>() != null);
      ArrayList /*LinearConstraint*/ clist = new ArrayList(this.Constraints.Count + lcs.Constraints.Count);
      clist.AddRange(this.Constraints);
      clist.AddRange(lcs.Constraints);
      return new LinearConstraintSystem(clist);
    }

#if DEBUG_PRINT
    public LinearConstraintSystem Join(LinearConstraintSystem lcs)
    {
      Console.WriteLine("===================================================================================");
      Console.WriteLine("DEBUG: Join");
      Console.WriteLine("Join: this=");
      Dump();
      Console.WriteLine("Join: lcs=");
      lcs.Dump();
      LinearConstraintSystem z = JoinX(lcs);
      Console.WriteLine("----------Join------------------------------>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
      Console.WriteLine("Join: result=");
      z.Dump();
      Console.WriteLine("===================================================================================");
      return z;
    }
#endif

    /// <summary>
    /// The join is computed as described in section 4.4 in Cousot and Halbwachs.
    /// </summary>
    /// <param name="lcs"></param>
    /// <returns></returns>
#if DEBUG_PRINT
    public LinearConstraintSystem JoinX(LinearConstraintSystem lcs) {
#else
    public LinearConstraintSystem/*!*/ Join(LinearConstraintSystem/*!*/ lcs) {
      Contract.Requires(lcs != null);
      Contract.Ensures(Contract.Result<LinearConstraintSystem>() != null);
#endif

      if (this.IsBottom()) {
        return cce.NonNull(lcs.Clone());
      } else if (lcs.IsBottom()) {
        return cce.NonNull(this.Clone());
      } else if (this.IsTop() || lcs.IsTop()) {
        return new LinearConstraintSystem(new ArrayList /*LinearConstraint*/ ());
      } else {
        LinearConstraintSystem/*!*/ z;
        // Start from the "larger" of the two frames (this is just a heuristic measure intended
        // to save work).
        Contract.Assume(this.FrameVertices != null);
        Contract.Assume(this.FrameRays != null);
        Contract.Assume(this.FrameLines != null);
        Contract.Assume(lcs.FrameVertices != null);
        Contract.Assume(lcs.FrameRays != null);
        Contract.Assume(lcs.FrameLines != null);
        if (this.FrameVertices.Count + this.FrameRays.Count + this.FrameLines.Count - this.FrameDimensions.Count <
          lcs.FrameVertices.Count + lcs.FrameRays.Count + lcs.FrameLines.Count - lcs.FrameDimensions.Count) {
          z = cce.NonNull(lcs.Clone());
          lcs = this;
        } else {
          z = cce.NonNull(this.Clone());
        }
#if DEBUG_PRINT
        Console.WriteLine("DEBUG: LinearConstraintSystem.Join ---------------");
        Console.WriteLine("z:");
        z.Dump();
        Console.WriteLine("lcs:");
        lcs.Dump();
#endif

        // Start by explicating the implicit lines of z for the dimensions dims(lcs)-dims(z).
        foreach (IVariable/*!*/ dim in lcs.FrameDimensions) {
          Contract.Assert(dim != null);
          if (!z.FrameDimensions.Contains(dim)) {
            z.FrameDimensions.Add(dim);
            FrameElement line = new FrameElement();
            line.AddCoordinate(dim, Rational.ONE);
            // Note:  AddLine is not called (because the line already exists in z--it's just that
            // it was represented implicitly).  Instead, just tack the explicit representation onto
            // FrameLines.
            Contract.Assume(z.FrameLines != null);
            z.FrameLines.Add(line);
#if DEBUG_PRINT
            Console.WriteLine("Join: After explicating line: {0}", line);
            z.Dump();
#endif
          }
        }

        // Now, the vertices, rays, and lines can be added.
        foreach (FrameElement/*!*/ v in lcs.FrameVertices) {
          Contract.Assert(v != null);
          z.AddVertex(v);
#if DEBUG_PRINT
          Console.WriteLine("Join: After adding vertex: {0}", v);
          z.Dump();
#endif
        }
        foreach (FrameElement/*!*/ r in lcs.FrameRays) {
          Contract.Assert(r != null);
          z.AddRay(r);
#if DEBUG_PRINT
          Console.WriteLine("Join: After adding ray: {0}", r);
          z.Dump();
#endif
        }
        foreach (FrameElement/*!*/ l in lcs.FrameLines) {
          Contract.Assert(l != null);
          z.AddLine(l);
#if DEBUG_PRINT
          Console.WriteLine("Join: After adding line: {0}", l);
          z.Dump();
#endif
        }
        // also add to z the implicit lines of lcs
        foreach (IVariable/*!*/ dim in z.FrameDimensions) {
          Contract.Assert(dim != null);
          if (!lcs.FrameDimensions.Contains(dim)) {
            // "dim" is a dimension that's explicit in "z" but implicit in "lcs"
            FrameElement line = new FrameElement();
            line.AddCoordinate(dim, Rational.ONE);
            z.AddLine(line);
#if DEBUG_PRINT
            Console.WriteLine("Join: After adding lcs's implicit line: {0}", line);
            z.Dump();
#endif
          }
        }

        z.SimplifyFrame();
        z.SimplifyConstraints();
        z.CheckInvariant();
#if DEBUG_PRINT
        Console.WriteLine("Join: Returning z:");
        z.Dump();
        Console.WriteLine("----------------------------------------");
#endif
        return z;
      }
    }

#if DEBUG_PRINT
    public LinearConstraintSystem Widen(LinearConstraintSystem lcs)
    {
      Console.WriteLine("===================================================================================");
      Console.WriteLine("DEBUG: Widen");
      Console.WriteLine("Widen: this=");
      Dump();
      Console.WriteLine("Widen: lcs=");
      lcs.Dump();
      LinearConstraintSystem z = WidenX(lcs);
      Console.WriteLine("----------Widen------------------------------>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
      Console.WriteLine("Widen: result=");
      z.Dump();
      Console.WriteLine("===================================================================================");
      return z;
    }
#endif

#if DEBUG_PRINT
    public LinearConstraintSystem WidenX(LinearConstraintSystem lcs){
#else
    public LinearConstraintSystem/*!*/ Widen(LinearConstraintSystem/*!*/ lcs) {
      Contract.Requires(lcs != null);
      Contract.Ensures(Contract.Result<LinearConstraintSystem>() != null);
#endif
      if (this.IsBottom()) {
        return cce.NonNull(lcs.Clone());
      } else if (lcs.IsBottom()) {
        return cce.NonNull(this.Clone());
      } else if (this.IsTop() || lcs.IsTop()) {
        return new LinearConstraintSystem(new ArrayList /*LinearConstraint*/ ());
      }

      // create new LCS, we will add only verified constraints to this...
      ArrayList /*LinearConstraint*/ newConstraints = new ArrayList /*LinearConstraint*/ ();
      Contract.Assume(this.Constraints != null);
      foreach (LinearConstraint/*!*/ ccX in this.Constraints) {
        Contract.Assert(ccX != null);
        LinearConstraint cc = ccX;
#if DEBUG_PRINT
        Console.WriteLine("Widen checking: Starting to check constraint: {0}", cc);
#endif
        if (cc.IsConstant()) {
          // (Can this ever occur in the stable state of a LinearConstraintSystem?  --KRML)
          // constraint is unaffected by the frame components
#if DEBUG_PRINT
          Console.WriteLine("Widen checking:   --Adding it!");
#endif
          newConstraints.Add(cc);
          continue;
        }

        // PHASE I: verify constraints against all frame vertices...

        foreach (FrameElement/*!*/ vertex in cce.NonNull(lcs.FrameVertices)) {
          Contract.Assert(vertex != null);
          Rational lhs = cc.EvaluateLhs(vertex);
          if (lhs > cc.rhs) {
            // the vertex does not satisfy the inequality <=
            if (cc.Relation == LinearConstraint.ConstraintRelation.LE) {
#if DEBUG_PRINT
              Console.WriteLine("Widen checking:   throwing out because of vertex: {0}", vertex);
#endif
              goto CHECK_NEXT_CONSTRAINT;
            } else {
              // ... but it does satisfy the inequality >=
#if DEBUG_PRINT
              Console.WriteLine("Widen checking:   throwing out <= because of vertex: {0}", vertex);
#endif
              cc = cc.ChangeRelationToAtLeast();
#if DEBUG_PRINT
              Console.WriteLine("Widen checking:   left with constraint: {0}", cc);
#endif
            }
          } else if (cc.Relation == LinearConstraint.ConstraintRelation.EQ && lhs < cc.rhs) {
            // the vertex does not satisfy the inequality >=, and the constraint is an equality constraint
#if DEBUG_PRINT
            Console.WriteLine("Widen checking:   throwing out >= because of vertex: {0}", vertex);
#endif
            cc = cc.ChangeRelation(LinearConstraint.ConstraintRelation.LE);
#if DEBUG_PRINT
            Console.WriteLine("Widen checking:   left with contraint: {0}", cc);
#endif
          }
        }

        // PHASE II: verify constraints against all frame rays...

        foreach (FrameElement/*!*/ ray in cce.NonNull(lcs.FrameRays)) {
          Contract.Assert(ray != null);
          // The following assumes the constraint to have some dimension with a non-zero coefficient
          Rational lhs = cc.EvaluateLhs(ray);
          if (lhs.IsPositive) {
            // the ray does not satisfy the inequality <=
            if (cc.Relation == LinearConstraint.ConstraintRelation.LE) {
#if DEBUG_PRINT
              Console.WriteLine("Widen checking:   throwing out because of ray: {0}", ray);
#endif
              goto CHECK_NEXT_CONSTRAINT;
            } else {
              // ... but it does satisfy the inequality >=
#if DEBUG_PRINT
              Console.WriteLine("Widen checking:   throwing out <= because of ray: {0}", ray);
#endif
              cc = cc.ChangeRelationToAtLeast();
#if DEBUG_PRINT
              Console.WriteLine("Widen checking:   left with contraint: {0}", cc);
#endif
            }
          } else if (cc.Relation == LinearConstraint.ConstraintRelation.EQ && lhs.IsNegative) {
            // the ray does not satisfy the inequality >=, and the constraint is an equality constraint
#if DEBUG_PRINT
            Console.WriteLine("Widen checking:   throwing out >= because of ray: {0}", ray);
#endif
            cc = cc.ChangeRelation(LinearConstraint.ConstraintRelation.LE);
#if DEBUG_PRINT
            Console.WriteLine("Widen checking:   left with constraint: {0}", cc);
#endif
          }
        }

        // PHASE III: verify constraints against all frame lines...

        foreach (FrameElement/*!*/ line in cce.NonNull(lcs.FrameLines)) {
          Contract.Assert(line != null);
          // The following assumes the constraint to have some dimension with a non-zero coefficient
          Rational lhs = cc.EvaluateLhs(line);
          if (!lhs.IsZero) {
            // The line satisfies neither the inequality <= nor the equality ==
#if DEBUG_PRINT
            Console.WriteLine("Widen checking:   throwing out because of line: {0}", line);
#endif
            goto CHECK_NEXT_CONSTRAINT;
          }
        }

        // constraint has been verified, so add to new constraint system
#if DEBUG_PRINT
        Console.WriteLine("Widen checking:   --Adding it!");
#endif
        newConstraints.Add(cc);

      CHECK_NEXT_CONSTRAINT: {
        }
#if DEBUG_PRINT
        Console.WriteLine("Widen checking: done with that constraint");
#endif
      }

      return new LinearConstraintSystem(newConstraints);
    }

#if DEBUG_PRINT
    public LinearConstraintSystem Project(IVariable/*!*/ dim){
Contract.Requires(dim != null);
      Console.WriteLine("===================================================================================");
      Console.WriteLine("DEBUG: Project(dim={0})", dim);
      Console.WriteLine("Project: this=");
      Dump();
      LinearConstraintSystem z = ProjectX(dim);
      Console.WriteLine("----------Project------------------------------>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
      Console.WriteLine("Project: result=");
      z.Dump();
      Console.WriteLine("===================================================================================");
      return z;
    }
#endif

#if DEBUG_PRINT
    public LinearConstraintSystem ProjectX(IVariable/*!*/ dim){Contract.Requires(dim != null);Contract.Requires(this.Constraints != null);
#else
    public LinearConstraintSystem/*!*/ Project(IVariable/*!*/ dim) {
      Contract.Requires(dim != null);
      Contract.Requires(this.Constraints != null);
      Contract.Ensures(Contract.Result<LinearConstraintSystem>() != null);
#endif


      ArrayList /*LinearConstraint!*//*!*/ cc = Project(dim, Constraints);
      Contract.Assert(cc != null);
      return new LinearConstraintSystem(cc);
    }

#if DEBUG_PRINT
    public LinearConstraintSystem Rename(IVariable/*!*/ oldName, IVariable/*!*/ newName){
Contract.Requires(newName != null);
Contract.Requires(oldName != null);
      Console.WriteLine("===================================================================================");
      Console.WriteLine("DEBUG: Rename(oldName={0}, newName={1})", oldName, newName);
      Console.WriteLine("Rename: this=");
      Dump();
      LinearConstraintSystem z = RenameX(oldName, newName);
      Console.WriteLine("----------Rename------------------------------>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
      Console.WriteLine("Rename: result=");
      z.Dump();
      Console.WriteLine("===================================================================================");
      return z;
    }
#endif

#if DEBUG_PRINT
    public LinearConstraintSystem RenameX(IVariable/*!*/ oldName, IVariable/*!*/ newName){Contract.Requires(oldName != null);Contract.Requires(newName != null);
#else
    public LinearConstraintSystem/*!*/ Rename(IVariable/*!*/ oldName, IVariable/*!*/ newName) {
      Contract.Requires(oldName != null);
      Contract.Requires(newName != null);
      Contract.Ensures(Contract.Result<LinearConstraintSystem>() != null);
#endif
      if (this.Constraints == null) {
        System.Diagnostics.Debug.Assert(this.FrameVertices == null);
        System.Diagnostics.Debug.Assert(this.FrameRays == null);
        System.Diagnostics.Debug.Assert(this.FrameLines == null);
        return this;
      }
      IMutableSet /*IVariable!*//*!*/ dims = this.FrameDimensions;
      Contract.Assert(dims != null);
      if (!dims.Contains(oldName)) {
        return this;
      }

      LinearConstraintSystem z = new LinearConstraintSystem();
      z.FrameDimensions = cce.NonNull((HashSet/*!*/ /*IVariable!*/)dims.Clone());
      z.FrameDimensions.Remove(oldName);
      z.FrameDimensions.Add(newName);

      z.Constraints = new ArrayList /*LinearConstraint!*/ (this.Constraints.Count);
      foreach (LinearConstraint/*!*/ lc in cce.NonNull(this.Constraints)) {
        Contract.Assert(lc != null);
        z.Constraints.Add(lc.Rename(oldName, newName));
      }
      z.FrameVertices = RenameInFE(cce.NonNull(this.FrameVertices), oldName, newName);
      z.FrameRays = RenameInFE(cce.NonNull(this.FrameRays), oldName, newName);
      z.FrameLines = RenameInFE(cce.NonNull(this.FrameLines), oldName, newName);
      return z;
    }

    static ArrayList /*FrameElement*/ RenameInFE(ArrayList/*!*/ /*FrameElement*/ list, IVariable/*!*/ oldName, IVariable/*!*/ newName) {
      Contract.Requires(list != null);
      Contract.Requires(newName != null);
      Contract.Requires(oldName != null);
      ArrayList/*FrameElement!*//*!*/ z = new ArrayList/*FrameElement!*/ (list.Count);
      Contract.Assert(z != null);
      foreach (FrameElement/*!*/ fe in list) {
        Contract.Assert(fe != null);
        z.Add(fe.Rename(oldName, newName));
      }
      System.Diagnostics.Debug.Assert(z.Count == list.Count);
      return z;
    }

    // --------------------------------------------------------------------------------------------------------
    // ------------------ support routines --------------------------------------------------------------------
    // --------------------------------------------------------------------------------------------------------

    /// <summary>
    /// Returns a set of constraints that is the given set of constraints with dimension "dim"
    /// projected out.  See Cousot and Halbwachs, section 3.3.1.1.
    /// </summary>
    /// <param name="dim"></param>
    /// <param name="constraints"></param>
    /// <returns></returns>
    static ArrayList /*LinearConstraint!*//*!*/ Project(IVariable/*!*/ dim, ArrayList /*LinearConstraint!*//*!*/ constraints) {
      Contract.Requires(constraints != null);
      Contract.Requires(dim != null);
      Contract.Ensures(Contract.Result<ArrayList>() != null);
      // Sort the inequality constaints into ones where dimension "dim" is 0, negative, and
      // positive, respectively.  Put equality constraints with a non-0 "dim" into "eq".
      ArrayList /*LinearConstraint!*//*!*/ final = new ArrayList /*LinearConstraint!*/ ();
      ArrayList /*LinearConstraint!*//*!*/ negative = new ArrayList /*LinearConstraint!*/ ();
      ArrayList /*LinearConstraint!*//*!*/ positive = new ArrayList /*LinearConstraint!*/ ();
      ArrayList /*LinearConstraint!*//*!*/ eq = new ArrayList /*LinearConstraint!*/ ();
      foreach (LinearConstraint/*!*/ cc in constraints) {
        Contract.Assert(cc != null);
        Rational coeff = cc[dim];
        if (coeff.IsZero) {
          LinearConstraint lc = cce.NonNull(cc.Clone());
          if (!lc.IsConstant()) {
            lc.RemoveDimension(dim);
            final.Add(lc);
          }
        } else if (cc.Relation == LinearConstraint.ConstraintRelation.EQ) {
          eq.Add(cc);
        } else if (coeff.IsNegative) {
          negative.Add(cc);
        } else {
          System.Diagnostics.Debug.Assert(coeff.IsPositive);
          positive.Add(cc);
        }
      }

      if (eq.Count != 0) {
        LinearConstraint eqConstraint = (LinearConstraint/*!*/)cce.NonNull(eq[eq.Count - 1]);
        eq.RemoveAt(eq.Count - 1);
        Rational eqC = -eqConstraint[dim];

        foreach (ArrayList /*LinearConstraint!*/ list in new ArrayList[] { eq, negative, positive }) {
          Contract.Assert(list != null);
          foreach (LinearConstraint/*!*/ lcX in list) {
            Contract.Assert(lcX != null);
            LinearConstraint lc = cce.NonNull(lcX.Clone());
            lc.AddMultiple(lc[dim] / eqC, eqConstraint);
            System.Diagnostics.Debug.Assert(lc[dim].IsZero);
            if (!lc.IsConstant()) {
              lc.RemoveDimension(dim);
              final.Add(lc);
            } else {
              System.Diagnostics.Debug.Assert(lc.IsConstantSatisfiable());
            }
          }
        }
      } else {
        // Consider all pairs of constraints with (negative,positive) coefficients of "dim".
        foreach (LinearConstraint/*!*/ cn in negative) {
          Contract.Assert(cn != null);
          Rational dn = -cn[dim];
          System.Diagnostics.Debug.Assert(dn.IsNonNegative);
          foreach (LinearConstraint/*!*/ cp in positive) {
            Contract.Assert(cp != null);
            Rational dp = cp[dim];

            LinearConstraint lc = new LinearConstraint(LinearConstraint.ConstraintRelation.LE);
            lc.AddMultiple(dn, cp);
            lc.AddMultiple(dp, cn);
            System.Diagnostics.Debug.Assert(lc[dim].IsZero);
            if (!lc.IsConstant()) {
              lc.RemoveDimension(dim);
              final.Add(lc);
            } else {
              System.Diagnostics.Debug.Assert(lc.IsConstantSatisfiable());
            }
          }
        }
      }

      return final;
    }

    /// <summary>
    /// Initializes FrameVertices, FrameRays, FrameLines, and FrameDimensions, see
    /// Cousot and Halbwachs, section 3.4.  Any previous values of these fields are
    /// ignored and overwritten.
    /// 
    /// If the set of Constraints is unsatisfiable, then "this" is changed into Bottom.
    /// </summary>
    void GenerateFrameFromConstraints() {
      if (Constraints == null) {
        FrameVertices = null;
        FrameRays = null;
        FrameLines = null;
        FrameDimensions = new HashSet /*IVariable!*/ ();
        return;
      }

      // Step 1 (see Cousot and Halbwachs, section 3.4.3):  create a Simplex Tableau.
#if DEBUG_PRINT
      Console.WriteLine("DEBUG: --- GenerateFrameFromConstraint ---");
      Console.WriteLine("Constraints:");
      foreach (LinearConstraint cc in Constraints) 
      {
        Console.WriteLine("  {0}", cc);
      }
#endif
      SimplexTableau tableau = new SimplexTableau(Constraints);
#if DEBUG_PRINT
      Console.WriteLine("Initial tableau:");
      tableau.Dump();
#endif
      FrameDimensions = tableau.GetDimensions();
#if DEBUG_PRINT
      Console.WriteLine("Dimensions:");
      foreach (object dim in FrameDimensions) 
      {
        Console.Write("  {0}", dim);
      }
      Console.WriteLine();
#endif

      // Step 3 and 2: Put as many initial variables as possible into basis, then check if
      // we reached a feasible basis
      tableau.AddInitialVarsToBasis();
#if DEBUG_PRINT
      Console.WriteLine("Tableau after Step 3:");
      tableau.Dump();
#endif
      if (!tableau.IsFeasibleBasis) {
        // The polyhedron is empty (according to Cousot and Halbwachs)
        ChangeIntoBottom();
        return;
      }

      FrameVertices = new ArrayList /*FrameElement*/ ();
      FrameRays = new ArrayList /*FrameElement*/ ();
      FrameLines = new ArrayList /*FrameElement*/ ();
      if (FrameDimensions.Count == 0) {
        // top element
        return;
      }

      if (tableau.AllInitialVarsInBasis) {
        // All initial variables are in basis; there are no lines.
#if DEBUG_PRINT
        Console.WriteLine("Tableau after Steps 2 and 3 (all initial variables in basis):");
        tableau.Dump();
#endif
      } else {
        // There are lines
#if DEBUG_PRINT
        Console.WriteLine("Tableau after Steps 2 and 3 (NOT all initial variables in basis--there are lines):");
        tableau.Dump();
#endif
        // Step 4.2: Pick out the lines, then produce the tableau for a new polyhedron without those lines.
        ArrayList /*LinearConstraint*/ moreConstraints = cce.NonNull((ArrayList/*!*/ /*LinearConstraint*/)Constraints.Clone());
        tableau.ProduceLines(FrameLines, moreConstraints);
        tableau = new SimplexTableau(moreConstraints);
#if DEBUG_PRINT
        Console.WriteLine("Lines produced:");
        foreach (FrameElement line in FrameLines) 
        {
          Console.WriteLine("  {0}", line);
        }
        Console.WriteLine("The new list of constraints is:");
        foreach (LinearConstraint c in moreConstraints) 
        {
          Console.WriteLine("  {0}", c);
        }
        Console.WriteLine("Tableau after producing lines in Step 4.2:");
        tableau.Dump();
#endif

        // Repeat step 3 for the new tableau.
        // Since the new tableau contains no lines, the following call should cause all initial
        // variables to be in basis (see step 4.2 in section 3.4.3 of Cousot and Halbwachs).
        tableau.AddInitialVarsToBasis();
        System.Diagnostics.Debug.Assert(tableau.AllInitialVarsInBasis);
        System.Diagnostics.Debug.Assert(tableau.IsFeasibleBasis);  // the new tableau represents a set of feasible constraints, so this basis should be found to be feasible
#if DEBUG_PRINT
        Console.WriteLine("Tableau after all initial variables have been moved into basis:");
        tableau.Dump();
#endif
      }

      // Step 4.1: One vertex has been found.  Find all others, too.
      tableau.TraverseVertices(FrameVertices, FrameRays);
#if DEBUG_PRINT
      Console.WriteLine("Tableau after vertex traversal:");
      tableau.Dump();
#endif
    }

    class LambdaDimension : IVariable {
      readonly int id;
      static int count = 0;

      /// <summary>
      /// Return the name of the variable
      /// </summary>
      public string Name {
        get {
          Contract.Ensures(Contract.Result<string>() != null);

          return this.ToString();
        }
      }

      public LambdaDimension() {
        id = count;
        count++;
      }
      [Pure]
      public override string/*!*/ ToString() {
        Contract.Ensures(Contract.Result<string>() != null);
        return "lambda" + id;
      }
      [Pure]
      public object DoVisit(ExprVisitor/*!*/ visitor) {
        //Contract.Requires(visitor != null);
        return visitor.VisitVariable(this);
      }
    }

    /// <summary>
    /// Adds a vertex to the frame of "this" and updates Constraints accordingly, see
    /// Cousot and Halbwachs, section 3.3.1.1.  However, this method does not simplify
    /// Constraints after the operation; that remains the caller's responsibility (which
    /// gives the caller the opportunity to make multiple calls to AddVertex, AddRay,
    /// and AddLine before calling SimplifyConstraints).
    /// Assumes Constraints (and the frame fields) to be non-null.
    /// </summary>
    /// <param name="vertex"></param>
    void AddVertex(FrameElement/*!*/ vertex) {
      Contract.Requires(vertex != null);
      Contract.Requires(this.FrameVertices != null);
#if DEBUG_PRINT
      Console.WriteLine("DEBUG: AddVertex called on {0}", vertex);
      Console.WriteLine("  Initial constraints:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif

      FrameVertices.Add(vertex.Clone());
#if FIXED_DESERIALIZER      
      Contract.Assert(Contract.ForAll(vertex.GetDefinedDimensions() , var=> FrameDimensions.Contains(var)));
#endif

      // We use a new temporary dimension.
      IVariable/*!*/ lambda = new LambdaDimension();

      // We change the constraints A*X <= B into
      //     A*X + (A*vector - B)*lambda <= A*vector.
      // That means that each row k in A (which corresponds to one LinearConstraint
      // in Constraints) is changed by adding
      //     (A*vector - B)[k] * lambda
      // to row k and changing the right-hand side of row k to
      //     (A*vector)[k]
      // Note:
      //     (A*vector - B)[k]
      //  =      { vector subtraction is pointwise }
      //     (A*vector)[k] - B[k]
      //  =      { A*vector is a row vector whose every row i is the dot-product of
      //           row i of A with the column vector "vector" }
      //     A[k]*vector - B[k]
      foreach (LinearConstraint/*!*/ cc in cce.NonNull(Constraints)) {
        Contract.Assert(cc != null);
        Rational d = cc.EvaluateLhs(vertex);
        cc.SetCoefficient(lambda, d - cc.rhs);
        cc.rhs = d;
      }

      // We also add the constraints that lambda lies between 0 ...
      LinearConstraint la = new LinearConstraint(LinearConstraint.ConstraintRelation.LE);
      la.SetCoefficient(lambda, Rational.MINUS_ONE);
      la.rhs = Rational.ZERO;
      Constraints.Add(la);
      // ... and 1.
      la = new LinearConstraint(LinearConstraint.ConstraintRelation.LE);
      la.SetCoefficient(lambda, Rational.ONE);
      la.rhs = Rational.ONE;
      Constraints.Add(la);
#if DEBUG_PRINT
      Console.WriteLine("  Constraints after addition:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif

      // Finally, project out the dummy dimension.
      Constraints = Project(lambda, Constraints);

#if DEBUG_PRINT
      Console.WriteLine("  Resulting constraints:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif
    }

    /// <summary>
    /// Adds a ray to the frame of "this" and updates Constraints accordingly, see
    /// Cousot and Halbwachs, section 3.3.1.1.  However, this method does not simplify
    /// Constraints after the operation; that remains the caller's responsibility (which
    /// gives the caller the opportunity to make multiple calls to AddVertex, AddRay,
    /// and AddLine before calling SimplifyConstraints).
    /// Assumes Constraints (and the frame fields) to be non-null.
    /// </summary>
    /// <param name="ray"></param>
    void AddRay(FrameElement/*!*/ ray) {
      Contract.Requires(ray != null);
      Contract.Requires(this.FrameRays != null);
#if DEBUG_PRINT
      Console.WriteLine("DEBUG: AddRay called on {0}", ray);
      Console.WriteLine("  Initial constraints:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif

      FrameRays.Add(ray.Clone());
#if FIXED_DESERIALIZER      
      Contract.Assert(Contract.ForAll(ray.GetDefinedDimensions() , var=> FrameDimensions.Contains(var)));
#endif

      // We use a new temporary dimension.
      IVariable/*!*/ lambda = new LambdaDimension();

      // We change the constraints A*X <= B into
      //     A*X - (A*ray)*lambda <= B.
      // That means that each row k in A (which corresponds to one LinearConstraint
      // in Constraints) is changed by subtracting
      //     (A*ray)[k] * lambda
      // from row k.
      // Note:
      //     (A*ray)[k]
      //  =      { A*ray is a row vector whose every row i is the dot-product of
      //           row i of A with the column vector "ray" }
      //     A[k]*ray
      foreach (LinearConstraint/*!*/ cc in cce.NonNull(Constraints)) {
        Contract.Assert(cc != null);
        Rational d = cc.EvaluateLhs(ray);
        cc.SetCoefficient(lambda, -d);
      }

      // We also add the constraints that lambda is at least 0.
      LinearConstraint la = new LinearConstraint(LinearConstraint.ConstraintRelation.LE);
      la.SetCoefficient(lambda, Rational.MINUS_ONE);
      la.rhs = Rational.ZERO;
      Constraints.Add(la);
#if DEBUG_PRINT
      Console.WriteLine("  Constraints after addition:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif

      // Finally, project out the dummy dimension.
      Constraints = Project(lambda, Constraints);

#if DEBUG_PRINT
      Console.WriteLine("  Resulting constraints:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif
    }

    /// <summary>
    /// Adds a line to the frame of "this" and updates Constraints accordingly, see
    /// Cousot and Halbwachs, section 3.3.1.1.  However, this method does not simplify
    /// Constraints after the operation; that remains the caller's responsibility (which
    /// gives the caller the opportunity to make multiple calls to AddVertex, AddRay,
    /// and AddLine before calling SimplifyConstraints).
    /// Assumes Constraints (and the frame fields) to be non-null.
    /// </summary>
    /// <param name="line"></param>
    void AddLine(FrameElement/*!*/ line) {
      Contract.Requires(line != null);
      Contract.Requires(this.FrameLines != null);
      // Note:  The code for AddLine is identical to that of AddRay, except the AddLine
      // does not introduce the constraint 0 <= lambda.  (One could imagine sharing the
      // code between AddRay and AddLine.)
#if DEBUG_PRINT
      Console.WriteLine("DEBUG: AddLine called on {0}", line);
      Console.WriteLine("  Initial constraints:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif

      FrameLines.Add(line.Clone());
#if FIXED_DESERIALIZER      
      Contract.Assert(Contract.ForAll(line.GetDefinedDimensions() , var=> FrameDimensions.Contains(var)));
#endif

      // We use a new temporary dimension.
      IVariable/*!*/ lambda = new LambdaDimension();

      // We change the constraints A*X <= B into
      //     A*X - (A*line)*lambda <= B.
      // That means that each row k in A (which corresponds to one LinearConstraint
      // in Constraints) is changed by subtracting
      //     (A*line)[k] * lambda
      // from row k.
      // Note:
      //     (A*line)[k]
      //  =      { A*line is a row vector whose every row i is the dot-product of
      //           row i of A with the column vector "line" }
      //     A[k]*line
      foreach (LinearConstraint/*!*/ cc in cce.NonNull(Constraints)) {
        Contract.Assert(cc != null);
        Rational d = cc.EvaluateLhs(line);
        cc.SetCoefficient(lambda, -d);
      }

#if DEBUG_PRINT
      Console.WriteLine("  Constraints after addition:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif

      // Finally, project out the dummy dimension.
      Constraints = Project(lambda, Constraints);

#if DEBUG_PRINT
      Console.WriteLine("  Resulting constraints:");
      foreach (LinearConstraint cc in Constraints) {
        Console.WriteLine("    {0}", cc);
      }
#endif
    }

    ISet /*IVariable!*//*!*/ GetDefinedDimensions() {
      Contract.Ensures(Contract.Result<ISet>() != null);
      HashSet /*IVariable!*//*!*/ dims = new HashSet /*IVariable!*/ ();
      foreach (ArrayList p in new ArrayList[] { FrameVertices, FrameRays, FrameLines }) {
        if (p != null) {
          foreach (FrameElement/*!*/ element in p) {
            Contract.Assert(element != null);
            foreach (IVariable/*!*/ dim in element.GetDefinedDimensions()) {
              Contract.Assert(dim != null);
              dims.Add(dim);
            }
          }
        }
      }
      return dims;
    }

    // --------------------------------------------------------------------------------------------------------
    // ------------------ Simplification routines -------------------------------------------------------------
    // --------------------------------------------------------------------------------------------------------

    /// <summary>
    /// Uses the Constraints to simplify the frame.  See section 3.4.4 of Cousot and Halbwachs.
    /// </summary>
    void SimplifyFrame() {
      Contract.Requires(this.Constraints != null);
      SimplificationStatus[]/*!*/ status;

      SimplifyFrameElements(cce.NonNull(FrameVertices), true, Constraints, out status);
      RemoveIrrelevantFrameElements(FrameVertices, status, null);

      SimplifyFrameElements(cce.NonNull(FrameRays), false, Constraints, out status);
      RemoveIrrelevantFrameElements(FrameRays, status, FrameLines);
    }

    enum SimplificationStatus {
      Irrelevant,
      Relevant,
      More
    };

    /// <summary>
    /// For each i, sets status[i] to:
    ///  <ul>
    ///  <li>Irrelevant if ff[i] is irrelevant</li>
    ///  <li>Relevant if ff[i] is irrelevant</li>
    ///  <li>More if vertices is true and ray ff[i] can be replaced by a line ff[i]</li>
    ///  </ul>
    /// </summary>
    /// <param name="ff"></param>
    /// <param name="vertices">true if "ff" contains vertices; false if "ff" contains rays</param>
    /// <param name="constraints"></param>
    /// <param name="status"></param>
    static void SimplifyFrameElements(ArrayList/*!*/ /*FrameElement*/ ff, bool vertices, ArrayList/*!*/ /*LinearConstraint*/ constraints, out SimplificationStatus[]/*!*/ status) {
      Contract.Requires(ff != null);
      Contract.Requires(constraints != null);
      Contract.Ensures(Contract.ValueAtReturn(out status) != null);
      status = new SimplificationStatus[ff.Count];
      bool[,] sat = new bool[ff.Count, constraints.Count];
      for (int i = 0; i < ff.Count; i++) {
        FrameElement f = (FrameElement/*!*/)cce.NonNull(ff[i]);
        int cnt = 0;
        for (int c = 0; c < constraints.Count; c++) {
          LinearConstraint lc = (LinearConstraint/*!*/)cce.NonNull(constraints[c]);
          bool s = lc.IsSaturatedBy(f, vertices);
          if (s) {
            sat[i, c] = true;
            cnt++;
          }
        }
        if (!vertices && cnt == constraints.Count) {
          status[i] = SimplificationStatus.More;
        } else {
          status[i] = SimplificationStatus.Relevant;
        }
      }

      CheckPairSimplifications(sat, status);
    }

    /// <summary>
    /// Requires sat.GetLength(0) == status.Length.
    /// </summary>
    /// <param name="sat"></param>
    /// <param name="status"></param>
    static void CheckPairSimplifications(bool[,]/*!*/ sat, SimplificationStatus[]/*!*/ status) {
      Contract.Requires(status != null);
      Contract.Requires(sat != null);
      Contract.Requires(sat.GetLength(0) == status.Length);
      int M = sat.GetLength(0);
      int N = sat.GetLength(1);

      for (int i = 0; i < M - 1; i++) {
        if (status[i] != SimplificationStatus.Relevant) {
          continue;
        }
        for (int j = i + 1; j < M; j++) {
          if (status[j] != SimplificationStatus.Relevant) {
            continue;
          }
          // check (sat[i,*] <= sat[j,*]) and (sat[i,*] >= sat[j,*])
          int cmp = 0;  // -1: (sat[i,*] <= sat[j,*]),  0: equal,  1: (sat[i,*] >= sat[j,*])
          for (int c = 0; c < N; c++) {
            if (cmp < 0) {
              if (sat[i, c] && !sat[j, c]) {
                // incomparable
                goto NEXT_PAIR;
              }
            } else if (0 < cmp) {
              if (!sat[i, c] && sat[j, c]) {
                // incomparable
                goto NEXT_PAIR;
              }
            } else if (sat[i, c] != sat[j, c]) {
              if (!sat[i, c]) {
                cmp = -1;
              } else {
                cmp = 1;
              }
            }
          }
          if (cmp <= 0) {
            // sat[i,*] <= sat[j,*] holds, so mark i as irrelevant
            status[i] = SimplificationStatus.Irrelevant;
            goto NEXT_OUTER;
          } else {
            // sat[i,*] >= sat[j,*] holds, so mark j as irrelevant
            status[j] = SimplificationStatus.Irrelevant;
          }
        NEXT_PAIR: {
          }
        }
      NEXT_OUTER: {
        }
      }
    }

    static void RemoveIrrelevantFrameElements(ArrayList/*!*/ /*FrameElement*/ ff, SimplificationStatus[]/*!*/ status,
      /*maybe null*/ ArrayList /*FrameElement*/ lines) {
      Contract.Requires(ff != null);
      Contract.Requires(status != null);
      Contract.Requires(ff.Count == status.Length);
      for (int j = ff.Count - 1; 0 <= j; j--) {
        switch (status[j]) {
          case SimplificationStatus.Relevant:
            break;
          case SimplificationStatus.Irrelevant:
#if DEBUG_PRINT
            Console.WriteLine("Removing irrelevant {0}: {1}", lines == null ? "vertex" : "ray", ff[j]);
#endif
            ff.RemoveAt(j);
            break;
          case SimplificationStatus.More:
            System.Diagnostics.Debug.Assert(lines != null);
            FrameElement f = (FrameElement)ff[j];
#if DEBUG_PRINT
            Console.WriteLine("Changing ray into line: {0}", f);
#endif
            ff.RemoveAt(j);
            Contract.Assert(lines != null);
            lines.Add(f);
            break;
        }
      }
    }

    /// <summary>
    /// Uses the frame to simplify Constraints.  See section 3.3.1.2 of Cousot and Halbwachs.
    /// 
    /// Note:  This code does not necessarily eliminate all irrelevant equalities; Cousot and
    /// Halbwachs only claim that the technique eliminates all irrelevant inequalities.
    /// </summary>
    void SimplifyConstraints() {
      if (Constraints == null) {
        return;
      }
      Contract.Assume(this.FrameVertices != null);
      Contract.Assume(this.FrameRays != null);

      SimplificationStatus[] status = new SimplificationStatus[Constraints.Count];
      /*readonly*/
      int feCount = FrameVertices.Count + FrameRays.Count;

      // Create a table that keeps track of which constraints are satisfied by which vertices and rays
      bool[,] sat = new bool[Constraints.Count, FrameVertices.Count + FrameRays.Count];
      for (int i = 0; i < Constraints.Count; i++) {
        status[i] = SimplificationStatus.Relevant;
        LinearConstraint lc = (LinearConstraint/*!*/)cce.NonNull(Constraints[i]);
        int cnt = 0;  // number of vertices and rays that saturate lc
        for (int j = 0; j < FrameVertices.Count; j++) {
          FrameElement vertex = (FrameElement/*!*/)cce.NonNull(FrameVertices[j]);
          if (lc.IsSaturatedBy(vertex, true)) {
            sat[i, j] = true;
            cnt++;
          }
        }
        if (cnt == 0) {
          // no vertex saturates the constraint, so the constraint is irrelevant
          status[i] = SimplificationStatus.Irrelevant;
          continue;
        }
        for (int j = 0; j < FrameRays.Count; j++) {
          FrameElement ray = (FrameElement/*!*/)cce.NonNull(FrameRays[j]);
          if (lc.IsSaturatedBy(ray, false)) {
            sat[i, FrameVertices.Count + j] = true;
            cnt++;
          }
        }
        if (cnt == feCount) {
          status[i] = SimplificationStatus.More;
        } else {
          // Cousot and Halbwachs says that all equalities are found in the way we just tested.
          // If I understand that right, then we should not get here if the constraint is an
          // equality constraint.  The following assertion tests my understanding.  --KRML
          System.Diagnostics.Debug.Assert(lc.Relation == LinearConstraint.ConstraintRelation.LE);
        }
      }

      CheckPairSimplifications(sat, status);

      // Finally, make the changes to the list of constraints
      for (int i = Constraints.Count - 1; 0 <= i; i--) {
        switch (status[i]) {
          case SimplificationStatus.Relevant:
            break;
          case SimplificationStatus.Irrelevant:
#if DEBUG_PRINT
            Console.WriteLine("Removing irrelevant constraint: {0}", Constraints[i]);
#endif
            Constraints.RemoveAt(i);
            break;
          case SimplificationStatus.More:
            LinearConstraint lc = (LinearConstraint/*!*/)cce.NonNull(Constraints[i]);
            if (lc.Relation == LinearConstraint.ConstraintRelation.LE) {
#if DEBUG_PRINT
              Console.WriteLine("Converting the following constraint into an equality: {0}", lc);
#endif
              LinearConstraint lcEq = lc.ChangeRelation(LinearConstraint.ConstraintRelation.EQ);
              Constraints[i] = lcEq;
            }
            break;
        }
      }

      foreach (LinearConstraint/*!*/ lc in Constraints) {
        Contract.Assert(lc != null);
        lc.Normalize();
      }
    }

    // --------------------------------------------------------------------------------------------------------
    // ------------------ Cloning routines --------------------------------------------------------------------
    // --------------------------------------------------------------------------------------------------------

    public LinearConstraintSystem/*!*/ Clone() {
      Contract.Ensures(Contract.Result<LinearConstraintSystem>() != null);
      LinearConstraintSystem z = new LinearConstraintSystem();
      z.FrameDimensions = (IMutableSet /*IVariable!*//*!*/)cce.NonNull(this.FrameDimensions.Clone());
      if (this.Constraints != null) {
        z.Constraints = DeeperListCopy_LC(this.Constraints);
        z.FrameVertices = DeeperListCopy_FE(cce.NonNull(this.FrameVertices));
        z.FrameRays = DeeperListCopy_FE(cce.NonNull(this.FrameRays));
        z.FrameLines = DeeperListCopy_FE(cce.NonNull(this.FrameLines));
      } else {
        System.Diagnostics.Debug.Assert(this.FrameVertices == null);
        System.Diagnostics.Debug.Assert(this.FrameRays == null);
        System.Diagnostics.Debug.Assert(this.FrameLines == null);
        // the constructor should already have set these fields of z to null
        System.Diagnostics.Debug.Assert(z.Constraints == null);
        System.Diagnostics.Debug.Assert(z.FrameVertices == null);
        System.Diagnostics.Debug.Assert(z.FrameRays == null);
        System.Diagnostics.Debug.Assert(z.FrameLines == null);
      }
      return z;
    }

    /// <summary>
    /// Clones "list" and the elements of "list".
    /// </summary>
    /// <param name="list"></param>
    /// <returns></returns>
    ArrayList /*LinearConstraint*/ DeeperListCopy_LC(ArrayList/*!*/ /*LinearConstraint*/ list) {
      Contract.Requires(list != null);
      ArrayList /*LinearConstraint*/ z = new ArrayList /*LinearConstraint*/ (list.Count);
      foreach (LinearConstraint/*!*/ lc in list) {
        Contract.Assert(lc != null);
        z.Add(lc.Clone());
      }
      System.Diagnostics.Debug.Assert(z.Count == list.Count);
      return z;
    }

    /// <summary>
    /// Clones "list" and the elements of "list".
    /// </summary>
    /// <param name="list"></param>
    /// <returns></returns>
    ArrayList /*FrameElement*/ DeeperListCopy_FE(ArrayList/*!*/ /*FrameElement*/ list) {
      Contract.Requires(list != null);
      ArrayList /*FrameElement*/ z = new ArrayList /*FrameElement*/ (list.Count);
      foreach (FrameElement/*!*/ fe in list) {
        Contract.Assert(fe != null);
        z.Add(fe.Clone());
      }
      System.Diagnostics.Debug.Assert(z.Count == list.Count);
      return z;
    }

    // --------------------------------------------------------------------------------------------------------
    // ------------------ Debugging and unit test routines ----------------------------------------------------
    // --------------------------------------------------------------------------------------------------------

    public void Dump() {
      Console.WriteLine("  Constraints:");
      if (Constraints == null) {
        Console.WriteLine("    <bottom>");
      } else {
        foreach (LinearConstraint cc in Constraints) {
          Console.WriteLine("    {0}", cc);
        }
      }

      Console.WriteLine("  FrameDimensions: {0}", FrameDimensions);

      Console.WriteLine("  FrameVerticies:");
      if (FrameVertices == null) {
        Console.WriteLine("    <null>");
      } else {
        foreach (FrameElement fe in FrameVertices) {
          Console.WriteLine("    {0}", fe);
        }
      }

      Console.WriteLine("  FrameRays:");
      if (FrameRays == null) {
        Console.WriteLine("    <null>");
      } else {
        foreach (FrameElement fe in FrameRays) {
          Console.WriteLine("    {0}", fe);
        }
      }

      Console.WriteLine("  FrameLines:");
      if (FrameLines == null) {
        Console.WriteLine("    <null>");
      } else {
        foreach (FrameElement fe in FrameLines) {
          Console.WriteLine("    {0}", fe);
        }
      }
    }

    class TestVariable : IVariable {
      readonly string/*!*/ name;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(name != null);
      }


      public string/*!*/ Name {
        get {
          Contract.Ensures(Contract.Result<string>() != null);

          return name;
        }
      }

      public TestVariable(string/*!*/ name) {
        Contract.Requires(name != null);
        this.name = name;
      }
      [Pure]
      public object DoVisit(ExprVisitor/*!*/ visitor) {
        //Contract.Requires(visitor != null);
        return visitor.VisitVariable(this);
      }
    }

    public static void RunValidationA() {
      IVariable/*!*/ dim1 = new TestVariable("X");
      IVariable/*!*/ dim2 = new TestVariable("Y");
      IVariable/*!*/ dim3 = new TestVariable("Z");
      Contract.Assert(dim1 != null);
      Contract.Assert(dim2 != null);
      Contract.Assert(dim3 != null);

      FrameElement s1 = new FrameElement();
      s1.AddCoordinate(dim1, Rational.ONE);
      s1.AddCoordinate(dim2, Rational.MINUS_ONE);
      s1.AddCoordinate(dim3, Rational.ZERO);
      FrameElement s2 = new FrameElement();
      s2.AddCoordinate(dim1, Rational.MINUS_ONE);
      s2.AddCoordinate(dim2, Rational.ONE);
      s2.AddCoordinate(dim3, Rational.ZERO);
      FrameElement r1 = new FrameElement();
      r1.AddCoordinate(dim1, Rational.ZERO);
      r1.AddCoordinate(dim2, Rational.ZERO);
      r1.AddCoordinate(dim3, Rational.ONE);
      FrameElement d1 = new FrameElement();
      d1.AddCoordinate(dim1, Rational.ONE);
      d1.AddCoordinate(dim2, Rational.ONE);
      d1.AddCoordinate(dim3, Rational.ZERO);

      // create lcs from frame -- cf. Cousot/Halbwachs 1978, section 3.3.1.1
      LinearConstraintSystem lcs = new LinearConstraintSystem(s1);
      lcs.Dump();

      lcs.AddVertex(s2);
      lcs.Dump();

      lcs.AddRay(r1);
      lcs.Dump();

      lcs.AddLine(d1);
      lcs.Dump();

      lcs.SimplifyConstraints();
      lcs.Dump();

#if LATER
      lcs.GenerateFrameFromConstraints(); // should give us back the original frame...
#endif
      Console.WriteLine("IsSubset? {0}", lcs.IsSubset(lcs.Clone()));
      lcs.Dump();
    }

    /// <summary>
    /// Tests the example in section 3.4.3 of Cousot and Halbwachs.
    /// </summary>
    public static void RunValidationB() {
      IVariable/*!*/ X = new TestVariable("X");
      IVariable/*!*/ Y = new TestVariable("Y");
      IVariable/*!*/ Z = new TestVariable("Z");
      Contract.Assert(X != null);
      Contract.Assert(Y != null);
      Contract.Assert(Z != null);
      ArrayList /*LinearConstraint*/ cs = new ArrayList /*LinearConstraint*/ ();

      LinearConstraint c = new LinearConstraint(LinearConstraint.ConstraintRelation.LE);
      c.SetCoefficient(X, Rational.MINUS_ONE);
      c.SetCoefficient(Y, Rational.ONE);
      c.SetCoefficient(Z, Rational.MINUS_ONE);
      c.rhs = Rational.ZERO;
      cs.Add(c);

      c = new LinearConstraint(LinearConstraint.ConstraintRelation.LE);
      c.SetCoefficient(X, Rational.MINUS_ONE);
      c.rhs = Rational.MINUS_ONE;
      cs.Add(c);

      c = new LinearConstraint(LinearConstraint.ConstraintRelation.LE);
      c.SetCoefficient(X, Rational.MINUS_ONE);
      c.SetCoefficient(Y, Rational.MINUS_ONE);
      c.SetCoefficient(Z, Rational.ONE);
      c.rhs = Rational.ZERO;
      cs.Add(c);

      c = new LinearConstraint(LinearConstraint.ConstraintRelation.LE);
      c.SetCoefficient(Y, Rational.MINUS_ONE);
      c.SetCoefficient(Z, Rational.ONE);
      c.rhs = Rational.FromInt(3);
      cs.Add(c);

      LinearConstraintSystem lcs = new LinearConstraintSystem(cs);
      Console.WriteLine("==================== The final linear constraint system ====================");
      lcs.Dump();
    }

    public static void RunValidationC() {
      // Run the example in section 3.4.3 of Cousot and Halbwachs backwards, that is, from
      // from to constraints.
      IVariable/*!*/ dim1 = new TestVariable("X");
      IVariable/*!*/ dim2 = new TestVariable("Y");
      IVariable/*!*/ dim3 = new TestVariable("Z");
      Contract.Assert(dim1 != null);
      Contract.Assert(dim2 != null);
      Contract.Assert(dim3 != null);

      FrameElement s0 = new FrameElement();
      s0.AddCoordinate(dim1, Rational.ONE);
      s0.AddCoordinate(dim2, Rational.FromInts(1, 2));
      s0.AddCoordinate(dim3, Rational.FromInts(-1, 2));

      FrameElement s1 = new FrameElement();
      s1.AddCoordinate(dim1, Rational.ONE);
      s1.AddCoordinate(dim2, Rational.FromInts(-1, 2));
      s1.AddCoordinate(dim3, Rational.FromInts(1, 2));

      FrameElement s2 = new FrameElement();
      s2.AddCoordinate(dim1, Rational.FromInt(3));
      s2.AddCoordinate(dim2, Rational.FromInts(-3, 2));
      s2.AddCoordinate(dim3, Rational.FromInts(3, 2));

      FrameElement r0 = new FrameElement();
      r0.AddCoordinate(dim1, Rational.ONE);
      r0.AddCoordinate(dim2, Rational.FromInts(1, 2));
      r0.AddCoordinate(dim3, Rational.FromInts(-1, 2));

      FrameElement r1 = new FrameElement();
      r1.AddCoordinate(dim1, Rational.ONE);
      r1.AddCoordinate(dim2, Rational.ZERO);
      r1.AddCoordinate(dim3, Rational.ZERO);

      FrameElement d0 = new FrameElement();
      d0.AddCoordinate(dim1, Rational.ZERO);
      d0.AddCoordinate(dim2, Rational.ONE);
      d0.AddCoordinate(dim3, Rational.ONE);

      LinearConstraintSystem lcs = new LinearConstraintSystem(s0);
      lcs.Dump();

      lcs.AddVertex(s1);
      lcs.Dump();

      lcs.AddVertex(s2);
      lcs.Dump();

      lcs.AddRay(r0);
      lcs.Dump();

      lcs.AddRay(r1);
      lcs.Dump();

      lcs.AddLine(d0);
      lcs.Dump();

      lcs.SimplifyConstraints();
      lcs.Dump();

#if LATER
      lcs.GenerateFrameFromConstraints(); // should give us back the original frame...
#endif
    }
  }
}