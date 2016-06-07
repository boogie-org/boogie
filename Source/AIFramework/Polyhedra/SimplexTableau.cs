//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework {
  using System.Collections;
  using System;
  using System.Diagnostics.Contracts;
  using Microsoft.Basetypes;
  using IMutableSet = Microsoft.Boogie.GSet<object>;
  using HashSet = Microsoft.Boogie.GSet<object>;


  /// <summary>
  /// Used by LinearConstraintSystem.GenerateFrameFromConstraints.
  /// </summary>
  public class SimplexTableau {
    readonly int rows;
    readonly int columns;
    readonly Rational[,]/*!*/ m;

    readonly int numInitialVars;
    readonly int numSlackVars;
    readonly int rhsColumn;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(m != null);
      Contract.Invariant(inBasis != null);
      Contract.Invariant(basisColumns != null);
    }

    readonly ArrayList /*IVariable!*//*!*/ dims;
    readonly int[]/*!*/ basisColumns;
    readonly int[]/*!*/ inBasis;
    bool constructionDone = false;

    void CheckInvariant() {
      Contract.Assert(rows == m.GetLength(0));
      Contract.Assert(1 <= columns && columns == m.GetLength(1));
      Contract.Assert(0 <= numInitialVars);
      Contract.Assert(0 <= numSlackVars && numSlackVars <= rows);
      Contract.Assert(numInitialVars + numSlackVars + 1 == columns);
      Contract.Assert(rhsColumn == columns - 1);
      Contract.Assert(dims.Count == numInitialVars);
      Contract.Assert(basisColumns.Length == rows);
      Contract.Assert(inBasis.Length == numInitialVars + numSlackVars);

      bool[] b = new bool[numInitialVars + numSlackVars];
      int numColumnsInBasis = 0;
      int numUninitializedRowInfo = 0;
      for (int i = 0; i < rows; i++) {
        int c = basisColumns[i];
        if (c == rhsColumn) {
          // all coefficients in this row are 0 (but the right-hand side may be non-0)
          for (int j = 0; j < rhsColumn; j++) {
            Contract.Assert(m[i, j].IsZero);
          }
          numColumnsInBasis++;
        } else if (c == -1) {
          Contract.Assert(!constructionDone);
          numUninitializedRowInfo++;
        } else {
          // basis column is a column
          Contract.Assert(0 <= c && c < numInitialVars + numSlackVars);
          // basis column is unique
          Contract.Assert(!b[c]);
          b[c] = true;
          // column is marked as being in basis
          Contract.Assert(inBasis[c] == i);
          // basis column really is a basis column
          for (int j = 0; j < rows; j++) {
            if (j == i) {
              Contract.Assert(m[j, c].HasValue(1));// == (Rational)new Rational(1)));
            } else {
              Contract.Assert(m[j, c].IsZero);
            }
          }
        }
      }
      // no other columns are marked as being in basis
      foreach (int i in inBasis) {
        if (0 <= i) {
          Contract.Assert(i < rows);
          numColumnsInBasis++;
        } else {
          Contract.Assert(i == -1);
        }
      }
      Contract.Assert(rows - numUninitializedRowInfo <= numColumnsInBasis && numColumnsInBasis <= rows);
      Contract.Assert(!constructionDone || numUninitializedRowInfo == 0);
    }

    /// <summary>
    /// Constructs a matrix that represents the constraints "constraints", adding slack
    /// variables for the inequalities among "constraints".  Puts the matrix in canonical
    /// form.
    /// </summary>
    /// <param name="constraints"></param>
    [NotDelayed]
    public SimplexTableau(ArrayList /*LinearConstraint*//*!*/ constraints) {
      Contract.Requires(constraints != null);
#if DEBUG_PRINT
            Console.WriteLine("DEBUG: SimplexTableau constructor called with:");
            foreach (LinearConstraint lc in constraints)
            {
              Console.WriteLine("  {0}", lc);
            }
#endif
      // Note:  This implementation is not particularly efficient, but it'll do for now.

      ArrayList dims = this.dims = new ArrayList /*IVariable!*/ ();
      int slacks = 0;
      foreach (LinearConstraint/*!*/ cc in constraints) {
        Contract.Assert(cc != null);
        foreach (IVariable/*!*/ dim in cc.coefficients.Keys) {
          Contract.Assert(dim != null);
          if (!dims.Contains(dim)) {
            dims.Add(dim);
          }
        }
        if (cc.Relation == LinearConstraint.ConstraintRelation.LE) {
          slacks++;
        }
      }

      int numInitialVars = this.numInitialVars = dims.Count;
      int numSlackVars = this.numSlackVars = slacks;
      int rows = this.rows = constraints.Count;
      int columns = this.columns = numInitialVars + numSlackVars + 1;
      this.m = new Rational[rows, columns];
      this.rhsColumn = columns - 1;
      this.basisColumns = new int[rows];
      this.inBasis = new int[columns - 1];

      //:base();

      for (int i = 0; i < inBasis.Length; i++) {
        inBasis[i] = -1;
      }

      // Fill in the matrix
      int r = 0;
      int iSlack = 0;
      foreach (LinearConstraint/*!*/ cc in constraints) {
        Contract.Assert(cc != null);
        for (int i = 0; i < dims.Count; i++) {
          m[r, i] = cc[(IVariable)cce.NonNull(dims[i])];
        }
        if (cc.Relation == LinearConstraint.ConstraintRelation.LE) {
          m[r, numInitialVars + iSlack] = Rational.ONE;
          basisColumns[r] = numInitialVars + iSlack;
          inBasis[numInitialVars + iSlack] = r;
          iSlack++;
        } else {
          basisColumns[r] = -1;  // special value to communicate to Pivot that basis column i hasn't been set up yet
        }
        m[r, rhsColumn] = cc.rhs;
        r++;
      }
      Contract.Assert(r == constraints.Count);
      Contract.Assert(iSlack == numSlackVars);
#if DEBUG_PRINT
            Console.WriteLine("DEBUG: Intermediate tableau state in SimplexTableau constructor:");
            Dump();
#endif

      // Go through the rows with uninitialized basis columns.  These correspond to equality constraints.
      // For each one, find an initial variable (non-slack variable) whose column we can make the basis
      // column of the row.
      for (int i = 0; i < rows; i++) {
        if (basisColumns[i] != -1) {
          continue;
        }
        // Find a non-0 column in row i that we can make a basis column.  Since rows corresponding
        // to equality constraints don't have slack variables and since the pivot operations performed
        // by iterations of this loop don't introduce any non-0 coefficients in the slack-variable
        // columns of these rows, we only need to look through the columns corresponding to initial
        // variables.
        for (int j = 0; j < numInitialVars; j++) {
          if (m[i, j].IsNonZero) {
#if DEBUG_PRINT
                            Console.WriteLine("-- About to Pivot({0},{1})", i, j);
#endif
            Contract.Assert(inBasis[j] == -1);
            Pivot(i, j);
#if DEBUG_PRINT
                            Console.WriteLine("Tableau after Pivot:");
                            Dump();
#endif
            goto SET_UP_NEXT_INBASIS_COLUMN;
          }
        }
        // Check the assertion in the comment above, that is, that columns corresponding to slack variables
        // are 0 in this row.
        for (int j = numInitialVars; j < rhsColumn; j++) {
          Contract.Assert(m[i, j].IsZero);
        }
        // There is no column in this row that we can put into basis.
        basisColumns[i] = rhsColumn;
      SET_UP_NEXT_INBASIS_COLUMN: {
        }
      }

      constructionDone = true;
      CheckInvariant();
    }

    public IMutableSet/*!*/ /*IVariable!*/ GetDimensions() {
      Contract.Ensures(Contract.Result<IMutableSet>() != null);
      HashSet /*IVariable!*/ z = new HashSet /*IVariable!*/ ();
      foreach (IVariable/*!*/ dim in dims) {
        Contract.Assert(dim != null);
        z.Add(dim);
      }
      return z;
    }

    public Rational this[int r, int c] {
      get {
        return m[r, c];
      }
      set {
        m[r, c] = value;
      }
    }

    /// <summary>
    /// Applies the Pivot Operation on row "r" and column "c".
    /// 
    /// This method can be called when !constructionDone, that is, at a time when not all basis
    /// columns have been set up (indicated by -1 in basisColumns).  This method helps set up
    /// those basis columns.
    /// 
    /// The return value is an undo record that can be used with UnPivot.
    /// </summary>
    /// <param name="r"></param>
    /// <param name="c"></param>
    public Rational[]/*!*/ Pivot(int r, int c) {
      Contract.Ensures(Contract.Result<Rational[]>() != null);
      Contract.Assert(0 <= r && r < rows);
      Contract.Assert(0 <= c && c < columns - 1);
      Contract.Assert(m[r, c].IsNonZero);
      Contract.Assert(inBasis[c] == -1);  // follows from invariant and m[r,c] != 0
      Contract.Assert(basisColumns[r] != rhsColumn);  // follows from invariant and m[r,c] != 0

      Rational[] undo = new Rational[rows + 1];
      for (int i = 0; i < rows; i++) {
        undo[i] = m[i, c];
      }

      // scale the pivot row
      Rational q = m[r, c];
      if (q != Rational.ONE) {
        for (int j = 0; j < columns; j++) {
          m[r, j] /= q;
        }
      }

      // subtract a multiple of the pivot row from all other rows
      for (int i = 0; i < rows; i++) {
        if (i != r) {
          q = m[i, c];
          if (q.IsNonZero) {
            for (int j = 0; j < columns; j++) {
              m[i, j] -= q * m[r, j];
            }
          }
        }
      }

      // update basis information
      int prevCol = basisColumns[r];
      undo[rows] = Rational.FromInt(prevCol);
      basisColumns[r] = c;
      if (prevCol != -1) {
        inBasis[prevCol] = -1;
      }
      inBasis[c] = r;

      return undo;
    }

    /// <summary>
    /// If the last operation applied to the tableau was:
    ///   undo = Pivot(i,j);
    /// then UnPivot(i, j, undo) undoes the pivot operation.
    /// Note:  This operation is not supported for any call to Pivot before constructionDone
    /// is set to true.
    /// </summary>
    /// <param name="r"></param>
    /// <param name="c"></param>
    /// <param name="undo"></param>
    void UnPivot(int r, int c, Rational[]/*!*/ undo) {
      Contract.Requires(undo != null);
      Contract.Assert(0 <= r && r < rows);
      Contract.Assert(0 <= c && c < columns - 1);
      Contract.Assert(m[r, c].HasValue(1));
      Contract.Assert(undo.Length == rows + 1);

      // add a multiple of the pivot row to all other rows
      for (int i = 0; i < rows; i++) {
        if (i != r) {
          Rational q = undo[i];
          if (q.IsNonZero) {
            for (int j = 0; j < columns; j++) {
              m[i, j] += q * m[r, j];
            }
          }
        }
      }

      // scale the pivot row
      Rational p = undo[r];
      for (int j = 0; j < columns; j++) {
        m[r, j] *= p;
      }

      // update basis information
      int prevCol = undo[rows].AsInteger;
      Contract.Assert(prevCol != -1);
      basisColumns[r] = prevCol;
      inBasis[c] = -1;
      inBasis[prevCol] = r;
    }

    /// <summary>
    /// Returns true iff the current basis of the system of constraints modeled by the simplex tableau
    /// is feasible.  May have a side effect of performing a number of pivot operations on the tableau,
    /// but any such pivot operation will be in the columns of slack variables (that is, this routine
    /// does not change the set of initial-variable columns in basis).
    /// 
    /// CAVEAT: I have no particular reason to believe that the algorithm used here will terminate. --KRML
    /// </summary>
    /// <returns></returns>
    public bool IsFeasibleBasis {
      get {
        // while there is a slack variable in basis whose row has a negative right-hand side
        while (true) {
          bool feasibleBasis = true;
          for (int c = numInitialVars; c < rhsColumn; c++) {
            int k = inBasis[c];
            if (0 <= k && k < rhsColumn && m[k, rhsColumn].IsNegative) {
              Contract.Assert(m[k, c].HasValue(1));  // c is in basis
              // Try to pivot on a different slack variable in this row
              for (int i = numInitialVars; i < rhsColumn; i++) {
                if (m[k, i].IsNegative) {
                  Contract.Assert(c != i);  // c is in basis, so m[k,c]==1, which is not negative
                  Pivot(k, i);
#if DEBUG_PRINT
                  Console.WriteLine("Tableau after Pivot operation on ({0},{1}) in IsFeasibleBasis:", k, i);
                  Dump();
#endif
                  Contract.Assert(inBasis[c] == -1);
                  Contract.Assert(inBasis[i] == k);
                  Contract.Assert(m[k, rhsColumn].IsNonNegative);
                  goto START_ANEW;
                }
              }
              feasibleBasis = false;
            }
          }
          return feasibleBasis;
        START_ANEW:
          ;
        }
      }
    }

    /// <summary>
    /// Whether or not all initial variables (the non-slack variables) are in basis)
    /// </summary>
    public bool AllInitialVarsInBasis {
      get {
        for (int i = 0; i < numInitialVars; i++) {
          if (inBasis[i] == -1) {
            return false;
          }
        }
        return true;
      }
    }

    /// <summary>
    /// Adds as many initial variables as possible to the basis.
    /// </summary>
    /// <returns></returns>
    public void AddInitialVarsToBasis() {
      // while there exists an initial variable not in the basis and not satisfying
      // condition 3.4.2.2 in Cousot and Halbwachs, perform a pivot operation
      while (true) {
        for (int i = 0; i < numInitialVars; i++) {
          if (inBasis[i] == -1) {
            // initial variable i is not in the basis
            for (int j = 0; j < rows; j++) {
              if (m[j, i].IsNonZero) {
                int k = basisColumns[j];
                if (numInitialVars <= k && k < rhsColumn) {
                  // slack variable k is in basis for row j
                  Pivot(j, i);
                  Contract.Assert(inBasis[k] == -1);
                  Contract.Assert(inBasis[i] == j && basisColumns[j] == i);
                  goto START_ANEW;
                }
              }
            }
          }
        }
        // No more initial variables can be moved into basis.
        return;
      START_ANEW: {
        }
      }
    }

    /// <summary>
    /// Adds to "lines" the lines implied by initial-variable columns not in basis
    /// (see section 3.4.2 of Cousot and Halbwachs), and adds to "constraints" the
    /// constraints to exclude those lines (see step 4.2 of section 3.4.3 of
    /// Cousot and Halbwachs).
    /// </summary>
    /// <param name="lines"></param>
    /// <param name="constraints"></param>
    public void ProduceLines(ArrayList /*FrameElement*//*!*/ lines, ArrayList /*LinearConstraint*//*!*/ constraints) {
      Contract.Requires(constraints != null);
      Contract.Requires(lines != null);
      // for every initial variable not in basis
      for (int i0 = 0; i0 < numInitialVars; i0++) {
        if (inBasis[i0] == -1) {
          FrameElement fe = new FrameElement();
          LinearConstraint lc = new LinearConstraint(LinearConstraint.ConstraintRelation.EQ);
          for (int i = 0; i < numInitialVars; i++) {
            if (i == i0) {
              fe.AddCoordinate((IVariable)cce.NonNull(dims[i]), Rational.ONE);
              lc.SetCoefficient((IVariable)cce.NonNull(dims[i]), Rational.ONE);
            } else if (inBasis[i] != -1) {
              // i is a basis column
              Contract.Assert(m[inBasis[i], i].HasValue(1));
              Rational val = -m[inBasis[i], i0];
              fe.AddCoordinate((IVariable)cce.NonNull(dims[i]), val);
              lc.SetCoefficient((IVariable)cce.NonNull(dims[i]), val);
            }
          }
          lines.Add(fe);
          constraints.Add(lc);
        }
      }
    }

    /// <summary>
    /// From a feasible point where all initial variables are in the basis, traverses
    /// all feasible bases containing all initial variables.  For each such basis, adds
    /// the vertices to "vertices" and adds to "rays" the extreme rays.  See step 4.2
    /// in section 3.4.3 of Cousot and Halbwachs.
    /// A more efficient algorithm is found in the paper "An algorithm for
    /// determining all extreme points of a convex polytope" by N. E. Dyer and L. G. Proll,
    /// Mathematical Programming, 12, 1977.
    /// Assumes that the tableau is in a state where all initial variables are in the basis.
    /// This method has no net effect on the tableau.
    /// Note: Duplicate vertices and rays may be added.
    /// </summary>
    /// <param name="vertices"></param>
    /// <param name="rays"></param>
    public void TraverseVertices(ArrayList/*!*/ /*FrameElement*/ vertices, ArrayList/*!*/ /*FrameElement*/ rays) {
      Contract.Requires(vertices != null);
      Contract.Requires(rays != null);
      ArrayList /*bool[]*/ basesSeenSoFar = new ArrayList /*bool[]*/ ();
      TraverseBases(basesSeenSoFar, vertices, rays);
    }

    /// <summary>
    /// Worker method of TraverseVertices.
    /// This method has no net effect on the tableau.
    /// </summary>
    /// <param name="basesSeenSoFar"></param>
    /// <param name="vertices"></param>
    /// <param name="rays"></param>
    void TraverseBases(ArrayList /*bool[]*//*!*/ basesSeenSoFar, ArrayList /*FrameElement*//*!*/ vertices, ArrayList /*FrameElement*//*!*/ rays) {
      Contract.Requires(rays != null);
      Contract.Requires(vertices != null);
      Contract.Requires(basesSeenSoFar != null);
      CheckInvariant();

      bool[] thisBasis = new bool[numSlackVars];
      for (int i = numInitialVars; i < rhsColumn; i++) {
        if (inBasis[i] != -1) {
          thisBasis[i - numInitialVars] = true;
        }
      }
      foreach (bool[]/*!*/ basis in basesSeenSoFar) {
        Contract.Assert(basis != null);
        Contract.Assert(basis.Length == numSlackVars);
        for (int i = 0; i < numSlackVars; i++) {
          if (basis[i] != thisBasis[i]) {
            goto COMPARE_WITH_NEXT_BASIS;
          }
        }
        // thisBasis and basis are the same--that is, basisColumns has been visited before--so
        // we don't traverse anything from here
        return;
      COMPARE_WITH_NEXT_BASIS: {
        }
      }
      // basisColumns has not been seen before; record thisBasis and continue with the traversal here
      basesSeenSoFar.Add(thisBasis);

#if DEBUG_PRINT
      Console.Write("TraverseBases, new basis:  ");
      foreach (bool t in thisBasis) {
        Console.Write("{0}", t ? "*" : ".");
      }
      Console.WriteLine();
      Dump();
#endif
      // Add vertex
      FrameElement v = new FrameElement();
      for (int i = 0; i < rows; i++) {
        int j = basisColumns[i];
        if (j < numInitialVars) {
          v.AddCoordinate((IVariable)cce.NonNull(dims[j]), m[i, rhsColumn]);
        }
      }
#if DEBUG_PRINT
      Console.WriteLine("  Adding vertex: {0}", v);
#endif
      vertices.Add(v);

      // Add rays.  Traverse all columns corresponding to slack variables that
      // are not in basis (see second bullet of section 3.4.2 of Cousot and Halbwachs).
      for (int i0 = numInitialVars; i0 < rhsColumn; i0++) {
        if (inBasis[i0] != -1) {
          // skip those slack-variable columns that are in basis
          continue;
        }
        // check if slack-variable, non-basis column i corresponds to an extreme ray
        for (int row = 0; row < rows; row++) {
          if (m[row, i0].IsPositive) {
            for (int k = numInitialVars; k < rhsColumn; k++) {
              if (inBasis[k] != -1 && m[row, k].IsNonZero) {
                // does not correspond to an extreme ray
                goto CHECK_NEXT_SLACK_VAR;
              }
            }
          }
        }
        // corresponds to an extreme ray
        FrameElement ray = new FrameElement();
        for (int i = 0; i < numInitialVars; i++) {
          int j0 = inBasis[i];
          Rational val = -m[j0, i0];
          ray.AddCoordinate((IVariable)cce.NonNull(dims[i]), val);
        }
#if DEBUG_PRINT
        Console.WriteLine("  Adding ray: {0}", ray);
#endif
        rays.Add(ray);
      CHECK_NEXT_SLACK_VAR: {
        }
      }

      // Continue traversal
      for (int i = numInitialVars; i < rhsColumn; i++) {
        int j = inBasis[i];
        if (j != -1) {
          // try moving i out of basis and some other slack-variable column into basis
          for (int k = numInitialVars; k < rhsColumn; k++) {
            if (inBasis[k] == -1 && m[j, k].IsPositive) {
              Rational[] undo = Pivot(j, k);
              // check if the new basis is feasible
              for (int p = 0; p < rows; p++) {
                int c = basisColumns[p];
                if (numInitialVars <= c && c < rhsColumn && m[p, rhsColumn].IsNegative) {
                  // not feasible
                  goto AFTER_TRAVERSE;
                }
              }
              TraverseBases(basesSeenSoFar, vertices, rays);
            AFTER_TRAVERSE:
              UnPivot(j, k, undo);
            }
          }
        }
      }
    }

    public void Dump() {
      // names
      Console.Write("      ");
      for (int i = 0; i < numInitialVars; i++) {
        Console.Write("  {0,4}   ", dims[i]);
      }
      Console.WriteLine();
      // numbers
      Console.Write("      ");
      for (int i = 0; i < columns; i++) {
        if (i == numInitialVars || i == rhsColumn) {
          Console.Write("|");
        }
        Console.Write("  {0,4}", i);
        if (i < rhsColumn && inBasis[i] != -1) {
          Console.Write("*  ");
          Contract.Assert(basisColumns[inBasis[i]] == i);
        } else {
          Console.Write("   ");
        }
      }
      Console.WriteLine();
      // line
      Console.Write("      ");
      for (int i = 0; i < columns; i++) {
        if (i == numInitialVars || i == rhsColumn) {
          Console.Write("+");
        }
        Console.Write("---------");
      }
      Console.WriteLine();

      for (int j = 0; j < rows; j++) {
        Console.Write("{0,4}: ", basisColumns[j]);
        for (int i = 0; i < columns; i++) {
          if (i == numInitialVars || i == rhsColumn) {
            Console.Write("|");
          }
          Console.Write("  {0,4:n1}   ", m[j, i]);
        }
        Console.WriteLine();
      }
    }
  }
}
