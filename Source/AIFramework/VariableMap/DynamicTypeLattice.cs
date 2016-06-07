//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework {
  using System.Collections;
  using System.Diagnostics;
  //using System.Compiler.Analysis;
  //using Microsoft.SpecSharp.Collections;
  using System.Diagnostics.Contracts;

  /// <summary>
  /// Represents information about the dynamic type of a variable.  In particular, for a
  /// variable "v", represents either Bottom, "typeof(v)==T" for some type T, or a set
  /// of constraints "typeof(v) subtype of T_i for some number of T_i's.
  /// </summary>
  public class DynamicTypeLattice : MicroLattice {
    enum What {
      Bottom,
      Exact,
      Bounds
    }

    private class Elt : Element {
      // Representation:
      // - Bottom is represented by:  what==What.Bottom
      // - An exact type T is represented by: what==What.Exact && ty==T
      // - A set of type constraints T0, T1, T2, ..., T{n-1} is represented by:
      //    -- if n==0:  what==What.Bounds && ty==null && manyBounds==null
      //    -- if n==1:  what==What.Bounds && ty==T0 && manyBounds==null
      //    -- if n>=2:  what==What.Bounds && ty==null &&
      //                 manyBounds!=null && manyBounds.Length==n &&
      //                 manyBounds[0]==T0 && manyBounds[1]==T1 && ... && manyBounds[n-1]==T{n-1}
      //   The reason for keeping the one-and-only bound in "ty" in case n==1 is to try
      //   to prevent the need for allocating a whole array of bounds, since 1 bound is
      //   bound to be common.
      // In the representation, there are no redundant bounds in manyBounds.
      // It is assumed that the types can can occur as exact bounds form a single-inheritance
      // hierarchy.  That is, if T0 and T1 are types that can occur as exact types, then
      // there is no v such that typeof(v) is a subtype of both T0 and T1, unless T0 and T1 are
      // the same type.
      public readonly What what;
      public readonly IExpr ty;
      [Rep]
      public readonly IExpr[] manyBounds;
      [ContractInvariantMethod]
      void ObjectInvariant() {

        Contract.Invariant(what != What.Bottom || ty == null && manyBounds == null);
        Contract.Invariant(manyBounds == null || what == What.Bounds);
        Contract.Invariant(manyBounds == null || Contract.ForAll(0, manyBounds.Length, i => manyBounds[i] != null));
      }
      public Elt(What what, IExpr ty) {
        Contract.Requires(what != What.Bottom || ty == null);
        Contract.Requires(what != What.Exact || ty != null);
        this.what = what;
        this.ty = ty;
        this.manyBounds = null;
      }

      public Elt(IExpr[]/*!*/ bounds) {
        Contract.Requires(bounds != null);
        Contract.Requires(Contract.ForAll(0, bounds.Length, i => bounds[i] != null));
        this.what = What.Bounds;
        if (bounds.Length == 0) {
          this.ty = null;
          this.manyBounds = null;
        } else if (bounds.Length == 1) {
          this.ty = bounds[0];
          this.manyBounds = null;
        } else {
          this.ty = null;
          this.manyBounds = bounds;
        }
      }

      /// <summary>
      /// Constructs an Elt with "n" bounds, namely the n non-null values of the "bounds" list.
      /// </summary>
      [NotDelayed]
      public Elt(ArrayList /*IExpr*//*!*/ bounds, int n) {
        Contract.Requires(bounds != null);
        Contract.Requires(0 <= n && n <= bounds.Count);
        this.what = What.Bounds;
        if (n > 1) {
          this.manyBounds = new IExpr[n];
        }
        int k = 0;
        foreach (IExpr bound in bounds) {
          if (bound != null) {
            Contract.Assert(k != n);
            if (n == 1) {
              Contract.Assert(this.ty == null);
              this.ty = bound;
            } else {
              Contract.Assume(manyBounds != null);
              manyBounds[k] = bound;
            }
            k++;
          }
        }
        Contract.Assert(k == n);
      }

      public int BoundsCount {
        get {
          Contract.Ensures(0 <= Contract.Result<int>());
          if (manyBounds != null) {
            return manyBounds.Length;
          } else if (ty != null) {
            return 1;
          } else {
            return 0;
          }
        }
      }

      [Pure]
      public override System.Collections.Generic.ICollection<IVariable/*!*/>/*!*/ FreeVariables() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<System.Collections.Generic.ICollection<IVariable>>()));
        return cce.NonNull(new System.Collections.Generic.List<IVariable/*!*/>()).AsReadOnly();
      }

      public override Element/*!*/ Clone() {
        Contract.Ensures(Contract.Result<Element>() != null);
        if (this.manyBounds != null)
          return new Elt(this.manyBounds);
        else
          return new Elt(this.what, this.ty);
      }
    }

    readonly ITypeExprFactory/*!*/ factory;
    readonly IPropExprFactory/*!*/ propFactory;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(factory != null);
      Contract.Invariant(propFactory != null);
    }


    public DynamicTypeLattice(ITypeExprFactory/*!*/ factory, IPropExprFactory/*!*/ propFactory) {
      Contract.Requires(propFactory != null);
      Contract.Requires(factory != null);
      this.factory = factory;
      this.propFactory = propFactory;
      // base();
    }

    public override Element/*!*/ Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(What.Bounds, null);
      }
    }

    public override Element/*!*/ Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(What.Bottom, null);
      }
    }

    public override bool IsTop(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      return e.what == What.Bounds && e.ty == null && e.manyBounds == null;
    }

    public override bool IsBottom(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      return e.what == What.Bottom;
    }

    public override Element/*!*/ NontrivialJoin(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;
      Contract.Assert(a.what != What.Bottom && b.what != What.Bottom);
      if (a.what == What.Exact && b.what == What.Exact) {
        Contract.Assert(a.ty != null && b.ty != null);
        if (factory.IsTypeEqual(a.ty, b.ty)) {
          return a;
        } else {
          return new Elt(What.Bounds, factory.JoinTypes(a.ty, b.ty));
        }
      }

      // The result is going to be a Bounds, since at least one of the operands is a Bounds.
      Contract.Assert(1 <= a.BoundsCount && 1 <= b.BoundsCount);  // a preconditions is that neither operand is Top
      int n = a.BoundsCount + b.BoundsCount;

      // Special case:  a and b each has exactly one bound
      if (n == 2) {
        Contract.Assert(a.ty != null && b.ty != null);
        IExpr join = factory.JoinTypes(a.ty, b.ty);
        Contract.Assert(join != null);
        if (join == a.ty && a.what == What.Bounds) {
          return a;
        } else if (join == b.ty && b.what == What.Bounds) {
          return b;
        } else {
          return new Elt(What.Bounds, join);
        }
      }

      // General case
      ArrayList /*IExpr*/ allBounds = new ArrayList /*IExpr*/ (n);  // final size
      ArrayList /*IExpr!*/ result = new ArrayList /*IExpr!*/ (n);  // a guess at the size, but could be as big as size(a)*size(b)
      if (a.ty != null) {
        allBounds.Add(a.ty);
      } else {
        allBounds.AddRange(cce.NonNull(a.manyBounds));
      }
      int bStart = allBounds.Count;
      if (b.ty != null) {
        allBounds.Add(b.ty);
      } else {
        allBounds.AddRange(cce.NonNull(b.manyBounds));
      }
      // compute the join of each pair, putting non-redundant joins into "result"
      for (int i = 0; i < bStart; i++) {
        IExpr/*!*/ aBound = cce.NonNull((IExpr/*!*/)allBounds[i]);
        for (int j = bStart; j < allBounds.Count; j++) {
          IExpr/*!*/ bBound = (IExpr/*!*/)cce.NonNull(allBounds[j]);

          IExpr/*!*/ join = factory.JoinTypes(aBound, bBound);
          Contract.Assert(join != null);

          int k = 0;
          while (k < result.Count) {
            IExpr/*!*/ r = (IExpr/*!*/)cce.NonNull(result[k]);
            if (factory.IsSubType(join, r)) {
              // "join" is more restrictive than a bound already placed in "result",
              // so toss out "join" and compute the join of the next pair
              goto NEXT_PAIR;
            } else if (factory.IsSubType(r, join)) {
              // "join" is less restrictive than a bound already placed in "result",
              // so toss out that old bound
              result.RemoveAt(k);
            } else {
              k++;
            }
          }
          result.Add(join);
        NEXT_PAIR: {
          }
        }
      }
      return new Elt(result, result.Count);
    }


    public override Element/*!*/ NontrivialMeet(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;
      Contract.Assert(a.what != What.Bottom && b.what != What.Bottom);

      if (a.what == What.Exact && b.what == What.Exact) {
        Contract.Assert(a.ty != null && b.ty != null);
        if (factory.IsTypeEqual(a.ty, b.ty)) {
          return a;
        } else {
          return Bottom;
        }

      } else if (a.what == What.Exact || b.what == What.Exact) {
        // One is Bounds, the other Exact.  Make b be the Bounds one.
        if (a.what == What.Bounds) {
          Elt tmp = a;
          a = b;
          b = tmp;
        }
        Contract.Assert(a.what == What.Exact && b.what == What.Bounds);
        // Check the exact type against all bounds.  If the exact type is more restrictive
        // than all bounds, then return it.  If some bound is not met by the exact type, return
        // bottom.
        Contract.Assert(a.ty != null);
        if (b.ty != null && !factory.IsSubType(a.ty, b.ty)) {
          return Bottom;
        }
        if (b.manyBounds != null) {
          foreach (IExpr/*!*/ bound in b.manyBounds) {
            Contract.Assert(bound != null);
            if (!factory.IsSubType(a.ty, bound)) {
              return Bottom;
            }
          }
        }
        return a;
      } else {
        // Both operands are Bounds.
        Contract.Assert(a.what == What.Bounds && b.what == What.Bounds);

        // Take all the bounds, but prune those bounds that follow from others.
        Contract.Assert(1 <= a.BoundsCount && 1 <= b.BoundsCount);  // a preconditions is that neither operand is Top
        int n = a.BoundsCount + b.BoundsCount;
        // Special case:  a and b each has exactly one bound
        if (n == 2) {
          Contract.Assert(a.ty != null && b.ty != null);
          if (factory.IsSubType(a.ty, b.ty)) {
            // a is more restrictive
            return a;
          } else if (factory.IsSubType(b.ty, a.ty)) {
            // b is more restrictive
            return b;
          } else {
            IExpr[]/*!*/ bounds = new IExpr[2];
            bounds[0] = a.ty;
            bounds[1] = b.ty;
            return new Elt(bounds);
          }
        }

        // General case
        ArrayList /*IExpr*/ allBounds = new ArrayList /*IExpr*/ (n);
        if (a.ty != null) {
          allBounds.Add(a.ty);
        } else {
          allBounds.AddRange(cce.NonNull(a.manyBounds));
        }
        int bStart = allBounds.Count;
        if (b.ty != null) {
          allBounds.Add(b.ty);
        } else {
          allBounds.AddRange(cce.NonNull(b.manyBounds));
        }
        for (int i = 0; i < bStart; i++) {
          IExpr/*!*/ aBound = cce.NonNull((IExpr)allBounds[i]);
          for (int j = bStart; j < allBounds.Count; j++) {
            IExpr bBound = (IExpr/*! Wouldn't the non-null typing in the original Spec# code had made bBound never null, 
                                              * thus negating the need for the continue statement?*/
                                                                                        )allBounds[j];
            if (bBound == null) {
              continue;
            } else if (factory.IsSubType(aBound, bBound)) {
              // a is more restrictive, so blot out the b bound
              allBounds[j] = null;
              n--;
            } else if (factory.IsSubType(bBound, aBound)) {
              // b is more restrictive, so blot out the a bound
              allBounds[i] = null;
              n--;
              goto CONTINUE_OUTER_LOOP;
            }
          }
        CONTINUE_OUTER_LOOP: {
          }
        }
        Contract.Assert(1 <= n);
        return new Elt(allBounds, n);
      }
    }

    public override Element/*!*/ Widen(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return Join(first, second);
    }

    protected override bool AtMost(Element/*!*/ first, Element/*!*/ second) // this <= that
    {
      //Contract.Requires(first != null);
      //Contract.Requires(second != null);
      Elt/*!*/ a = (Elt/*!*/)cce.NonNull(first);
      Elt/*!*/ b = (Elt/*!*/)cce.NonNull(second);
      Contract.Assert(a.what != What.Bottom && b.what != What.Bottom);

      if (a.what == What.Exact && b.what == What.Exact) {
        Contract.Assert(a.ty != null && b.ty != null);
        return factory.IsTypeEqual(a.ty, b.ty);
      } else if (b.what == What.Exact) {
        return false;
      } else if (a.what == What.Exact) {
        Contract.Assert(a.ty != null);
        if (b.ty != null) {
          return factory.IsSubType(a.ty, b.ty);
        } else {
          return Contract.ForAll(b.manyBounds, bound => factory.IsSubType(a.ty, bound));
        }
      } else {
        Contract.Assert(a.what == What.Bounds && b.what == What.Bounds);
        Contract.Assert(a.ty != null || a.manyBounds != null);  // a precondition is that a is not Top
        Contract.Assert(b.ty != null || b.manyBounds != null);  // a precondition is that b is not Top
        // Return true iff: for each constraint in b, there is a stricter constraint in a.
        if (a.ty != null && b.ty != null) {
          return factory.IsSubType(a.ty, b.ty);
        } else if (a.ty != null) {
          return Contract.ForAll(b.manyBounds, bound => factory.IsSubType(a.ty, bound));
        } else if (b.ty != null) {
          return Contract.Exists(a.manyBounds, bound => factory.IsSubType(bound, b.ty));
        } else {
          return Contract.ForAll(b.manyBounds, bBound => Contract.Exists(a.manyBounds, aBound => factory.IsSubType(aBound, bBound)));
        }
      }
    }

    public override IExpr/*!*/ ToPredicate(IVariable/*!*/ var, Element/*!*/ element) {
      //Contract.Requires(element != null);
      //Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      Elt e = (Elt)element;
      switch (e.what) {
        case What.Bottom:
          return propFactory.False;
        case What.Exact:
          return factory.IsExactlyA(var, cce.NonNull(e.ty));
        case What.Bounds:
          if (e.ty == null && e.manyBounds == null) {
            return propFactory.True;
          } else if (e.ty != null) {
            return factory.IsA(var, e.ty);
          } else {
            IExpr/*!*/ p = factory.IsA(var, (IExpr/*!*/)cce.NonNull(e.manyBounds)[0]);
            for (int i = 1; i < e.manyBounds.Length; i++) {
              p = propFactory.And(p, factory.IsA(var, (IExpr/*!*/)cce.NonNull(e.manyBounds[i])));
            }
            return p;
          }
        default: {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          }
          throw new System.Exception();
      }
    }

    public override IExpr GetFoldExpr(Element/*!*/ e) {
      //Contract.Requires(e != null);
      // cannot fold into an expression that can be substituted for the variable
      return null;
    }

    public override bool Understands(IFunctionSymbol/*!*/ f, IList/*<IExpr!>*//*!*/ args) {
      //Contract.Requires(args != null);
      //Contract.Requires(f != null);
      bool isEq = f.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq);
      if (isEq || f.Equals(Microsoft.AbstractInterpretationFramework.Value.Subtype)) {
        Contract.Assert(args.Count == 2);
        IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(args[0]);
        IExpr/*!*/ arg1 = (IExpr/*!*/)cce.NonNull(args[1]);

        // Look for $typeof(var) == t or t == $typeof(var) or $typeof(var) <: t
        if (isEq && factory.IsTypeConstant(arg0)) {
          // swap the arguments
          IExpr/*!*/ tmp = arg0;
          arg0 = arg1;
          arg1 = tmp;
        } else if (!factory.IsTypeConstant(arg1)) {
          return false;
        }
        IFunApp typeofExpr = arg0 as IFunApp;
        if (typeofExpr != null &&
            typeofExpr.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Typeof)) {
          Contract.Assert(typeofExpr.Arguments.Count == 1);
          if (typeofExpr.Arguments[0] is IVariable) {
            // we have a match
            return true;
          }
        }
      }
      return false;
    }

    public override Element/*!*/ EvaluatePredicate(IExpr/*!*/ e) {
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      IFunApp nary = e as IFunApp;
      if (nary != null) {

        bool isEq = nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq);
        if (isEq || nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Subtype)) {
          IList/*<IExpr!>*//*!*/ args = nary.Arguments;
          Contract.Assert(args != null);
          Contract.Assert(args.Count == 2);
          IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(args[0]);
          IExpr/*!*/ arg1 = (IExpr/*!*/)cce.NonNull(args[1]);

          // Look for $typeof(var) == t or t == $typeof(var) or $typeof(var) <: t
          if (isEq && factory.IsTypeConstant(arg0)) {
            // swap the arguments
            IExpr/*!*/ tmp = arg0;
            arg0 = arg1;
            arg1 = tmp;
          } else if (!factory.IsTypeConstant(arg1)) {
            return Top;
          }
          IFunApp typeofExpr = arg0 as IFunApp;
          if (typeofExpr != null &&
              typeofExpr.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Typeof)) {
            Contract.Assert(typeofExpr.Arguments.Count == 1);
            if (typeofExpr.Arguments[0] is IVariable) {
              // we have a match
              return new Elt(isEq ? What.Exact : What.Bounds, arg1);
            }
          }
        }
      }
      return Top;
    }

  }
}
