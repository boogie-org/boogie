//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework
{
    using System.Collections;
    using System.Diagnostics;
    using System.Compiler.Analysis;
    using Microsoft.SpecSharp.Collections;
    using Microsoft.Contracts;

    /// <summary>
    /// Represents information about the dynamic type of a variable.  In particular, for a
    /// variable "v", represents either Bottom, "typeof(v)==T" for some type T, or a set
    /// of constraints "typeof(v) subtype of T_i for some number of T_i's.
    /// </summary>
    public class DynamicTypeLattice : MicroLattice 
    {
        enum What { Bottom, Exact, Bounds }

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
            invariant what == What.Bottom ==> ty == null && manyBounds == null;
            invariant manyBounds != null ==> what == What.Bounds;
            invariant manyBounds != null ==> forall{int i in (0:manyBounds.Length); manyBounds[i] != null};

            public Elt(What what, IExpr ty)
                requires what == What.Bottom ==> ty == null;
                requires what == What.Exact ==> ty != null;
            {
                this.what = what;
                this.ty = ty;
                this.manyBounds = null;
            }
            
            public Elt(IExpr[]! bounds)
                requires forall{int i in (0:bounds.Length); bounds[i] != null};
            {
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
            public Elt(ArrayList /*IExpr*/! bounds, int n)
                requires 0 <= n && n <= bounds.Count;
            {
                this.what = What.Bounds;
                if (n > 1) {
                    this.manyBounds = new IExpr[n];
                }
                int k = 0;
                foreach (IExpr bound in bounds) {
                    if (bound != null) {
                        assert k != n;
                        if (n == 1) {
                            assert this.ty == null;
                            this.ty = bound;
                        } else {
                            assume manyBounds != null;
                            manyBounds[k] = bound;
                        }
                        k++;
                    }
                }
                assert k == n;
            }

            public int BoundsCount
            {
                get
                    ensures 0 <= result;
                {
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
            public override System.Collections.Generic.ICollection<IVariable!>! FreeVariables()
            {
                return (!) (new System.Collections.Generic.List<IVariable!>()).AsReadOnly();
            }
            
            public override Element! Clone()
            {
                if (this.manyBounds != null)
                    return new Elt(this.manyBounds);
                else
                    return new Elt(this.what, this.ty);
            }
        }

        readonly ITypeExprFactory! factory;
        readonly IPropExprFactory! propFactory;

        public DynamicTypeLattice(ITypeExprFactory! factory, IPropExprFactory! propFactory)
        {
            this.factory = factory;
            this.propFactory = propFactory;
            // base();
        }

        public override Element! Top
        {
            get { return new Elt(What.Bounds, null); } 
        }

        public override Element! Bottom
        { 
            get { return new Elt(What.Bottom, null); } 
        }

        public override bool IsTop (Element! element)
        {
            Elt e = (Elt)element;
            return e.what == What.Bounds && e.ty == null && e.manyBounds == null;
        }

        public override bool IsBottom(Element! element)
        { 
            Elt e = (Elt)element;
            return e.what == What.Bottom;
        }

        public override Element! NontrivialJoin(Element! first, Element! second)
        {
            Elt a = (Elt)first;
            Elt b = (Elt)second;
            assert a.what != What.Bottom && b.what != What.Bottom;
            if (a.what == What.Exact && b.what == What.Exact) {
                assert a.ty != null && b.ty != null;
                if (factory.IsTypeEqual(a.ty, b.ty)) {
                    return a;
                } else {
                    return new Elt(What.Bounds, factory.JoinTypes(a.ty, b.ty));
                }
            }

            // The result is going to be a Bounds, since at least one of the operands is a Bounds.
            assert 1 <= a.BoundsCount && 1 <= b.BoundsCount;  // a preconditions is that neither operand is Top
            int n = a.BoundsCount + b.BoundsCount;

            // Special case:  a and b each has exactly one bound
            if (n == 2) {
                assert a.ty != null && b.ty != null;
                IExpr! join = factory.JoinTypes(a.ty, b.ty);
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
                allBounds.AddRange((!)a.manyBounds);
            }
            int bStart = allBounds.Count;
            if (b.ty != null) {
                allBounds.Add(b.ty);
            } else {
                allBounds.AddRange((!)b.manyBounds);
            }
            // compute the join of each pair, putting non-redundant joins into "result"
            for (int i = 0; i < bStart; i++) {
                IExpr! aBound = (IExpr!)allBounds[i];
                for (int j = bStart; j < allBounds.Count; j++) {
                    IExpr! bBound = (IExpr!)allBounds[j];
                    
                    IExpr! join = factory.JoinTypes(aBound, bBound);

                    int k = 0;
                    while (k < result.Count) {
                        IExpr! r = (IExpr!)result[k];
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
                    NEXT_PAIR: {}
                }
            }
            return new Elt(result, result.Count);
        }


        public override Element! NontrivialMeet(Element! first, Element! second)
        {
            Elt a = (Elt)first;
            Elt b = (Elt)second;
            assert a.what != What.Bottom && b.what != What.Bottom;

            if (a.what == What.Exact && b.what == What.Exact) {
                assert a.ty != null && b.ty != null;
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
                assert a.what == What.Exact && b.what == What.Bounds;
                // Check the exact type against all bounds.  If the exact type is more restrictive
                // than all bounds, then return it.  If some bound is not met by the exact type, return
                // bottom.
                assert a.ty != null;
                if (b.ty != null && !factory.IsSubType(a.ty, b.ty)) {
                    return Bottom;
                }
                if (b.manyBounds != null) {
                    foreach (IExpr! bound in b.manyBounds) {
                        if (!factory.IsSubType(a.ty, bound)) {
                            return Bottom;
                        }
                    }
                }
                return a;
            }

            else {
                // Both operands are Bounds.
                assert a.what == What.Bounds && b.what == What.Bounds;

                // Take all the bounds, but prune those bounds that follow from others.
                assert 1 <= a.BoundsCount && 1 <= b.BoundsCount;  // a preconditions is that neither operand is Top
                int n = a.BoundsCount + b.BoundsCount;
                // Special case:  a and b each has exactly one bound
                if (n == 2) {
                    assert a.ty != null && b.ty != null;
                    if (factory.IsSubType(a.ty, b.ty)) {
                        // a is more restrictive
                        return a;
                    } else if (factory.IsSubType(b.ty, a.ty)) {
                        // b is more restrictive
                        return b;
                    } else {
                        IExpr[]! bounds = new IExpr[2];
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
                    allBounds.AddRange((!)a.manyBounds);
                }
                int bStart = allBounds.Count;
                if (b.ty != null) {
                    allBounds.Add(b.ty);
                } else {
                    allBounds.AddRange((!)b.manyBounds);
                }
                for (int i = 0; i < bStart; i++) {
                    IExpr! aBound = (IExpr!)allBounds[i];
                    for (int j = bStart; j < allBounds.Count; j++) {
                        IExpr bBound = (IExpr!)allBounds[j];
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
                    CONTINUE_OUTER_LOOP: {}
                }
                assert 1 <= n;
                return new Elt(allBounds, n);
            }
        }

        public override Element! Widen (Element! first, Element! second)
        {
            return Join(first,second);
        }

        protected override bool AtMost (Element! first, Element! second) // this <= that
        {
            Elt! a = (Elt!)first;
            Elt! b = (Elt!)second;
            assert a.what != What.Bottom && b.what != What.Bottom;
            
            if (a.what == What.Exact && b.what == What.Exact) {
                assert a.ty != null && b.ty != null;
                return factory.IsTypeEqual(a.ty, b.ty);
            } else if (b.what == What.Exact) {
                return false;
            } else if (a.what == What.Exact) {
                assert a.ty != null;
                if (b.ty != null) {
                    return factory.IsSubType(a.ty, b.ty);
                } else {
                    return forall{IExpr! bound in b.manyBounds; factory.IsSubType(a.ty, bound)};
                }
            } else {
                assert a.what == What.Bounds && b.what == What.Bounds;
                assert a.ty != null || a.manyBounds != null;  // a precondition is that a is not Top
                assert b.ty != null || b.manyBounds != null;  // a precondition is that b is not Top
                // Return true iff: for each constraint in b, there is a stricter constraint in a.
                if (a.ty != null && b.ty != null) {
                    return factory.IsSubType(a.ty, b.ty);
                } else if (a.ty != null) {
                    return forall{IExpr! bound in b.manyBounds; factory.IsSubType(a.ty, bound)};
                } else if (b.ty != null) {
                    return exists{IExpr! bound in a.manyBounds; factory.IsSubType(bound, b.ty)};
                } else {
                    return forall{IExpr! bBound in b.manyBounds;
                             exists{IExpr! aBound in a.manyBounds; factory.IsSubType(aBound, bBound)}};
                }
            }
        }

        public override IExpr! ToPredicate(IVariable! var, Element! element) {
            Elt e = (Elt)element;
            switch (e.what) {
            case What.Bottom:
                return propFactory.False;
            case What.Exact:
                return factory.IsExactlyA(var, (!)e.ty);
            case What.Bounds:
                if (e.ty == null && e.manyBounds == null) {
                    return propFactory.True;
                } else if (e.ty != null) {
                    return factory.IsA(var, e.ty);
                } else {
                    IExpr! p = factory.IsA(var, (IExpr!)((!)e.manyBounds)[0]);
                    for (int i = 1; i < e.manyBounds.Length; i++) {
                        p = propFactory.And(p, factory.IsA(var, (IExpr!)e.manyBounds[i]));
                    }
                    return p;
                }
            default:
                assert false;
                throw new System.Exception();
            }
        }

        public override IExpr GetFoldExpr(Element! e) {
            // cannot fold into an expression that can be substituted for the variable
            return null;
        }

        public override bool Understands(IFunctionSymbol! f, IList/*<IExpr!>*/! args) {
            bool isEq = f.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq);
            if (isEq || f.Equals(Microsoft.AbstractInterpretationFramework.Value.Subtype)) {
                assert args.Count == 2;
                IExpr! arg0 = (IExpr!)args[0];
                IExpr! arg1 = (IExpr!)args[1];

                // Look for $typeof(var) == t or t == $typeof(var) or $typeof(var) <: t
                if (isEq && factory.IsTypeConstant(arg0)) {
                    // swap the arguments
                    IExpr! tmp = arg0;
                    arg0 = arg1;
                    arg1 = tmp;
                } else if (!factory.IsTypeConstant(arg1)) {
                    return false;
                }
                IFunApp typeofExpr = arg0 as IFunApp;
                if (typeofExpr != null &&
                    typeofExpr.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Typeof)) {
                    assert typeofExpr.Arguments.Count == 1;
                    if (typeofExpr.Arguments[0] is IVariable) {
                        // we have a match
                        return true;
                    }
                }
            }
            return false;
        }

        public override Element! EvaluatePredicate(IExpr! e) {
            IFunApp nary = e as IFunApp;
            if (nary != null) {

                bool isEq = nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq);
                if (isEq || nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Subtype)) {
                    IList/*<IExpr!>*/! args = nary.Arguments;
                    assert args.Count == 2;
                    IExpr! arg0 = (IExpr!)args[0];
                    IExpr! arg1 = (IExpr!)args[1];
                    
                    // Look for $typeof(var) == t or t == $typeof(var) or $typeof(var) <: t
                    if (isEq && factory.IsTypeConstant(arg0)) {
                        // swap the arguments
                        IExpr! tmp = arg0;
                        arg0 = arg1;
                        arg1 = tmp;
                    } else if (!factory.IsTypeConstant(arg1)) {
                        return Top;
                    }
                    IFunApp typeofExpr = arg0 as IFunApp;
                    if (typeofExpr != null &&
                        typeofExpr.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Typeof)) {
                        assert typeofExpr.Arguments.Count == 1;
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
