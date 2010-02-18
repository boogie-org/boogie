//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using Microsoft.Contracts;
namespace Microsoft.AbstractInterpretationFramework
{
    using System.Collections;
    using System.Diagnostics;
    using System.Compiler.Analysis;

    public class NullnessLattice : MicroLattice 
    {
        readonly INullnessFactory! factory;

        public NullnessLattice(INullnessFactory! factory) {
            this.factory = factory;
            // base();
        }
        
        enum Value { Bottom, NotNull, Null, MayBeNull }

        private class Elt : Element
        {
            public Value value;

            public Elt (Value v) { this.value = v; }
            
            [Pure]
            public override System.Collections.Generic.ICollection<IVariable!>! FreeVariables()
            {
                return (!) (new System.Collections.Generic.List<IVariable!>()).AsReadOnly();
            }
            
            public override Element! Clone()
            {
                return new Elt(this.value);
            }
        }


        public override Element! Top 
        {
            get { return new Elt(Value.MayBeNull); } 
        }

        public override Element! Bottom 
        { 
            get { return new Elt(Value.Bottom); } 
        }

        public static Element! Null
        { 
            get { return new Elt(Value.Null); } 
        }

        public static Element! NotNull 
        { 
            get { return new Elt(Value.NotNull); } 
        }

        public override bool IsTop (Element! element)
        {
            Elt e = (Elt) element;
            return e.value == Value.MayBeNull;
        }

        public override bool IsBottom    (Element! element)
        {
            Elt e = (Elt) element;
            return e.value == Value.Bottom;
        }

        public override Lattice.Element! NontrivialJoin (Element! first, Element! second)
        {
            Elt a = (Elt) first;
            Elt b = (Elt) second;
            return (a.value == b.value) ? a : (Elt)Top;
        }

        public override Lattice.Element! NontrivialMeet (Element! first, Element! second)
        {
            Elt a = (Elt) first;
            Elt b = (Elt) second;
            return (a.value == b.value) ? a : (Elt)Bottom;
        }
        
        public override Element! Widen (Element! first, Element! second)
        {
            return Join(first,second);
        }

        protected override bool AtMost (Element! first, Element! second) // this <= that
        {
            Elt a = (Elt) first;
            Elt b = (Elt) second;
            return a.value == b.value;
        }

        public override IExpr! ToPredicate(IVariable! var, Element! element) {
            Elt e = (Elt)element;

            if (e.value == Value.NotNull)
            {
                return factory.Neq(var, factory.Null);
            }
            if (e.value == Value.Null)
            {
                return factory.Eq(var, factory.Null);
            }
            assert false;
            throw new System.Exception();
        }

        public override IExpr GetFoldExpr(Element! e) {
            Elt elt = (Elt)e;
            if (elt.value == Value.Null) {
                return factory.Null;
            } else {
                // can't fold into an expression
                return null;
            }
        }

        public override bool Understands(IFunctionSymbol! f, IList/*<IExpr!>*/! args) {
            if (f.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq) ||
                f.Equals(Microsoft.AbstractInterpretationFramework.Value.Neq)) {

                assert args.Count == 2;
                IExpr! arg0 = (IExpr!)args[0];
                IExpr! arg1 = (IExpr!)args[1];

                // Look for "x OP null" or "null OP x" where OP is "==" or "!=".
                if (arg0 is IVariable && arg1 is IFunApp && ((IFunApp)arg1).FunctionSymbol == Ref.Null) {
                    return true;
                } else if (arg1 is IVariable && arg0 is IFunApp && ((IFunApp)arg0).FunctionSymbol == Ref.Null) {
                    return true;
                }
            }
            return false;
        }

        public override Element! EvaluatePredicate(IExpr! e) {
            IFunApp nary = e as IFunApp;
            if (nary != null) {
                bool isEq = nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq);
                if (isEq || nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Neq)) {
                    IList/*<IExpr!>*/! args = nary.Arguments;
                    assert args.Count == 2;
                    IExpr! arg0 = (IExpr!)args[0];
                    IExpr! arg1 = (IExpr!)args[1];

                    // Look for "x OP null" or "null OP x" where OP is "==" or "!=".
                    IVariable var = null;
                    if (arg0 is IVariable && arg1 is IFunApp && ((IFunApp)arg1).FunctionSymbol == Ref.Null)
                    {
                        var = (IVariable)arg0;
                    }
                    else if (arg1 is IVariable && arg0 is IFunApp && ((IFunApp)arg0).FunctionSymbol == Ref.Null)
                    {
                        var = (IVariable)arg1;
                    }

                    if (var != null) // found the pattern
                    {
                        return isEq ? Null:NotNull;
                    }
                }
            }
            return Top;
        }
    }

#if false

    public class NullnessMicroLattice : MicroLattice 
    {
        public override MicroLatticeElement Top { get { return NullnessLatticeElement.Top; } }
        public override MicroLatticeElement Bottom { get { return NullnessLatticeElement.Bottom; } }


        public override MicroLatticeElement EvaluateExpression (Expr e, LookupValue lookup)
        {
            if (e is LiteralExpr && ((LiteralExpr)e).Val == null)
            {
                return NullnessLatticeElement.Null;
            }
            return Top;
        }


        public override MicroLatticeElement EvaluatePredicate (Expr e, LookupValue lookup)
        {
            NAryExpr nary = e as NAryExpr;
            if (nary != null && 
                    (nary.Fun.FunctionName.Equals("==") || nary.Fun.FunctionName.Equals("!=")))
            {
                Debug.Assert(nary.Args.Length == 2);

                Expr arg0 = nary.Args[0], arg1 = nary.Args[1];
                Variable var = null;

                // Look for "x OP null" or "null OP x" where OP is "==" or "!=".
                if (arg0 is IdentifierExpr && arg1 is LiteralExpr && ((LiteralExpr)arg1).Val == null)
                {
                    var = ((IdentifierExpr)arg0).Decl;
                }
                else if (arg1 is IdentifierExpr && arg0 is LiteralExpr && ((LiteralExpr)arg0).Val == null)
                {
                    var = ((IdentifierExpr)arg1).Decl;
                }

                if (var != null) // found the pattern
                {
                    return nary.Fun.FunctionName.Equals("==") ? 
                        NullnessLatticeElement.Null : 
                        NullnessLatticeElement.NotNull;
                }
            }
            return Top;
        }
    }

#endif

}
