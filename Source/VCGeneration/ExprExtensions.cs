//-----------------------------------------------------------------------------
//
// Copyright (C) 2012 Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------


using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Term = Microsoft.Boogie.VCExprAST.VCExpr;
using FuncDecl = Microsoft.Boogie.VCExprAST.VCExprOp;
using Sort = Microsoft.Boogie.Type;
using Microsoft.Boogie.VCExprAST;


/** This namespace contains some extensions to allow VCExpr to provide the
 *   interface needed by RPFP and FixedpointVC. */

namespace Microsoft.Boogie.ExprExtensions
{
    class ReferenceComparer<T> : IEqualityComparer<T> where T : class
    {
        private static ReferenceComparer<T> m_instance;

        public static ReferenceComparer<T> Instance
        {
            get
            {
                return m_instance ?? (m_instance = new ReferenceComparer<T>());
            }
        }

        public bool Equals(T x, T y)
        {
            return ReferenceEquals(x, y);
        }

        public int GetHashCode(T obj)
        {
            return System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(obj);
        }
    }

    public class TermDict<T> : Dictionary<Term, T> 
    {
        public TermDict() : base(ReferenceComparer<Term>.Instance) { }
    }

        

    public enum TermKind { App, Other };

    public enum DeclKind { Uninterpreted, And, Implies, Label, Other };

    public static class MyExtensions
    {
        public static Term[] GetAppArgs(this Term t)
        {
            Microsoft.Boogie.VCExprAST.VCExprNAry tn = t as Microsoft.Boogie.VCExprAST.VCExprNAry;
            return tn.ToArray();
        }

        public static FuncDecl GetAppDecl(this Term t)
        {
            Microsoft.Boogie.VCExprAST.VCExprNAry tn = t as Microsoft.Boogie.VCExprAST.VCExprNAry;
            return tn.Op;
        }

        public static string GetDeclName(this FuncDecl f)
        {
            return (f as VCExprBoogieFunctionOp).Func.Name; //TODO
        }

        public static DeclKind GetKind(this FuncDecl f)
        {
            if (f is VCExprBoogieFunctionOp)
                return DeclKind.Uninterpreted;
            if (f == VCExpressionGenerator.AndOp)
                return DeclKind.And;
            if (f == VCExpressionGenerator.ImpliesOp)
                return DeclKind.Implies;
            if (f is VCExprLabelOp)
                return DeclKind.Label;
            return DeclKind.Other;
        }

        public static bool IsLabel(this Term t)
        {
            return (t is VCExprNAry) && (GetAppDecl(t) is VCExprLabelOp);
        }

        public static string LabelName(this Term t)
        {
            return (GetAppDecl(t) as VCExprLabelOp).label;
        }
         
        public static Sort GetSort(this Term t)
        {
            return t.Type;
        }

        public static TermKind GetKind(this Term t)
        {
            if (t is Microsoft.Boogie.VCExprAST.VCExprNAry)
                return TermKind.App;
            return TermKind.Other;
        }

        public static bool IsFunctionApp(this Term t)
        {
            return t.GetKind() == TermKind.App && t.GetAppDecl().GetKind() == DeclKind.Uninterpreted;
        }

        public static bool IsFalse(this Term t)
        {
            return t == VCExpressionGenerator.False;
        }

        public static Term VCExprToTerm(this Microsoft.Boogie.ProverContext ctx, VCExpr e, LineariserOptions lin){
          return e;
        }

    }

    public class Context : Microsoft.Boogie.VCExpressionGenerator
    {
        public Term MkTrue()
        {
            return VCExpressionGenerator.True;
        }

        public Term MkFalse()
        {
            return VCExpressionGenerator.False;
        }


        public List<Term> axioms = new List<Term>();

        public void AddAxiom(Term ax)
        {
            axioms.Add(ax);
        }

        public void RemoveAxiom(Term ax)
        {
            axioms.Remove(ax);
        }

        public FuncDecl MkFuncDecl(string name, FuncDecl f)
        {
            Function h =  (f as VCExprBoogieFunctionOp).Func;
            Function g = new Function(Token.NoToken, name, h.InParams, h.OutParams[0]);
            return BoogieFunctionOp(g);
        }

        public FuncDecl MkFuncDecl(string name, Sort rng)
        {
            Function g = new Function(Token.NoToken, name, new List<Variable>(), new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "dummy",rng)));
            return BoogieFunctionOp(g);
        }

        public Term MkApp(FuncDecl f, Term[] args)
        {
            return Function(f, args);
        }

        public Term MkApp(FuncDecl f, Term[] args, Type[]/*!*/ typeArguments)
        {
            return Function(f, args, typeArguments);
        }

        public Term MkApp(FuncDecl f, Term arg)
        {
            return Function(f, arg);
        }

        public Term CloneApp(Term t, Term[] args)
        {
            var f = t.GetAppDecl();
            var typeArgs = (t as VCExprNAry).TypeArguments;
            if (typeArgs != null && typeArgs.Count > 0)
            {
                return MkApp(f, args, typeArgs.ToArray());
            }
            else
            {
                return MkApp(f, args);
            }
        }
        
        public Term MkAnd(Term[] args)
        {
            if (args.Length == 0) return True;
            Term res = args[0];
            for (int i = 1; i < args.Length; i++)
                res = And(res, args[i]);
            return res;
        }

        public Term MkAnd(Term arg1, Term arg2)
        {
            return And(arg1, arg2);
        }


        public Term MkNot(Term arg1)
        {
            return Not(arg1);
        }
        
        public Term MkImplies(Term arg1, Term arg2)
        {
            return Implies(arg1, arg2);
        }
        
        public Term MkEq(Term arg1, Term arg2)
        {
            return Eq(arg1, arg2);
        }

        public Sort MkBoolSort()
        {
            return Type.Bool;
        }

        public Term MkConst(string name, Sort sort)
        {
            return Variable(name, sort);
        }

        public Term MkForall(Term[] bounds, Term body)
        {
            if (bounds.Length == 0)
                return body;
            List<VCExprVar> vbs = new List<VCExprVar>();
            foreach(var v in bounds)
                vbs.Add(v as VCExprVar);
            return Forall(vbs,new List<VCTrigger>(), body);
        }

        public Term MkExists(Term[] bounds, Term body)
        {
            if (bounds.Length == 0)
                return body; 
            List<VCExprVar> vbs = new List<VCExprVar>();
            foreach (var v in bounds)
                vbs.Add(v as VCExprVar);
            return Exists(vbs, new List<VCTrigger>(), body);
        }

        private class Letifier
        {
            private class counter
            {
                public int cnt = 0;
            }
            TermDict<counter> refcnt = new TermDict<counter>();
            List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
            TermDict< VCExprVar> bindingMap = new TermDict< VCExprVar>();
            int letcnt = 0;
            Context ctx;

            public Letifier(Context _ctx) { ctx = _ctx; }

            private void RefCnt(Term t)
            {
                counter cnt;
                if (!refcnt.TryGetValue(t, out cnt))
                {
                    cnt = new counter();
                    refcnt.Add(t, cnt);
                }
                cnt.cnt++;
                if (cnt.cnt == 1)
                {
                    var kind = t.GetKind();
                    if (kind == TermKind.App)
                    {
                        var args = t.GetAppArgs();
                        foreach (var arg in args)
                            RefCnt(arg);
                    }
                    else if (t is VCExprQuantifier)
                    {
                        RefCnt((t as VCExprQuantifier).Body);
                    }
                }
            }

            private Term Doit(Term t)
            {
                VCExprVar v;
                if (bindingMap.TryGetValue(t, out v))
                {
                    return v;
                }
                Term res = null;
                var kind = t.GetKind();
                bool letok = false;
                if (kind == TermKind.App)
                {
                    var f = t.GetAppDecl();
                    var args = t.GetAppArgs();
                    args = args.Select(x => Doit(x)).ToArray();
                    res = ctx.MkApp(f, args);
                    letok = true;
                }
                else if (t is VCExprQuantifier)
                {
                    var q = t as VCExprQuantifier;
                    var newbody = ctx.Letify(q.Body);
                    if (q.Quan == Quantifier.ALL)
                        res = ctx.Forall(q.BoundVars, q.Triggers, newbody);
                    else
                        res = ctx.Exists(q.BoundVars, q.Triggers, newbody);
                    letok = true;
                }
                else res = t;
                if (letok && refcnt[t].cnt > 1)
                {
                    VCExprVar lv = ctx.MkConst("fpvc$" + Convert.ToString(letcnt), t.GetSort()) as VCExprVar;
                    VCExprLetBinding b = ctx.LetBinding(lv, res);
                    bindings.Add(b);
                    bindingMap.Add(t, lv);
                    res = lv;
                    letcnt++;
                }
                return res;
            }

            public Term Letify(Term t)
            {
                RefCnt(t);
                Term res = Doit(t);
                if (bindings.Count > 0)
                    res = ctx.Let(bindings, res);
                return res;
            }

        }

        public Term Letify(Term t)
        {
            var thing = new Letifier(this);
            return thing.Letify(t);
        }

    };
}
