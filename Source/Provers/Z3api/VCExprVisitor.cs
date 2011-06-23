//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Z3;

namespace Microsoft.Boogie.Z3
{
    public class Z3apiExprLineariser : IVCExprVisitor<Term, LineariserOptions>
    {
        private Z3apiOpLineariser OpLinObject = null;
        private IVCExprOpVisitor<Term, LineariserOptions> OpLineariser
        {
            get
            {
                Contract.Ensures(Contract.Result<IVCExprOpVisitor<bool, LineariserOptions>>() != null);
                if (OpLinObject == null)
                    OpLinObject = new Z3apiOpLineariser(this);
                return OpLinObject;
            }
        }

        internal readonly UniqueNamer namer;
        internal readonly Dictionary<VCExprVar, Term> letBindings;
        protected Z3Context cm;

        public Z3apiExprLineariser(Z3Context cm, UniqueNamer namer)
        {
            this.cm = cm;
            this.namer = namer;
            this.letBindings = new Dictionary<VCExprVar, Term>();
        }

        public Term Linearise(VCExpr expr, LineariserOptions options)
        {
            Contract.Requires(options != null);
            Contract.Requires(expr != null);
            return expr.Accept<Term, LineariserOptions>(this, options);
        }

        /////////////////////////////////////////////////////////////////////////////////////

        public Term Visit(VCExprLiteral node, LineariserOptions options)
        {
            Contract.Requires(options != null);
            Contract.Requires(node != null);

            if (node == VCExpressionGenerator.True)
                return cm.z3.MkTrue();
            else if (node == VCExpressionGenerator.False)
                return cm.z3.MkFalse();
            else if (node is VCExprIntLit)
              return cm.z3.MkNumeral(((VCExprIntLit)node).Val.ToInt, cm.z3.MkIntSort());
            else
            {
                Contract.Assert(false);
                throw new cce.UnreachableException();
            }
        }

        public Term Visit(VCExprNAry node, LineariserOptions options)
        {
            Contract.Requires(options != null);
            Contract.Requires(node != null);
            VCExprOp op = node.Op;
            Contract.Assert(op != null);

            if (op.Equals(VCExpressionGenerator.AndOp) || op.Equals(VCExpressionGenerator.OrOp))
            {
                // handle these operators without recursion
                List<Term> asts = new List<Term>();
                string opString = op.Equals(VCExpressionGenerator.AndOp) ? "AND" : "OR";

                IEnumerator enumerator = new VCExprNAryUniformOpEnumerator(node);
                Contract.Assert(enumerator != null);
                while (enumerator.MoveNext())
                {
                    VCExprNAry naryExpr = enumerator.Current as VCExprNAry;
                    if (naryExpr == null || !naryExpr.Op.Equals(op))
                    {
                        asts.Add(Linearise(cce.NonNull((VCExpr)enumerator.Current), options));
                    }
                }

                return cm.Make(opString, asts);
            }

            return node.Accept<Term, LineariserOptions>(OpLineariser, options);
        }

        public Term Visit(VCExprVar node, LineariserOptions options)
        {
            Contract.Requires(options != null);
            Contract.Requires(node != null);
            if (letBindings.ContainsKey(node))
            {
                return letBindings[node];
            }
            else
            {
                string varName = namer.GetName(node, node.Name);
                return cm.GetConstant(varName, node.Type);
            }
        }

        public Term Visit(VCExprQuantifier node, LineariserOptions options)
        {
            Contract.Requires(options != null);
            Contract.Requires(node != null);
            Contract.Assert(node.TypeParameters.Count == 0);

            namer.PushScope();
            try
            {
                List<string> varNames;
                List<Type> varTypes;
                VisitBounds(node.BoundVars, out varNames, out varTypes);
                List<Pattern> patterns;
                List<Term> no_patterns;
                VisitTriggers(node.Triggers, options, out patterns, out no_patterns);
                Term body = Linearise(node.Body, options);
                Term result;
                uint weight = 1;
                string qid = "";
                int skolemid = 0;

                if (options.QuantifierIds)
                {
                    VCQuantifierInfos infos = node.Infos;
                    Contract.Assert(infos != null);
                    if (infos.qid != null)
                    {
                        qid = infos.qid;
                    }
                    if (0 <= infos.uniqueId)
                    {
                        skolemid = infos.uniqueId;
                    }
                }

                if (options.UseWeights)
                {
                    weight = (uint) QKeyValue.FindIntAttribute(node.Infos.attributes, "weight", 1);
                }

                switch (node.Quan)
                {
                    case Microsoft.Boogie.VCExprAST.Quantifier.ALL:
                        result = cm.MakeQuantifier(true, weight, qid, skolemid, varNames, varTypes, patterns, no_patterns, body); break;
                    case Microsoft.Boogie.VCExprAST.Quantifier.EX:
                        result = cm.MakeQuantifier(false, weight, qid, skolemid, varNames, varTypes, patterns, no_patterns, body); break;
                    default:
                        throw new Exception("unknown quantifier kind " + node.Quan);
                }
                return result;
            }
            finally
            {
                namer.PopScope();
            }
        }
        
        private void VisitBounds(List<VCExprVar> boundVars, out List<string> varNames, out List<Type> varTypes)
        {
            varNames = new List<string>();
            varTypes = new List<Type>();
            foreach (VCExprVar var in boundVars)
            {
                string varName = namer.GetLocalName(var, var.Name);
                varNames.Add(varName);
                varTypes.Add(var.Type);
            }
        }

        private void VisitTriggers(List<VCTrigger> triggers, LineariserOptions options, out List<Pattern> patterns, out List<Term> no_patterns)
        {
            patterns = new List<Pattern>();
            no_patterns = new List<Term>();
            foreach (VCTrigger trigger in triggers)
            {
                List<Term> exprs = new List<Term>();
                foreach (VCExpr expr in trigger.Exprs)
                {
                    System.Diagnostics.Debug.Assert(expr != null);
                    Term termAst = Linearise(expr, options);
                    exprs.Add(termAst);
                }
                if (exprs.Count > 0)
                {
                    if (trigger.Pos)
                    {
                        Pattern pattern = cm.MakePattern(exprs);
                        patterns.Add(pattern);
                    }
                    else
                    {
                        System.Diagnostics.Debug.Assert(false, "Z3api currently does not handle nopats");
                        foreach (Term expr in exprs)
                            no_patterns.Add(expr);
                    }
                }
            }
        }

        public Term Visit(VCExprLet node, LineariserOptions options)
        {
            foreach (VCExprLetBinding b in node)
            {
                Term defAst = Linearise(b.E, options);
                letBindings.Add(b.V, defAst);
            }
            Term letAst = Linearise(node.Body, options);
            foreach (VCExprLetBinding b in node)
            {
                letBindings.Remove(b.V);
            }
            return letAst;
        }  

        /////////////////////////////////////////////////////////////////////////////////////

        internal class Z3apiOpLineariser : IVCExprOpVisitor<Term, LineariserOptions>
        {
            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(ExprLineariser != null);
            }

            private readonly Z3apiExprLineariser ExprLineariser;

            public Z3apiOpLineariser(Z3apiExprLineariser ExprLineariser)
            {
                Contract.Requires(ExprLineariser != null);
                this.ExprLineariser = ExprLineariser;
            }

            ///////////////////////////////////////////////////////////////////////////////////

            private Term WriteApplication(string op, IEnumerable<VCExpr> terms, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(op != null);
                Contract.Requires(cce.NonNullElements(terms));

                List<Term> args = new List<Term>();
                foreach (VCExpr e in terms)
                {
                    Contract.Assert(e != null);
                    args.Add(ExprLineariser.Linearise(e, options));
                }
                return ExprLineariser.cm.Make(op, args);
            }

            ///////////////////////////////////////////////////////////////////////////////////

            public Term VisitNotOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("NOT", node, options);
            }

            public Term VisitEqOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("EQ", node, options);
            }

            public Term VisitNeqOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("NEQ", node, options);
            }

            public Term VisitAndOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("AND", node, options);  
            }

            public Term VisitOrOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("OR", node, options); 
            }

            public Term VisitImpliesOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                if (options.InverseImplies)
                {
                    List<Term> args = new List<Term>();

                    args.Add(ExprLineariser.Linearise(node[1], options));
                    List<Term> t = new List<Term>();
                    t.Add(ExprLineariser.Linearise(node[0], options));
                    args.Add(ExprLineariser.cm.Make("NOT", t));
                    return ExprLineariser.cm.Make("OR", args);
                }
                else
                {
                    return WriteApplication("IMPLIES", node, options);
                }
            }

            public Term VisitDistinctOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);

                if (node.Length < 2)
                {
                    return ExprLineariser.Linearise(VCExpressionGenerator.True, options);
                }
                else
                {
                    List<Term> args = new List<Term>();
                    foreach (VCExpr e in node)
                    {
                        Contract.Assert(e != null);
                        args.Add(ExprLineariser.Linearise(e, options));
                    }
                    return ExprLineariser.cm.Make("DISTINCT", args);
                }
            }

            public Term VisitLabelOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                VCExprLabelOp op = (VCExprLabelOp)node.Op;
                Contract.Assert(op != null);
                return ExprLineariser.cm.MakeLabel(op.label, op.pos, ExprLineariser.Linearise(node[0], options)); 
            }

            public Term VisitSelectOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                List<Term> args = new List<Term>();
                foreach (VCExpr e in node)
                {
                    Contract.Assert(e != null);
                    args.Add(ExprLineariser.Linearise(e, options));
                }

                Term[] unwrapChildren = args.ToArray();
                return ExprLineariser.cm.z3.MkArraySelect(unwrapChildren[0], unwrapChildren[1]);
                // return ExprLineariser.cm.Make(SimplifyLikeExprLineariser.SelectOpName(node), args);
            }

            public Term VisitStoreOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                List<Term> args = new List<Term>();
                foreach (VCExpr e in node)
                {
                    Contract.Assert(e != null);
                    args.Add(ExprLineariser.Linearise(e, options));
                }

                Term[] unwrapChildren = args.ToArray();
                return ExprLineariser.cm.z3.MkArrayStore(unwrapChildren[0], unwrapChildren[1], unwrapChildren[2]);
                // return ExprLineariser.cm.Make(SimplifyLikeExprLineariser.StoreOpName(node), args);
            }

            public Term VisitBvOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                List<int> args = new List<int>();
                foreach (VCExpr e in node) {
                  VCExprIntLit literal = e as VCExprIntLit;
                  System.Diagnostics.Debug.Assert(literal != null);
                  args.Add(literal.Val.ToInt);
                }
                System.Diagnostics.Debug.Assert(args.Count == 1);
                return ExprLineariser.cm.z3.MkNumeral(args[0], ExprLineariser.cm.z3.MkBvSort((uint)node.Type.BvBits));
            }

            public Term VisitBvExtractOp(VCExprNAry node, LineariserOptions options) {
              Contract.Requires(options != null);
              Contract.Requires(node != null);

              VCExprBvExtractOp op = (VCExprBvExtractOp)node.Op;
              Contract.Assert(op != null);
              System.Diagnostics.Debug.Assert(0 <= op.Start && op.Start < op.End);

              List<Term> args = new List<Term>();
              foreach (VCExpr e in node) {
                Contract.Assert(e != null);
                args.Add(ExprLineariser.Linearise(e, options));
              }
              System.Diagnostics.Debug.Assert(args.Count == 1);
              return ExprLineariser.cm.z3.MkBvExtract((uint) op.End - 1, (uint) op.Start, args[0]);
            }

            public Term VisitBvConcatOp(VCExprNAry node, LineariserOptions options) {
              Contract.Requires(options != null);
              Contract.Requires(node != null);

              VCExprBvConcatOp op = (VCExprBvConcatOp)node.Op;
              Contract.Assert(op != null);

              List<Term> args = new List<Term>();
              foreach (VCExpr e in node) {
                Contract.Assert(e != null);
                args.Add(ExprLineariser.Linearise(e, options));
              }
              System.Diagnostics.Debug.Assert(args.Count == 2);
              return ExprLineariser.cm.z3.MkBvConcat(args[0], args[1]);
            }

            public Term VisitIfThenElseOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);

                List<Term> args = new List<Term>();
                args.Add(ExprLineariser.Linearise(node[0], options));
                args.Add(ExprLineariser.Linearise(node[1], options));
                args.Add(ExprLineariser.Linearise(node[2], options));
                return ExprLineariser.cm.Make("ITE", args);
            }

            public Term VisitCustomOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(node != null);
                Contract.Requires(options != null);
                VCExprCustomOp op = (VCExprCustomOp)node.Op;
                List<Term> args = new List<Term>();
                foreach (VCExpr arg in node)
                {
                    args.Add(ExprLineariser.Linearise(arg, options));
                }
                return ExprLineariser.cm.Make(op.Name, args);
            }

            public Term VisitAddOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                if (CommandLineOptions.Clo.ReflectAdd)
                {
                    return WriteApplication("Reflect$Add", node, options);
                }
                else
                {
                    return WriteApplication("+", node, options);
                }
            }

            public Term VisitSubOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("-", node, options);
            }

            public Term VisitMulOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("*", node, options);
            }

            public Term VisitDivOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("/", node, options);
            }

            public Term VisitModOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("%", node, options);
            }

            public Term VisitLtOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("<", node, options);
            }

            public Term VisitLeOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("<=", node, options);
            }

            public Term VisitGtOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication(">", node, options);
            }

            public Term VisitGeOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication(">=", node, options);
            }

            public Term VisitSubtypeOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("<:", node, options);
            }

            public Term VisitSubtype3Op(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("<::", node, options);
            }

            public Term VisitBoogieFunctionOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp)node.Op;
                Contract.Assert(op != null);
                string funcName = op.Func.Name;
                Contract.Assert(funcName != null);
                string bvzName = op.Func.FindStringAttribute("external");
                if (bvzName != null) funcName = bvzName;

                List<Term> args = new List<Term>();
                foreach (VCExpr e in node)
                {
                    Contract.Assert(e != null);
                    args.Add(ExprLineariser.Linearise(e, options));
                }
                return ExprLineariser.cm.Make(funcName, args);
            }
        }
    }
}
