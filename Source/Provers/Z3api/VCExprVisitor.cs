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

namespace Microsoft.Boogie.Z3
{
    public class Z3apiExprLineariser : IVCExprVisitor<Z3TermAst, LineariserOptions>
    {
        private Z3apiOpLineariser OpLinObject = null;
        private IVCExprOpVisitor<Z3TermAst, LineariserOptions> OpLineariser
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
        internal readonly Dictionary<VCExprVar, Z3TermAst> letBindings;
        protected Z3Context cm;

        public Z3apiExprLineariser(Z3Context cm, UniqueNamer namer)
        {
            this.cm = cm;
            this.namer = namer;
            this.letBindings = new Dictionary<VCExprVar, Z3TermAst>();
        }

        public Z3TermAst Linearise(VCExpr expr, LineariserOptions options)
        {
            Contract.Requires(options != null);
            Contract.Requires(expr != null);
            return expr.Accept<Z3TermAst, LineariserOptions>(this, options);
        }

        /////////////////////////////////////////////////////////////////////////////////////

        public Z3TermAst Visit(VCExprLiteral node, LineariserOptions options)
        {
            Contract.Requires(options != null);
            Contract.Requires(node != null);

            if (node == VCExpressionGenerator.True)
                return cm.MakeTrue();
            else if (node == VCExpressionGenerator.False)
                return cm.MakeFalse();
            else if (node is VCExprIntLit)
                return cm.MakeIntLiteral(((VCExprIntLit)node).Val.ToString());
            else
            {
                Contract.Assert(false);
                throw new cce.UnreachableException();
            }
        }

        public Z3TermAst Visit(VCExprNAry node, LineariserOptions options)
        {
            Contract.Requires(options != null);
            Contract.Requires(node != null);
            VCExprOp op = node.Op;
            Contract.Assert(op != null);

            if (op.Equals(VCExpressionGenerator.AndOp) || op.Equals(VCExpressionGenerator.OrOp))
            {
                // handle these operators without recursion
                List<Z3TermAst> asts = new List<Z3TermAst>();
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

            return node.Accept<Z3TermAst, LineariserOptions>(OpLineariser, options);
        }

        public Z3TermAst Visit(VCExprVar node, LineariserOptions options)
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

        public Z3TermAst Visit(VCExprQuantifier node, LineariserOptions options)
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
                List<Z3PatternAst> patterns;
                List<Z3TermAst> no_patterns;
                VisitTriggers(node.Triggers, options, out patterns, out no_patterns);
                Z3TermAst body = Linearise(node.Body, options);
                Z3TermAst result;
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
                    case Quantifier.ALL:
                        result = cm.MakeQuantifier(true, weight, qid, skolemid, varNames, varTypes, patterns, no_patterns, body); break;
                    case Quantifier.EX:
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

        private void VisitTriggers(List<VCTrigger> triggers, LineariserOptions options, out List<Z3PatternAst> patterns, out List<Z3TermAst> no_patterns)
        {
            patterns = new List<Z3PatternAst>();
            no_patterns = new List<Z3TermAst>();
            foreach (VCTrigger trigger in triggers)
            {
                List<Z3TermAst> exprs = new List<Z3TermAst>();
                foreach (VCExpr expr in trigger.Exprs)
                {
                    System.Diagnostics.Debug.Assert(expr != null);
                    Z3TermAst termAst = Linearise(expr, options);
                    exprs.Add(termAst);
                }
                if (exprs.Count > 0)
                {
                    if (trigger.Pos)
                    {
                        Z3PatternAst pattern = cm.MakePattern(exprs);
                        patterns.Add(pattern);
                    }
                    else
                    {
                        System.Diagnostics.Debug.Assert(false, "Z3api currently does not handle nopats");
                        foreach (Z3TermAst expr in exprs)
                            no_patterns.Add(expr);
                    }
                }
            }
        }

        public Z3TermAst Visit(VCExprLet node, LineariserOptions options)
        {
            foreach (VCExprLetBinding b in node)
            {
                Z3TermAst defAst = Linearise(b.E, options);
                letBindings.Add(b.V, defAst);
            }
            Z3TermAst letAst = Linearise(node.Body, options);
            foreach (VCExprLetBinding b in node)
            {
                letBindings.Remove(b.V);
            }
            return letAst;
        }  

        /////////////////////////////////////////////////////////////////////////////////////

        internal class Z3apiOpLineariser : IVCExprOpVisitor<Z3TermAst, LineariserOptions>
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

            private Z3TermAst WriteApplication(string op, IEnumerable<VCExpr> terms, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(op != null);
                Contract.Requires(cce.NonNullElements(terms));

                List<Z3TermAst> args = new List<Z3TermAst>();
                foreach (VCExpr e in terms)
                {
                    Contract.Assert(e != null);
                    args.Add(ExprLineariser.Linearise(e, options));
                }
                return ExprLineariser.cm.Make(op, args);
            }

            ///////////////////////////////////////////////////////////////////////////////////

            public Z3TermAst VisitNotOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("NOT", node, options);
            }

            public Z3TermAst VisitEqOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("EQ", node, options);
            }

            public Z3TermAst VisitNeqOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("NEQ", node, options);
            }

            public Z3TermAst VisitAndOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("AND", node, options);  
            }

            public Z3TermAst VisitOrOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("OR", node, options); 
            }

            public Z3TermAst VisitImpliesOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                if (options.InverseImplies)
                {
                    List<Z3TermAst> args = new List<Z3TermAst>();

                    args.Add(ExprLineariser.Linearise(node[1], options));
                    List<Z3TermAst> t = new List<Z3TermAst>();
                    t.Add(ExprLineariser.Linearise(node[0], options));
                    args.Add(ExprLineariser.cm.Make("NOT", t));
                    return ExprLineariser.cm.Make("OR", args);
                }
                else
                {
                    return WriteApplication("IMPLIES", node, options);
                }
            }

            public Z3TermAst VisitDistinctOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);

                if (node.Length < 2)
                {
                    return ExprLineariser.Linearise(VCExpressionGenerator.True, options);
                }
                else
                {
                    List<Z3TermAst> args = new List<Z3TermAst>();
                    foreach (VCExpr e in node)
                    {
                        Contract.Assert(e != null);
                        args.Add(ExprLineariser.Linearise(e, options));
                    }
                    return ExprLineariser.cm.Make("DISTINCT", args);
                }
            }

            public Z3TermAst VisitLabelOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                VCExprLabelOp op = (VCExprLabelOp)node.Op;
                Contract.Assert(op != null);
                return ExprLineariser.cm.MakeLabel(op.label, op.pos, ExprLineariser.Linearise(node[0], options)); 
            }

            public Z3TermAst VisitSelectOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                List<Z3TermAst> args = new List<Z3TermAst>();
                foreach (VCExpr e in node)
                {
                    Contract.Assert(e != null);
                    args.Add(ExprLineariser.Linearise(e, options));
                }
                return ExprLineariser.cm.MakeArraySelect(args);
                // return ExprLineariser.cm.Make(SimplifyLikeExprLineariser.SelectOpName(node), args);
            }

            public Z3TermAst VisitStoreOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                List<Z3TermAst> args = new List<Z3TermAst>();
                foreach (VCExpr e in node)
                {
                    Contract.Assert(e != null);
                    args.Add(ExprLineariser.Linearise(e, options));
                }
                return ExprLineariser.cm.MakeArrayStore(args);
                // return ExprLineariser.cm.Make(SimplifyLikeExprLineariser.StoreOpName(node), args);
            }

            public Z3TermAst VisitBvOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("$make_bv" + node.Type.BvBits, node, options);
            }

            public Z3TermAst VisitBvExtractOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication(SimplifyLikeExprLineariser.BvExtractOpName(node), node, options);
            }

            public Z3TermAst VisitBvConcatOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication(SimplifyLikeExprLineariser.BvConcatOpName(node), node, options);
            }

            public Z3TermAst VisitIfThenElseOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);

                List<Z3TermAst> args = new List<Z3TermAst>();
                args.Add(ExprLineariser.Linearise(node[0], options));
                args.Add(ExprLineariser.Linearise(node[1], options));
                args.Add(ExprLineariser.Linearise(node[2], options));
                return ExprLineariser.cm.Make("ITE", args);
            }

            public Z3TermAst VisitCustomOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(node != null);
                Contract.Requires(options != null);
                VCExprCustomOp op = (VCExprCustomOp)node.Op;
                List<Z3TermAst> args = new List<Z3TermAst>();
                foreach (VCExpr arg in node)
                {
                    args.Add(ExprLineariser.Linearise(arg, options));
                }
                return ExprLineariser.cm.Make(op.Name, args);
            }

            public Z3TermAst VisitAddOp(VCExprNAry node, LineariserOptions options)
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

            public Z3TermAst VisitSubOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("-", node, options);
            }

            public Z3TermAst VisitMulOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("*", node, options);
            }

            public Z3TermAst VisitDivOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("/", node, options);
            }

            public Z3TermAst VisitModOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("%", node, options);
            }

            public Z3TermAst VisitLtOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("<", node, options);
            }

            public Z3TermAst VisitLeOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("<=", node, options);
            }

            public Z3TermAst VisitGtOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication(">", node, options);
            }

            public Z3TermAst VisitGeOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication(">=", node, options);
            }

            public Z3TermAst VisitSubtypeOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("<:", node, options);
            }

            public Z3TermAst VisitSubtype3Op(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                return WriteApplication("<::", node, options);
            }

            public Z3TermAst VisitBoogieFunctionOp(VCExprNAry node, LineariserOptions options)
            {
                Contract.Requires(options != null);
                Contract.Requires(node != null);
                VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp)node.Op;
                Contract.Assert(op != null);
                string funcName = op.Func.Name;
                Contract.Assert(funcName != null);
                string bvzName = op.Func.FindStringAttribute("external");
                if (bvzName != null) funcName = bvzName;

                List<Z3TermAst> args = new List<Z3TermAst>();
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
