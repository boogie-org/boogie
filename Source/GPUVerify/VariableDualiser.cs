using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

using System.Diagnostics;

namespace GPUVerify
{
    class VariableDualiser : Duplicator
    {
        private int id;
        private UniformityAnalyser uniformityAnalyser;
        private string procName;

        public VariableDualiser(int id, UniformityAnalyser uniformityAnalyser, string procName)
        {
            Debug.Assert((uniformityAnalyser == null && procName == null)
                || (uniformityAnalyser != null && procName != null));

            this.id = id;
            this.uniformityAnalyser = uniformityAnalyser;
            this.procName = procName;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (!(node.Decl is Constant))
            {
                return new IdentifierExpr(node.tok, new LocalVariable(node.tok, DualiseTypedIdent(node.Decl)));
            }

            if (GPUVerifier.IsThreadLocalIdConstant(node.Decl))
            {
                return new IdentifierExpr(node.tok, new Constant(node.tok, DualiseTypedIdent(node.Decl)));
            }

            if (CommandLineOptions.InterGroupRaceChecking && GPUVerifier.IsGroupIdConstant(node.Decl))
            {
                return new IdentifierExpr(node.tok, new Constant(node.tok, DualiseTypedIdent(node.Decl)));
            }

            return node;
        }

        private TypedIdent DualiseTypedIdent(Variable v)
        {

            if (uniformityAnalyser == null || !uniformityAnalyser.IsUniform(procName, v.Name))
            {
                return new TypedIdent(v.tok, v.Name + "$" + id, v.TypedIdent.Type);
            }

            return new TypedIdent(v.tok, v.Name, v.TypedIdent.Type);
        }

        public override Variable VisitVariable(Variable node)
        {
            if (!(node is Constant) || GPUVerifier.IsThreadLocalIdConstant(node) ||
                (CommandLineOptions.InterGroupRaceChecking && GPUVerifier.IsGroupIdConstant(node)))
            {
                node.TypedIdent = DualiseTypedIdent(node);
                node.Name = node.Name + "$" + id;
                return node;
            }

            return base.VisitVariable(node);
        }


        public override Expr VisitNAryExpr(NAryExpr node)
        {
            // The point of this override is to avoid dualisation of certain special
            // intrinsics that are cross-thread

            if (node.Fun is FunctionCall)
            {
                FunctionCall call = node.Fun as FunctionCall;

                if (call.Func.Name.Equals("__other_bool") || call.Func.Name.Equals("__other_bv32"))
                {
                    Debug.Assert(id == 1 || id == 2);
                    int otherId = id == 1 ? 2 : 1;
                    return new VariableDualiser(otherId, uniformityAnalyser, procName).VisitExpr(
                        node.Args[0]);
                }

            }

            return base.VisitNAryExpr(node);
        }


    }

}
