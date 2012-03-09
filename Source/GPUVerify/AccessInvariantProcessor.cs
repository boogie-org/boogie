using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{
    class AccessInvariantProcessor : StandardVisitor
    {

        private const string NO_READ = "__no_read_";
        private const string NO_WRITE = "__no_write_";
        private const string READ = "__read_";
        private const string WRITE = "__write_";
        private const string READ_OFFSET = "__read_offset_";
        private const string WRITE_OFFSET = "__write_offset_";
        private const string READ_IMPLIES = "__read_implies_";
        private const string WRITE_IMPLIES = "__write_implies_";

        public override Expr VisitNAryExpr(NAryExpr node)
        {

            if (node.Fun is FunctionCall)
            {
                FunctionCall call = node.Fun as FunctionCall;

                if (MatchesIntrinsic(call.Func, NO_READ))
                {
                    return Expr.Not(
                        MakeReadHasOccurred(node, call, NO_READ)
                    );
                }

                if (MatchesIntrinsic(call.Func, NO_WRITE))
                {
                    return Expr.Not(
                        MakeWriteHasOccurred(node, call, NO_WRITE)
                    );
                }

                if (MatchesIntrinsic(call.Func, READ_OFFSET))
                {
                    return new IdentifierExpr(node.tok, new GlobalVariable(
                            node.tok, new TypedIdent(node.tok, "_READ_OFFSET_X_" +
                                call.Func.Name.Substring(READ_OFFSET.Length), Microsoft.Boogie.Type.GetBvType(32)))
                    );
                }

                if (MatchesIntrinsic(call.Func, WRITE_OFFSET))
                {
                    return new IdentifierExpr(node.tok, new GlobalVariable(
                            node.tok, new TypedIdent(node.tok, "_WRITE_OFFSET_X_" +
                                call.Func.Name.Substring(WRITE_OFFSET.Length), Microsoft.Boogie.Type.GetBvType(32)))
                    );
                }

                if (MatchesIntrinsic(call.Func, READ))
                {
                    return MakeReadHasOccurred(node, call, READ);
                }

                if (MatchesIntrinsic(call.Func, WRITE))
                {
                    return MakeWriteHasOccurred(node, call, WRITE);
                }

                if (MatchesIntrinsic(call.Func, READ_IMPLIES))
                {
                    return Expr.Imp(MakeReadHasOccurred(node, call, READ_IMPLIES), node.Args[0]);
                }

                if (MatchesIntrinsic(call.Func, WRITE_IMPLIES))
                {
                    return Expr.Imp(MakeWriteHasOccurred(node, call, WRITE_IMPLIES), node.Args[0]);
                }

            }

            return base.VisitNAryExpr(node);
        }

        private static IdentifierExpr MakeReadHasOccurred(NAryExpr node, FunctionCall call, string intrinsicPrefix)
        {
            return new IdentifierExpr(node.tok, new GlobalVariable(
                                        node.tok, new TypedIdent(node.tok, "_READ_HAS_OCCURRED_" +
                                            call.Func.Name.Substring(intrinsicPrefix.Length), Microsoft.Boogie.Type.Bool)));
        }

        private static IdentifierExpr MakeWriteHasOccurred(NAryExpr node, FunctionCall call, string intrinsicPrefix)
        {
            return new IdentifierExpr(node.tok, new GlobalVariable(
                                        node.tok, new TypedIdent(node.tok, "_WRITE_HAS_OCCURRED_" +
                                            call.Func.Name.Substring(intrinsicPrefix.Length), Microsoft.Boogie.Type.Bool)));
        }


        private bool MatchesIntrinsic(Function function, string intrinsicPrefix)
        {
            return function.Name.Length > intrinsicPrefix.Length &&
                function.Name.Substring(0, intrinsicPrefix.Length).Equals(intrinsicPrefix);
        }
    
    
    }
}
