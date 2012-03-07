using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{
    class EnabledToPredicateVisitor : StandardVisitor
    {

        public EnabledToPredicateVisitor(TypedIdent currentPredicate)
        {
            this.currentPredicate = currentPredicate;

        }

        private TypedIdent currentPredicate;


        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (node.Fun is FunctionCall)
            {
                FunctionCall call = node.Fun as FunctionCall;

                if (call.Func.Name.Equals("__enabled"))
                {
                    return new IdentifierExpr(node.tok, new LocalVariable(node.tok, currentPredicate));
                }

            }

            return base.VisitNAryExpr(node);
        }

    }
}
