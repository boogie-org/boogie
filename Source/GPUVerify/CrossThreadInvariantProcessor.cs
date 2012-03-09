using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{
    class CrossThreadInvariantProcessor : StandardVisitor
    {

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            
            if (node.Fun is FunctionCall)
            {
                FunctionCall call = node.Fun as FunctionCall;

                if (call.Func.Name.Equals("__uniform_bv32") || call.Func.Name.Equals("__uniform_bool"))
                {
                    return Expr.Eq(new VariableDualiser(1).VisitExpr(node.Args[0].Clone() as Expr),
                                   new VariableDualiser(2).VisitExpr(node.Args[0].Clone() as Expr));
                }

                if (call.Func.Name.Equals("__distinct_bv32") || call.Func.Name.Equals("__distinct_bool"))
                {
                    return Expr.Neq(new VariableDualiser(1).VisitExpr(node.Args[0].Clone() as Expr),
                                   new VariableDualiser(2).VisitExpr(node.Args[0].Clone() as Expr));
                }

                if (call.Func.Name.Equals("__all"))
                {
                    return Expr.And(new VariableDualiser(1).VisitExpr(node.Args[0].Clone() as Expr),
                                   new VariableDualiser(2).VisitExpr(node.Args[0].Clone() as Expr));
                }

                if (call.Func.Name.Equals("__at_most_one"))
                {
                    return Expr.Not(Expr.And(new VariableDualiser(1).VisitExpr(node.Args[0].Clone() as Expr),
                                   new VariableDualiser(2).VisitExpr(node.Args[0].Clone() as Expr)));
                }


            }

            return base.VisitNAryExpr(node);
        }



    }
}
