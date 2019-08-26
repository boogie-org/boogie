using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Boogie
{
    public class CivlUtil
    {
        public static void AddInlineAttribute(Declaration decl)
        {
            decl.AddAttribute("inline", Expr.Literal(1));
        }
    }

    // Handy syntactic suggar missing in Expr
    public static class ExprHelper
    {
        public static NAryExpr FunctionCall(Function f, params Expr[] args)
        {
            return new NAryExpr(Token.NoToken, new FunctionCall(f), args);
        }

        public static NAryExpr IfThenElse(Expr ifExpr, Expr thenExpr, Expr elseExpr)
        {
            return new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken),
                new Expr[] { ifExpr, thenExpr, elseExpr });
        }

        public static OldExpr Old(Expr expr)
        {
            return new OldExpr(Token.NoToken, expr);
        }
    }
}
