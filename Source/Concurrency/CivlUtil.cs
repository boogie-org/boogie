using System;
using System.Collections.Generic;
using System.Linq;
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

    public static class CmdHelper
    {
        public static ReturnCmd ReturnCmd => new ReturnCmd(Token.NoToken);

        public static CallCmd CallCmd(Procedure callee, List<Expr> ins, List<IdentifierExpr> outs)
        {
            return new CallCmd(Token.NoToken, callee.Name, ins, outs)
            { Proc = callee };
        }

        public static AssumeCmd AssumeCmd(Expr expr)
        {
            return new AssumeCmd(Token.NoToken, expr);
        }
    }

    public static class VarHelper
    {
        public static LocalVariable LocalVariable(string name, Type type)
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, type));
        }

        public static BoundVariable BoundVariable(string name, Type type)
        {
            return new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, type));
        }

        public static Formal Formal(string name, Type type, bool incoming)
        {
            return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, name, type), incoming);
        }
    }

    public static class LinqExtensions
    {
        public static IEnumerable<IEnumerable<T>> CartesianProduct<T>(this IEnumerable<IEnumerable<T>> sequences)
        {
            IEnumerable<IEnumerable<T>> emptyProduct = new[] { Enumerable.Empty<T>() };
            return sequences.Aggregate(
                emptyProduct,
                (accumulator, sequence) =>
                from acc in accumulator
                from item in sequence
                select acc.Concat(new[] { item }));
        }
    }
}
