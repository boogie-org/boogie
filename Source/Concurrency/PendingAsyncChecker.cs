using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    public static class PendingAsyncChecker
    {
        public static void AddCheckers(CivlTypeChecker ctc)
        {
            foreach (var action in ctc.AllActions.Where(a => a.HasPendingAsyncs))
            {
                var requires = action.gate.Select(g => new Requires(false, g.Expr)).ToList();
                var cmds = new List<Cmd>
                {
                    CmdHelper.CallCmd(
                        action.proc,
                        action.impl.InParams.Select(Expr.Ident).ToList<Expr>(),
                        action.impl.OutParams.Select(Expr.Ident).ToList())
                };
                var blocks = new List<Block>() { new Block(Token.NoToken, "init", cmds, CmdHelper.ReturnCmd) };

                var PAs = Expr.Ident(action.impl.OutParams.Last(p => p.TypedIdent.Type.Equals(ctc.pendingAsyncMultisetType)));
                var paBound = VarHelper.BoundVariable("pa", ctc.pendingAsyncType);
                var pa = Expr.Ident(paBound);

                var nonnegativeExpr =
                    new ForallExpr(Token.NoToken, new List<Variable> { paBound },
                        Expr.Ge(Expr.Select(PAs, pa), Expr.Literal(0)));
                var correctTypeExpr = new ForallExpr(Token.NoToken, new List<Variable> { paBound },
                    Expr.Imp(
                        Expr.Gt(Expr.Select(PAs, pa), Expr.Literal(0)),
                        Expr.Or(action.pendingAsyncs.Select(a => ExprHelper.FunctionCall(a.pendingAsyncCtor.membership, pa)))));
                var ensures = new List<Ensures> {
                    new Ensures(false, nonnegativeExpr) { ErrorData = $"Action {action.proc.Name} might create negative pending asyncs" },
                    new Ensures(false, correctTypeExpr) { ErrorData = $"Action {action.proc.Name} might create undeclared pending asyncs" },
                };

                CivlUtil.ResolveAndTypecheck(ensures);

                var proc = new Procedure(Token.NoToken, $"PendingAsyncChecker_{action.proc.Name}", new List<TypeVariable>(),
                    action.impl.InParams, action.impl.OutParams,
                    requires, action.proc.Modifies, ensures);
                var impl = new Implementation(Token.NoToken, proc.Name, proc.TypeParameters,
                    proc.InParams, proc.OutParams, new List<Variable>(), blocks)
                    { Proc = proc };

                ctc.program.AddTopLevelDeclaration(proc);
                ctc.program.AddTopLevelDeclaration(impl);
            }
        }
    }
}
