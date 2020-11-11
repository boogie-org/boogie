using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public static class PendingAsyncChecker
  {
    public static void AddCheckers(CivlTypeChecker civlTypeChecker)
    {
      foreach (var action in civlTypeChecker.AllAtomicActions.Where(a => a.HasPendingAsyncs))
      {
        var requires = action.gate.Select(g => new Requires(false, g.Expr)).ToList();

        var PAs = Expr.Ident(action.impl.OutParams.Last(p => p.TypedIdent.Type.Equals(civlTypeChecker.pendingAsyncMultisetType)));
        var paBound = civlTypeChecker.BoundVariable("pa", civlTypeChecker.pendingAsyncType);
        var pa = Expr.Ident(paBound);

        var nonnegativeExpr =
          ExprHelper.ForallExpr(new List<Variable> {paBound},
            Expr.Ge(Expr.Select(PAs, pa), Expr.Literal(0)));
        var correctTypeExpr = ExprHelper.ForallExpr(new List<Variable> {paBound},
          Expr.Imp(
            Expr.Gt(Expr.Select(PAs, pa), Expr.Literal(0)),
            Expr.Or(action.pendingAsyncs.Select(a => ExprHelper.FunctionCall(a.pendingAsyncCtor.membership, pa)))));

        CivlUtil.ResolveAndTypecheck(nonnegativeExpr);
        CivlUtil.ResolveAndTypecheck(correctTypeExpr);

        var cmds = new List<Cmd>
        {
          CmdHelper.CallCmd(
            action.proc,
            action.impl.InParams.Select(Expr.Ident).ToList<Expr>(),
            action.impl.OutParams.Select(Expr.Ident).ToList()),
          CmdHelper.AssertCmd(
            action.proc.tok,
            nonnegativeExpr,
            $"Action {action.proc.Name} might create negative pending asyncs"),
          CmdHelper.AssertCmd(
            action.proc.tok,
            correctTypeExpr,
            $"Action {action.proc.Name} might create undeclared pending asyncs")
        };
        var blocks = new List<Block>() { BlockHelper.Block("init", cmds) };

        var proc = DeclHelper.Procedure(civlTypeChecker.AddNamePrefix($"PendingAsyncChecker_{action.proc.Name}"),
          action.impl.InParams, action.impl.OutParams,
          requires, action.proc.Modifies, new List<Ensures>());
        var impl = DeclHelper.Implementation(proc, proc.InParams, proc.OutParams, new List<Variable>(), blocks);

        civlTypeChecker.program.AddTopLevelDeclaration(proc);
        civlTypeChecker.program.AddTopLevelDeclaration(impl);
      }
    }
  }
}