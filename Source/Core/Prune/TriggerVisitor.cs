using System.Collections.Generic;

namespace Microsoft.Boogie
{
  class TriggerVisitor : ReadOnlyVisitor
  {
    public readonly ISet<Declaration> Declarations = new HashSet<Declaration>();

    public override Expr VisitExpr(Expr node)
    {
      if (node is IdentifierExpr iExpr && iExpr.Decl is Constant c) {
        Declarations.Add(c);
      } else if (node is NAryExpr e && e.Fun is FunctionCall f) {
        Declarations.Add(f.Func);
      }
      return base.VisitExpr(node);
    }
  }
}