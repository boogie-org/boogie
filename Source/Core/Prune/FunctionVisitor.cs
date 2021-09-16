namespace Microsoft.Boogie
{
  internal class FunctionVisitor : DependencyEvaluator
  {
    public FunctionVisitor(Function func) : base(func)
    {
      incoming.Add(func);
    }

    public override Expr VisitExpr(Expr node)
    {
      if (node is IdentifierExpr iExpr && iExpr.Decl is Constant c)
      {
        outgoing.Add(c);
      }
      else if (node is NAryExpr e && e.Fun is FunctionCall f)
      {
        outgoing.Add(f.Func);
      }
      return base.VisitExpr(node);
    }
    public override Boogie.Type VisitType(Boogie.Type node)
    {
      types.Add(node);
      return base.VisitType(node);
    }
  }
}