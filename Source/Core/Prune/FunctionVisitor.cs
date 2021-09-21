namespace Microsoft.Boogie
{
  internal class FunctionVisitor : DependencyEvaluator
  {
    public FunctionVisitor(Function func) : base(func)
    {
    }
    
    public static DependencyEvaluator GetFunctionDependencies(Function function)
    {
      var result = new FunctionVisitor(function);
      result.Visit(function);
      return result;
    }

    public override Expr VisitExpr(Expr node)
    {
      if (node is IdentifierExpr iExpr && iExpr.Decl is Constant c)
      {
        AddOutgoing(c);
      }
      else if (node is NAryExpr e && e.Fun is FunctionCall f)
      {
        AddOutgoing(f.Func);
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