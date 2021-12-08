using System.Collections.Generic;

namespace Microsoft.Boogie
{
  internal class BlocksVisitor : DependencyEvaluator
  {
    public List<Block> Blocks;

    public BlocksVisitor(List<Block> blocks) : base(null)
    {
      Blocks = blocks;
    }

    public override Expr VisitExpr(Expr node)
    {
      if (node is IdentifierExpr iExpr && iExpr.Decl is Constant c) {
        AddOutgoing(c);
      } else if (node is NAryExpr e && e.Fun is FunctionCall f) {
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