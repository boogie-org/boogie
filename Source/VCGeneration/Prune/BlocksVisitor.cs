using System.Collections.Generic;

namespace Microsoft.Boogie
{
  internal class BlocksVisitor : DependencyEvaluator
  {
    public List<Block> Blocks;
    public HashSet<Variable> RelVars;

    public BlocksVisitor(List<Block> blocks) : base(null)
    {
      Blocks = blocks;
      RelVars = new HashSet<Variable>();
    }

    public override Variable VisitVariable(Variable v) {
      RelVars.Add(v);
      return base.VisitVariable(v);
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

    public override Cmd VisitAssumeCmd(AssumeCmd ac) {
      if (Prune.GetWhereVariable(ac) != null) {
        var cacheVars = new HashSet<Variable> (RelVars);
        var ex = base.VisitAssumeCmd(ac);
        this.RelVars = cacheVars;
        return ex;
      } else {
        return base.VisitAssumeCmd(ac);
      }
    }

    public override Boogie.Type VisitType(Boogie.Type node)
    {
      types.Add(node);
      return base.VisitType(node);
    }
  }
}