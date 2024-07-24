using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class MutableVariableCollector : ReadOnlyVisitor
{
  public HashSet<Variable> UsedVariables = new HashSet<Variable>();

  public void AddUsedVariables(HashSet<Variable> usedVariables)
  {
    Contract.Requires(usedVariables != null);

    foreach (var v in usedVariables)
    {
      UsedVariables.Add(v);
    }
  }

  public override Expr VisitIdentifierExpr(IdentifierExpr node)
  {
    Contract.Ensures(Contract.Result<Expr>() != null);

    if (node.Decl != null && node.Decl.IsMutable)
    {
      UsedVariables.Add(node.Decl);
    }

    return base.VisitIdentifierExpr(node);
  }
}