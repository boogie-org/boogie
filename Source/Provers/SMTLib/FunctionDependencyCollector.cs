using System.Collections.Generic;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.SMTLib;

public class FunctionDependencyCollector : BoundVarTraversingVCExprVisitor<bool, bool>
{
  private List<Function> functionList;

  // not used but required by interface
  protected override bool StandardResult(VCExpr node, bool arg)
  {
    return true;
  }

  public List<Function> Collect(VCExpr expr)
  {
    functionList = new List<Function>();
    Traverse(expr, true);
    return functionList;
  }

  public override bool Visit(VCExprNAry node, bool arg)
  {
    VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
    if (op != null)
    {
      functionList.Add(op.Func);
    }

    return base.Visit(node, arg);
  }
}