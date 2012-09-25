using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie
{
  class GetThenOfIfThenElseVisitor : StandardVisitor
  {
    LiteralExpr result;

    internal GetThenOfIfThenElseVisitor()
    {
      result = null;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is IfThenElse)
      {
        if (node.Args[1] is LiteralExpr)
        {
          Debug.Assert(result == null);
          result = (LiteralExpr)node.Args[1];
        }
      }
      return base.VisitNAryExpr(node);
    }

    internal LiteralExpr getResult()
    {
      Debug.Assert(result != null);
      return result;
    }
  }
}
