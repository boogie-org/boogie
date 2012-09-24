using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie
{
  class GetIfOfIfThenElseVisitor : StandardVisitor
  {
    IdentifierExpr result;

    internal GetIfOfIfThenElseVisitor()
    {
      result = null;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is IfThenElse)
      {
        if (node.Args[0] is IdentifierExpr)
        {
          Debug.Assert(result == null);
          result = node.Args[0] as IdentifierExpr;
        }
        else if (node.Args[0] is NAryExpr)
        {
          Debug.Assert(result == null);
          result = ExtractEnabledArg((NAryExpr)node.Args[0]);
        }
      }
      return base.VisitNAryExpr(node);
    }

    internal IdentifierExpr getResult()
    {
      Debug.Assert(result != null);
      return result;
    }

    internal IdentifierExpr ExtractEnabledArg(NAryExpr ne) 
    {
      if (ne.Args[0] is IdentifierExpr)
      {
        return (IdentifierExpr)ne.Args[0];
      }
      else if (ne.Args[0] is NAryExpr)
      {
        return ExtractEnabledArg((NAryExpr)ne.Args[0]);
      }
      else
      {
        Debug.Assert(false, "ExtractEnabledArg: not all cases covered");
        return null;
      }
    }
  }
}
