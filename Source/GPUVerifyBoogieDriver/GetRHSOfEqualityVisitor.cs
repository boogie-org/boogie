using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie
{
  class GetRHSOfEqualityVisitor : StandardVisitor
  {

    string LHSPattern;
    Expr result;

    internal GetRHSOfEqualityVisitor(string LHSPattern)
    {
      this.LHSPattern = LHSPattern;
      result = null;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is BinaryOperator && ((BinaryOperator)node.Fun).Op == BinaryOperator.Opcode.Eq)
      {
        if (node.Args[0] is IdentifierExpr && Regex.IsMatch(((IdentifierExpr)node.Args[0]).Decl.Name, LHSPattern))
        {
          Debug.Assert(result == null);
          result = node.Args[1];
        }
      }
      return base.VisitNAryExpr(node);
    }

    internal Expr getResult()
    {
      Debug.Assert(result != null);
      return result;
    }

  }
}
