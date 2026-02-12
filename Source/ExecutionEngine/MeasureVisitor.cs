using System;
using System.Linq;
using System.Collections;
using System.Diagnostics;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;
using Microsoft.Boogie.GraphUtil;
using System.Collections.Concurrent;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using VC;
using System.Runtime.Caching;
using VCGeneration;
using System.Reflection;
using System.ComponentModel.DataAnnotations;

namespace Microsoft.Boogie
{
  public sealed class MeasureVisitor : StandardVisitor
  {
    public override Procedure VisitProcedure(Procedure node)
    {
      foreach (var mes in node.Measure)
      {
        var condition = mes.Condition;
        Expr zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
        var condition2 = Expr.Gt(condition, zero);
        var req = new Requires(node.tok, true, condition2, "");
        node.Requires.Add(req);
      }

      return base.VisitProcedure(node);
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      var newBlockList = new List<Block>();

      foreach (var block in node.Blocks)
      {
        var newBlock = new Block(Token.NoToken, null);

        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd)
          {
            var count = 0;

            foreach (var mes in callCmd.Proc.Measure)
            {
              var ass = new AssertCmd(
                cmd.tok,
                Expr.Lt(mes.Condition, node.Proc.Measure[count].Condition),
                new MeasureDescription()
              );

              newBlock.Cmds.Add(ass);
              count++;
            }
          }
        }

        newBlockList.Add(newBlock);
      }

      node.Blocks = newBlockList;
      return base.VisitImplementation(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      VisitProcedure(node.Proc);
      return base.VisitCallCmd(node);
    }

  }
}
