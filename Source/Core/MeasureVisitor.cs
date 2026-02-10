using System.Collections.Generic;
using Microsoft.BaseTypes;

namespace Microsoft.Boogie
{
  public class MeasureVisitor : StandardVisitor
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

            // fix this
            // if(callCmd.Proc.Measure)
            // {
            // new AssertCmd(callCmd.tok, null, new DecreasesRecursiveDescription()));
            //somehow make this work
            // }
            foreach (var mes in callCmd.Proc.Measure)
            {
              var ass = new AssertCmd(
                cmd.tok,
                Expr.Lt(mes.Condition, node.Proc.Measure[count].Condition), new MeasureDescription()
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
