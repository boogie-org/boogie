using System.Collections.Generic;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.BaseTypes;
using System.Threading;
namespace Microsoft.Boogie;

public class MeasureVisitor : StandardVisitor
{
  public override Procedure VisitProcedure(Procedure node)
  {
    // find all measure and add precondition
    foreach (var dec in node.Measure)
    { 
      var condition = dec.Condition;
      Expr zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
      var condition2 = Expr.Gt(condition, zero);
      var req = new Requires(Token.NoToken, true, condition2, "hello");
      node.Requires.Add(req);
    }
    return base.VisitProcedure(node);
  }

  
  public override Implementation VisitImplementation(Implementation node)
  {
    // procedure with at least one measure, visit it's body and add assertions
    // look up node.Proc 
    
    var newBlockList = new List<Block>();
    
    foreach(var block in node.Blocks)
    {
      var newblock = new Block(Token.NoToken, null);
      foreach(var cmd in block.Cmds)
      {
        if (cmd is CallCmd callCmd)
        {
        var count =0;
          foreach(var dec2 in callCmd.Proc.Measure)
          {
            AssertCmd ass = new AssertCmd(Token.NoToken, Expr.Lt(dec2.Condition, node.Proc.Measure[count].Condition));
             newblock.Cmds.Add(ass);
             count++;
        }
        }
    }
    newBlockList.Add(newblock);
    }

   node.Blocks = newBlockList;
   Console.WriteLine("hello");



    Console.WriteLine(node);
    return base.VisitImplementation(node);
  }

  // public void VisitImplementation(Implementation impl)
  // {
  //   throw new NotImplementedException();
  // }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      VisitProcedure(node.Proc);
      return base.VisitCallCmd(node);
    }

  //  private AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
  //   {


  //   }

  // public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
  // {
  //   // descends into VisitCallCmd;
  //   // introduce newCmdSeq in which we create a newCmdSeq = same ;insert assertion; insert call;
  //   // return newCmdSeq
  //   return base.VisitCmdSeq(cmdSeq);
  // }
}

/*
A 
measure x, y;
{

call B;
}

B measure y

*/