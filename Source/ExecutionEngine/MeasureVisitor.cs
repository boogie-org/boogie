using System.Collections.Generic;
using System.IO;
using Microsoft.Boogie.GraphUtil;
using Microsoft.BaseTypes;
using System;

namespace Microsoft.Boogie
{
  public class MeasureVisitor : StandardVisitor
  {
    internal static string GetFileNameForConsole(ExecutionEngineOptions options, string filename)
    {
      return options.UseBaseNameForFileName && !string.IsNullOrEmpty(filename) &&
             filename != "<console>"
        ? Path.GetFileName(filename)
        : filename;
    }

    protected Graph<Implementation> callGraph;

    public MeasureVisitor(
      Program program,
      ExecutionEngineOptions Options,
      CivlTypeChecker civlTypeChecker,
      string bplFileName)
    {
      callGraph = Program.BuildTransitiveCallGraph(Options, program);
      // protected Graph<Implementation> callGraph = Program.BuildCallGraph(Options, program);

      foreach (var edge in callGraph.Edges)
      {
        if (edge.Item1 == edge.Item2)
        {
          var proc = edge.Item1?.Proc;
          if (proc.Measure.Count == 0)
          {
            Options.OutputWriter.WriteLine(
              "Recursive calls should have measure annotation.",
              civlTypeChecker.checkingContext.ErrorCount,
              GetFileNameForConsole(Options, bplFileName)
            );
          }
        }
      }

      foreach (var proc in program.Procedures)
      {
        VisitProcedure(proc);
      }

      foreach (var impl in program.Implementations)
      {
        VisitImplementation2(impl, program);
      }
    }

    public override Procedure VisitProcedure(Procedure node)
    {
      foreach (var mes in node.Measure)
      {
        var condition = mes.Condition;
        Expr zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
        var condition2 = Expr.Gt(condition, zero);
        var req = new Requires(node.tok, false, condition2, "");
        node.Requires.Add(req);
      }

      return base.VisitProcedure(node);
    }

    public Implementation VisitImplementation2(Implementation node, Program program)
{
  var newBlockList = new List<Block>();

  foreach (var block in node.Blocks)
  {
    var newBlock = new Block(Token.NoToken, null);

    foreach (var cmd in block.Cmds)
    {
      if (cmd is CallCmd callCmd)
      {
        foreach (var impl in program.Implementations)
        {
          if (impl.Proc == callCmd.Proc)
          {
            foreach (var edge in callGraph.Edges)
            {
              if (edge.Item1 == impl && edge.Item2 == node)
              {
                Console.WriteLine("wohoo");
              }
            }
          }
        }

        Expr storeExprEqual = Expr.True;
        Expr Expr3 = Expr.False;
        var count = 0;

        foreach (var mes in callCmd.Proc.Measure)
        {
          var Expr1 = Expr.Lt(
            mes.Condition,
            node.Proc.Measure[count].Condition
          );

          Expr3 = Expr.Or(Expr.And(Expr1, storeExprEqual), Expr3);

          storeExprEqual = Expr.And(
            storeExprEqual,
            Expr.Eq(mes.Condition, node.Proc.Measure[count].Condition)
          );

          count++; //
        }

        var ass = new AssertCmd(node.tok, Expr3, new MeasureDescription(), null);
        newBlock.Cmds.Add(ass);
      }
      else
      {
        // Keep non-call commands, otherwise you're deleting them
        newBlock.Cmds.Add(cmd);
      }
    }

    newBlockList.Add(newBlock);
  }

  node.Blocks = newBlockList;

  // If you want to traverse children via the base visitor:
  base.VisitImplementation(node);

  return node;
}


    // public Implementation VisitImplementation2(Implementation node, Program program)
    // {
    //   var newBlockList = new List<Block>();

    //   foreach (var block in node.Blocks)
    //   {
    //     var newBlock = new Block(Token.NoToken, null);
    //     foreach (var cmd in block.Cmds)
    //     {
    //       if (cmd is CallCmd callCmd)
    //       {
          
    //         foreach(var impl in program.Implementations){
    //           if(impl.Proc == callCmd.Proc)
    //           {
    //              foreach (var edge in callGraph.Edges)
    //             {
    //               if(edge.Item1 == impl && edge.Item2 == node)
    //               {
    //                 Console.WriteLine("wohoo");
    //               }
    //           }
    //         }
    //         Expr Expr0 = Expr.True;
    //         Expr storeExprEqual = Expr.True;
    //         Expr Expr3 = Expr.False;
    //         var count = 0;

    //         foreach (var mes in callCmd.Proc.Measure)
    //         {
              
    //           var Expr1 = Expr.Lt(
    //             mes.Condition,
    //             node.Proc.Measure[count].Condition
    //           );

    //           Expr3 = Expr.Or(Expr.And(Expr1, storeExprEqual),Expr3);

    //           storeExprEqual =  Expr.And(storeExprEqual, Expr.Eq(
    //             mes.Condition,
    //             node.Proc.Measure[count].Condition
    //           ));
    //         }
    //         var ass = new AssertCmd( node.tok, Expr3, new MeasureDescription(),  null);
    //         newBlock.Cmds.Add(ass);
    //         count++;
    //       }
    //     }
    //     newBlockList.Add(newBlock);
    //   }

    //   node.Blocks = newBlockList;
    //   return base.VisitImplementation(node);
    // }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      VisitProcedure(node.Proc);
      return base.VisitCallCmd(node);
    }
  }
}
