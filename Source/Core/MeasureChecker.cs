using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;
using Microsoft.BaseTypes;

namespace Microsoft.Boogie
{
  public class MeasureChecker
  {
    protected Graph<Implementation> callGraph;
    private readonly Program program;
    public readonly CheckingContext checkingContext = new CheckingContext(null);

    public MeasureChecker(Program program, CoreOptions options)
    {
      this.program = program;
      callGraph = Program.BuildTransitiveCallGraph(options, program);
      CheckRecursiveProceduresHaveMeasure();
    }

    public void Transform()
    {
      foreach (var proc in program.Procedures)
      {
        TransformProcedure(proc);
      }

      foreach (var impl in program.Implementations)
      {
        TransformImplementation(impl);
      }
    }

    // ------------------------------------------------------------
    // Require measure exists on recursive procedures
    // ------------------------------------------------------------
    // private void CheckRecursiveProceduresHaveMeasure()
    // iterate over implemenations of left mover yield procedures / seq procedures (A) with measure - check for same layer also
    // check for a call cmd. (B)
    // check for a backedge (B to A)
    // if -> then we check if there is a measure for B, and then check the length to be equal.
    // report an error on the call cmd.

    // must also handle async and parallel calls
    // for async call -> it needs to have a sync annotation and call is to a procedure at same layer
    // for parallel call -> check for same layer 

    private void CheckRecursiveProceduresHaveMeasure()
    {
      foreach(var impl in program.Implementations)
      {
        if (((impl.Proc is YieldProcedureDecl yp && yp.MoverType.HasValue && yp.MoverType.Value == MoverType.Left) || (!(impl.Proc is YieldProcedureDecl))) && (impl.Proc.Measure.Count != 0))
        {
          foreach(var block in impl.Blocks)
          {
            foreach(var cmd in block.Cmds)
            {
              if(cmd is CallCmd  || cmd is CallCmd asyncCall && asyncCall.IsAsync)
              {
                var callCmd = (CallCmd)cmd;
                bool recursive = callGraph.Edges.Any(e => e.Item1.Proc == callCmd.Proc && e.Item2.Proc == impl.Proc);
                if (recursive && ((Microsoft.Boogie.YieldProcedureDecl)impl.Proc).Layer== ((Microsoft.Boogie.YieldProcedureDecl)callCmd.Proc).Layer)
                {
                  if (callCmd.Proc.Measure.Count != impl.Proc.Measure.Count)
                  {
                    checkingContext.Error(callCmd.tok, $"The callee and caller measure count should match.");
                  }
                }
              }
              if(cmd is ParCallCmd parCallCmd)
              {
                foreach(var procCallCmd in parCallCmd.CallCmds)
                {
                  bool recursive = callGraph.Edges.Any(e => e.Item1.Proc == procCallCmd.Proc && e.Item2.Proc == impl.Proc);
                  if (recursive && ((Microsoft.Boogie.YieldProcedureDecl)impl.Proc).Layer== ((Microsoft.Boogie.YieldProcedureDecl)procCallCmd.Proc).Layer)
                  {
                    if (procCallCmd.Proc.Measure.Count != impl.Proc.Measure.Count)
                    {
                      checkingContext.Error(procCallCmd.tok, $"The callee and caller measure count should match.");
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
      
    // ------------------------------------------------------------
    // Add measure > 0 requirement at procedure entry
    // ------------------------------------------------------------
    private void TransformProcedure(Procedure node)
    {
      foreach (var mes in node.Measure)
      {
        var zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
        var gt = Expr.Gt(mes.Condition, zero);
        var req = new Requires(node.tok, false, gt, "measure must be > 0");
        // all non-negative and one of them is strictly greater than 0
        node.Requires.Add(req);
      }
      // node.Measure = empty list
    }

    // ------------------------------------------------------------
    // Inject correct measure check
    // ------------------------------------------------------------
    public void TransformImplementation(Implementation impl)
    // go over all blocks in the impl
    // create an empty list of commands
    // iterate over each command - if it is a call cmd and it has a measure - substitute and inject - also push the call cmd
    // otherwise push it
    {
      var newBlocks = new List<Block>();
      // you don't need new blocks, just add new commands.


      foreach (var block in impl.Blocks)
      {
        var newCmds = new List<Cmd>();

        foreach (var cmd in block.Cmds)
        {
          // newCmds.Add(cmd);
          // first inject the assertion if any

          if (cmd is not CallCmd callCmd ||
              callCmd.Proc == null ||
              callCmd.Proc.Measure == null ||
              impl.Proc.Measure == null ||
              callCmd.Proc.Measure.Count == 0)
          {
            continue;
          }

          bool recursive = callGraph.Edges.Any(
            e => e.Item1 == impl && e.Item2.Proc == callCmd.Proc);

          if (!recursive)
          {
            continue;
          }

          var callFormalsToActuals =
            Substituter.SubstitutionFromDictionary(
              callCmd.Proc.InParams
                .Zip(callCmd.Ins, (formal, actual) => (formal, actual))
                .ToDictionary(
                  p => (Variable)p.formal,
                  p => (Expr)p.actual));

          Expr decreasing = Expr.False;
          Expr equalPrefix = Expr.True;

          int k = Math.Min(
            callCmd.Proc.Measure.Count,
            impl.Proc.Measure.Count);

          for (int i = 0; i < k; i++)
          {
            Expr instantiated =
              Substituter.Apply(
                callFormalsToActuals,
                callCmd.Proc.Measure[i].Condition);

            var callerMeasure =
              impl.Proc.Measure[i].Condition;

            var less = Expr.Lt(instantiated, callerMeasure);
            var term = Expr.And(equalPrefix, less);

            decreasing = Expr.Or(decreasing, term);
            equalPrefix =
              Expr.And(
                equalPrefix,
                Expr.Eq(instantiated, callerMeasure));
          }

          newCmds.Add(
            new AssertCmd(
              callCmd.tok,
              decreasing,
              new MeasureDescription(),
              null));
        }

        newBlocks.Add(
          new Block(
            block.tok,
            block.Label,
            newCmds,
            block.TransferCmd));
      }

      impl.Blocks = newBlocks;
    }
  }
}