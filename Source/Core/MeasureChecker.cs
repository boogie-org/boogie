using System.Collections.Generic;
using System.Diagnostics;
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
      CheckMeasure(program);
      callGraph = Program.BuildTransitiveCallGraph(options, program);
      CheckRecursiveCalls();
    }

    public void CheckMeasure(Program program)
    {
      foreach (var impl in program.Implementations)
      {
        var graph = Program.GraphFromImpl(impl);
        graph.ComputeLoops();

        var listHeads = new List<Block>();
        foreach (var header in graph.Headers)
        {
          listHeads.Add(header);

          var afterMeasure = false;
          foreach (var cmd in header.Cmds)
          {
            if (cmd is MeasureCmd measureCmd)
            {
              foreach (var cmd2 in header.Cmds)
              {
                if (cmd2 is MeasureCmd mc)
                {
                  afterMeasure = true;
                }

                if (cmd2 is AssignCmd ac && afterMeasure)
                {
                  checkingContext.Error(cmd.tok, $"Cannot update measure in loop head");
                }
              }
            }
          }
        }

        foreach (var block in impl.Blocks)
        {
          var countMeasure = 0;
          foreach (var cmd in block.Cmds)
          {
            if (cmd is MeasureCmd mc)
            {
              if (!listHeads.Contains(block))
              {
                checkingContext.Error(cmd.tok, $"You cannot have measure outside loop head");
              }
              else
              {
                countMeasure++;
              }
            }
          }

          if (countMeasure > 1)
          {
            checkingContext.Error(block.tok, $"Loop head can contain only one measure");
          }
        }
      }
    }

    public static void Transform(Program program, CoreOptions options)
    {
      var measureChecker = new MeasureChecker(program, options);
      Debug.Assert(measureChecker.checkingContext.ErrorCount == 0);

      foreach (var impl in program.Implementations.Where(impl => impl.Proc.Measure.Count > 0))
      {
        measureChecker.TransformCallCmds(impl);
      }

      // Add non-negative requirements for each measure
      // Since implementations have already been transformed, measure annotations are no longer
      // needed and should be dropped
      foreach (var proc in program.Procedures)
      {
        measureChecker.TransformProcedure(proc);
      }

      measureChecker.TransformMeasureCmds(program);
    }

    private bool IsRecursiveCall(Procedure callerProc, CallCmd callCmd)
    {
      return callGraph.Edges.Any(e => e.Item1.Proc == callCmd.Proc && e.Item2.Proc == callerProc);
    }

    // ------------------------------------------------------------
    // Check that number of measures match on recursive calls
    // ------------------------------------------------------------
    private void CheckRecursiveCalls()
    {
      IEnumerable<CallCmd> RecursiveCallCmds(Procedure callerDecl, Block block)
      {
        return block.Cmds.OfType<ParCallCmd>()
          .SelectMany(parCallCmd => parCallCmd.CallCmds)
          .Union(block.Cmds.OfType<CallCmd>())
          .Where(callCmd => IsRecursiveCall(callerDecl, callCmd));
      }

      foreach (var impl in program.Implementations.Where(impl => impl.Proc.Measure.Count > 0))
      {
        var callerDecl = impl.Proc;
        if (callerDecl is ActionDecl || callerDecl is YieldProcedureDecl yp && !yp.MoverType.HasValue)
        {
          checkingContext.Error(callerDecl.tok, $"Measure expected only for mover procedures");
        }
        else
        {
          foreach (var block in impl.Blocks)
          {
            foreach (var callCmd in RecursiveCallCmds(callerDecl, block))
            {
              if (callCmd.Proc.Measure.Count != callerDecl.Measure.Count)
              {
                checkingContext.Error(callCmd.tok, $"Expected number of measures on callee and caller to be same");
              }
            }
          }
        }
      }
    }

    // ------------------------------------------------------------
    // Add non-negative measure requirement at procedure entry
    // ------------------------------------------------------------
    private void TransformProcedure(Procedure node)
    {
      foreach (var m in node.Measure)
      {
        var zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
        var ge = Expr.Ge(m.Condition, zero);
        node.Requires.Add(new Requires(m.tok, false, ge) { Description = new MeasureNonNegativeDescription() });
      }

      node.Measure = [];
    }

    // ------------------------------------------------------------
    // Inject measure decreases check
    // ------------------------------------------------------------
    private void TransformCallCmds(Implementation impl)
    {
      var implFormals = impl.InParams.Select(x => (Expr)Expr.Ident(x));
      var procToImplSubst = Substituter.SubstitutionFromDictionary(impl.Proc.InParams.Zip(implFormals).ToDictionary());

      foreach (var block in impl.Blocks)
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd && IsRecursiveCall(impl.Proc, callCmd))
          {
            var formalToActualSubst =
              Substituter.SubstitutionFromDictionary(callCmd.Proc.InParams.Zip(callCmd.Ins).ToDictionary());

            var callerMeasures = new List<Expr>();
            var calleeMeasures = new List<Expr>();
            for (int i = 0; i < callCmd.Proc.Measure.Count; i++)
            {
              var callerMeasure = new OldExpr(
                callCmd.tok,
                Substituter.Apply(procToImplSubst, impl.Proc.Measure[i].Condition));
              callerMeasures.Add(callerMeasure);

              var calleeMeasure =
                Substituter.Apply(formalToActualSubst, callCmd.Proc.Measure[i].Condition);
              calleeMeasures.Add(calleeMeasure);
            }

            newCmds.Add(
              new AssertCmd(callCmd.tok, MeasureLessThanExpr(calleeMeasures, callerMeasures))
              {
                Description = new MeasureDecreasesDescription()
              });
          }

          newCmds.Add(cmd);
        }

        block.Cmds = newCmds;
      }
    }

    private void TransformMeasureCmds(Program program)
    {
      foreach (var impl in program.Implementations)
      {
        var graph = Program.GraphFromImpl(impl);
        graph.ComputeLoops();

        foreach (var header in graph.Headers)
        {
          var newCmds = new List<Cmd>();
          Expr deferredAssertExpr = null;

          foreach (var cmd in header.Cmds)
          {
            if (cmd is MeasureCmd measureCmd)
            {
              var zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);

              var oldMeasureExprs = new List<Expr>();
              foreach (var expr in measureCmd.Exprs)
              {
                var localVar = new LocalVariable(
                  Token.NoToken,
                  new TypedIdent(
                    Token.NoToken,
                    $"old_{measureCmd.UniqueId}_{expr.UniqueId}",
                    Type.Int));
                impl.LocVars.Add(localVar);

                var lhs = new SimpleAssignLhs(Token.NoToken, Expr.Ident(localVar));
                newCmds.Add(
                  new AssignCmd(
                    Token.NoToken,
                    new List<AssignLhs> { lhs },
                    new List<Expr> { expr }));

                var localVarExpr = Expr.Ident(localVar);
                oldMeasureExprs.Add(localVarExpr);
                var ge = Expr.Ge(localVarExpr, zero);
                var ac = new AssertCmd(expr.tok, ge) { Description = new MeasureNonNegativeDescription() };
                newCmds.Add(ac);
              }

              deferredAssertExpr = MeasureLessThanExpr(measureCmd.Exprs, oldMeasureExprs);
            }
            else
            {
              newCmds.Add(cmd);
            }
          }

          header.Cmds = newCmds;

          if (deferredAssertExpr == null)
          {
            continue;
          }

          foreach (var backEdgeNode in graph.BackEdgeNodes(header))
          {
            var deferredAssert = new AssertCmd(backEdgeNode.tok, deferredAssertExpr)
            {
              Description = new MeasureDecreasesDescription()
            };
            backEdgeNode.Cmds.Add(deferredAssert);
          }
        }
      }
    }

    // returns the expression for measure1 < measure2
    private static Expr MeasureLessThanExpr(List<Expr> measure1, List<Expr> measure2)
    {
      Debug.Assert(measure1.Count == measure2.Count);

      Expr lessThan = Expr.False;
      Expr equalPrefix = Expr.True;
      for (int i = 0; i < measure1.Count; i++)
      {
        lessThan = Expr.Or(
          lessThan,
          Expr.And(equalPrefix, Expr.Lt(measure1[i], measure2[i])));
        equalPrefix = Expr.And(equalPrefix, Expr.Eq(measure1[i], measure2[i]));
      }

      return lessThan;
    }
  }
}