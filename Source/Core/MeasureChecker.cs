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
      CheckMeasureCmds(program);
      CheckProcedureMeasures(program);
      callGraph = Program.BuildTransitiveCallGraph(options, program);
      CheckRecursiveCalls();
    }

    public void CheckMeasureCmds(Program program)
    {
      foreach (var impl in program.Implementations)
      {
        var graph = Program.GraphFromImpl(impl);
        graph.ComputeLoops();

        var headers = new List<Block>();
        foreach (var header in graph.Headers)
        {
          headers.Add(header);

          var measureCmds = header.Cmds.OfType<MeasureCmd>().ToList();
          if (measureCmds.Count == 0)
          {
            continue;
          }

          if (impl.Proc is YieldProcedureDecl)
          {
            var seenLayers = new Dictionary<int, MeasureCmd>();
            foreach (var measureCmd in measureCmds)
            {
              foreach (var layer in measureCmd.Layers)
              {
                if (seenLayers.ContainsKey(layer))
                {
                  checkingContext.Error(
                    measureCmd.tok,
                    $"Loop head may not contain multiple measure commands for layer {layer}");
                }
                else
                {
                  seenLayers[layer] = measureCmd;
                }
              }
            }
          }
          else
          {
            if (measureCmds.Count > 1)
            {
              checkingContext.Error(
                header.tok,
                "Loop head may contain at most one measure command in a sequential procedure");
            }
          }

          var afterAssignment = false;
          foreach (var cmd in header.Cmds)
          {
            if (cmd is AssignCmd)
            {
              afterAssignment = true;
            }
            else if (afterAssignment && cmd is MeasureCmd)
            {
              checkingContext.Error(
                cmd.tok,
                "Assignment must come after the measure command in loop head");
              break;
            }
          }
        }

        foreach (var block in impl.Blocks.Where(block => !headers.Contains(block)))
        {
          foreach (var cmd in block.Cmds.OfType<MeasureCmd>())
          {
            checkingContext.Error(
              cmd.tok,
              "Measure command must not occur outside a loop head");
          }
        }
      }
    }

    private void CheckProcedureMeasures(Program program)
    {
      foreach (var proc in program.Procedures)
      {
        if (proc.Measure == null || proc.Measure.Count == 0)
        {
          continue;
        }

        var seenLayers = new Dictionary<int, MeasureCmd>();
        foreach (var measureCmd in proc.Measure)
        {
          foreach (var layer in measureCmd.Layers)
          {
            if (seenLayers.ContainsKey(layer))
            {
              checkingContext.Error(
                measureCmd.tok,
                $"Procedure may not contain multiple measure commands for layer {layer}");
              break;
            }
            else
            {
              seenLayers[layer] = measureCmd;
            }
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
          checkingContext.Error(callerDecl.tok, "Measure expected only for mover procedures");
        }
        else
        {
          foreach (var block in impl.Blocks)
          {
            foreach (var callCmd in RecursiveCallCmds(callerDecl, block))
            {
              if (callCmd.Proc.Measure.Count != callerDecl.Measure.Count)
              {
                checkingContext.Error(
                  callCmd.tok,
                  "Expected number of measures on callee and caller to be same");
              }
            }
          }
        }
      }
    }

    private void TransformProcedure(Procedure node)
    {
      foreach (var measureCmd in node.Measure)
      {
        foreach (var expr in measureCmd.Expressions)
        {
          if (expr.Type.Equals(Type.Int))
          {
            var zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
            var ge = Expr.Ge(expr, zero);
            node.Requires.Add(
              new Requires(expr.tok, false, ge)
              {
                Description = new MeasureNonNegativeDescription()
              });
          }
        }
      }

      node.Measure = new List<MeasureCmd>();
    }

    private void TransformCallCmds(Implementation impl)
    {
      var implFormals = impl.InParams.Select(x => (Expr)Expr.Ident(x));
      var procToImplSubst =
        Substituter.SubstitutionFromDictionary(impl.Proc.InParams.Zip(implFormals).ToDictionary());

      foreach (var block in impl.Blocks)
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd && IsRecursiveCall(impl.Proc, callCmd))
          {
            var formalToActualSubst =
              Substituter.SubstitutionFromDictionary(
                callCmd.Proc.InParams.Zip(callCmd.Ins).ToDictionary());

            var callerMeasureExprs =
              impl.Proc.Measure.SelectMany(mc => mc.Expressions).ToList();

            var calleeMeasureExprs =
              callCmd.Proc.Measure.SelectMany(mc => mc.Expressions).ToList();

            var callerMeasures = new List<Expr>();
            var calleeMeasures = new List<Expr>();

            for (int i = 0; i < calleeMeasureExprs.Count; i++)
            {
              var callerMeasure = new OldExpr(
                callCmd.tok,
                Substituter.Apply(procToImplSubst, callerMeasureExprs[i]));
              callerMeasures.Add(callerMeasure);

              var calleeMeasure =
                Substituter.Apply(formalToActualSubst, calleeMeasureExprs[i]);
              calleeMeasures.Add(calleeMeasure);
            }

            newCmds.Add(
              new AssertCmd(
                callCmd.tok,
                MeasureLessThanExpr(calleeMeasures, callerMeasures))
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
              foreach (var m in measureCmd.Expressions)
              {
                if (m.Type.Equals(Type.Int))
                {
                  var zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
                  newCmds.Add(new AssertCmd(m.tok, Expr.Ge(m, zero)));
                }
              }

              var oldMeasureExprs = new List<Expr>();
              foreach (var expr in measureCmd.Expressions)
              {
                var localVar = new LocalVariable(
                  Token.NoToken,
                  new TypedIdent(
                    Token.NoToken,
                    $"old_{measureCmd.UniqueId}_{expr.UniqueId}",
                    expr.Type));

                impl.LocVars.Add(localVar);
                oldMeasureExprs.Add(Expr.Ident(localVar));

                var lhs = new SimpleAssignLhs(Token.NoToken, Expr.Ident(localVar));
                newCmds.Add(new AssignCmd(Token.NoToken, [lhs], [expr]));
              }

              deferredAssertExpr = MeasureLessThanExpr(
                measureCmd.Expressions.ToList(),
                oldMeasureExprs);
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

    private static Expr MeasureLessThanExpr(List<Expr> measure1, List<Expr> measure2)
    {
      Debug.Assert(measure1.Count == measure2.Count);

      Expr lessThan = Expr.False;
      Expr equalPrefix = Expr.True;

      for (int i = 0; i < measure1.Count; i++)
      {
        Expr strictDecrease;
        if (measure1[i].Type.Equals(Type.Int))
        {
          strictDecrease = Expr.Lt(measure1[i], measure2[i]);
        }
        else if (measure1[i].Type.Equals(Type.Bool))
        {
          strictDecrease = Expr.And(Expr.Not(measure1[i]), measure2[i]);
        }
        else
        {
          throw new Cce.UnreachableException();
        }

        lessThan = Expr.Or(
          lessThan,
          Expr.And(equalPrefix, strictDecrease));

        equalPrefix = Expr.And(
          equalPrefix,
          Expr.Eq(measure1[i], measure2[i]));
      }

      return lessThan;
    }
  }
}