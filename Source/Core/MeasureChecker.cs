using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;
using Microsoft.BaseTypes;
using System.Diagnostics;
using System.Reflection.Emit;

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
      CheckRecursiveCalls();
      //To add typechecking or measure commands.
      TransformMeasureCmds(program);
    }

    public void Transform(Program program, CoreOptions options)
    {
      var measureChecker = new MeasureChecker(program, options);
      Debug.Assert(measureChecker.checkingContext.ErrorCount == 0);

      foreach (var impl in program.Implementations.Where(impl => impl.Proc.Measure.Count > 0))
      {
        measureChecker.TransformImplementation(impl);
      }

      // Add non-negative requirements for each measure
      // Since implementations have already been transformed, measure annotations are no longer
      // needed and should be dropped
      foreach (var proc in program.Procedures)
      {
        measureChecker.TransformProcedure(proc);
      }
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
        return block.Cmds.OfType<ParCallCmd>().SelectMany(parCallCmd => parCallCmd.CallCmds).Union(block.Cmds.OfType<CallCmd>())
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
        node.Requires.Add(new Requires(m.tok, false, ge){ Description = new MeasureNonNegativeDescription() });
      }
      node.Measure = [];
    }

    // ------------------------------------------------------------
    // Inject measure decreases check
    // ------------------------------------------------------------
    public void TransformImplementation(Implementation impl)
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
            Expr decreasing = Expr.False;
            Expr equalPrefix = Expr.True;
            for (int i = 0; i < callCmd.Proc.Measure.Count; i++)
            {
              var callerMeasure = new OldExpr(callCmd.tok, Substituter.Apply(procToImplSubst, impl.Proc.Measure[i].Condition));
              var calleeMeasure = Substituter.Apply(formalToActualSubst, callCmd.Proc.Measure[i].Condition);
              decreasing = Expr.Or(decreasing, Expr.And(equalPrefix, Expr.Lt(calleeMeasure, callerMeasure)));
              equalPrefix = Expr.And(equalPrefix, Expr.Eq(calleeMeasure, callerMeasure));
            }
            newCmds.Add(new AssertCmd(callCmd.tok, decreasing){ Description = new MeasureDecreasesDescription() });
          }
          newCmds.Add(cmd);
        }
        block.Cmds = newCmds;
      }
    }

    public void TransformMeasureCmds(Program program)
    {
      foreach (var impl in program.Implementations)
      {
        var graph = Program.GraphFromImpl(impl);
        graph.ComputeLoops();
        Dictionary<string, List<Expr>> map = new Dictionary<string, List<Expr>>();

        foreach (var header in graph.Headers)
        {
          foreach (var backEdgeNode in graph.BackEdgeNodes(header))
          {
            var block_loopHead = header;
            var block_loopBody = backEdgeNode;

            var newCmdsHead = new List<Cmd>();
            var newCmdsBody = new List<Cmd>();

            foreach (var cmd in block_loopHead.Cmds)
            {
              if (cmd is MeasureCmd measureCmd)
              {
                var zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
                foreach (var ex in measureCmd.Exprs)
                {
                  var ge = Expr.Ge(ex, zero);
                  var ac1 = new AssertCmd(measureCmd.tok, ge);
                  newCmdsHead.Add(ac1);
                }

                var newLocalVars = new List<Variable>();

                foreach (var ex in measureCmd.Exprs)
                {
                  LocalVariable localVar =
                    new LocalVariable(
                      Token.NoToken,
                      new TypedIdent(Token.NoToken, "old_" + ex, Type.Int));

                  newLocalVars.Add(localVar);

                  foreach (var k in impl.LocVars)
                  {
                    newLocalVars.Add(k);
                  }

                  impl.LocVars = newLocalVars;

                  var lhs = new SimpleAssignLhs(Token.NoToken, Expr.Ident(localVar));

                  newCmdsHead.Add(
                    new AssignCmd(
                      Token.NoToken,
                      new List<AssignLhs> { lhs },
                      new List<Expr> { ex }));
                }
              }
              else
              {
                newCmdsHead.Add(cmd);
              }
            }

            foreach (var c in block_loopBody.Cmds)
            {
              newCmdsBody.Add(c);
            }

            foreach (var cmd in block_loopHead.Cmds)
            {
              if (cmd is MeasureCmd measureCmd)
              {
                foreach (var ex in measureCmd.Exprs)
                {
                  LocalVariable localVar =
                    new LocalVariable(
                      Token.NoToken,
                      new TypedIdent(Token.NoToken, "old_" + ex, Type.Int));

                  var old = Expr.Ident(localVar);
                  var decreasing = Expr.Lt(ex, old);
                  var ac2 = new AssertCmd(Token.NoToken, decreasing);
                  newCmdsBody.Add(ac2);
                }
              }
              else
              {
                newCmdsBody = block_loopBody.Cmds;
              }
            }

            block_loopHead.Cmds = newCmdsHead;
            block_loopBody.Cmds = newCmdsBody;
          }
        }
      }
    }
  }
}