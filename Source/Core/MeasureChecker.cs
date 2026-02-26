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
      CheckRecursiveCalls();
    }

    public void Transform()
    {
      foreach (var proc in program.Procedures)
      {
        TransformProcedure(proc);
      }

      foreach (var impl in program.Implementations.Where(impl => impl.Proc.Measure.Count > 0))
      {
        TransformImplementation(impl);
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

      foreach(var impl in program.Implementations.Where(impl => impl.Proc.Measure.Count > 0))
      {
        var callerDecl = impl.Proc;
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
              var callerMeasure = Substituter.Apply(procToImplSubst, impl.Proc.Measure[i].Condition);
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
  }
}