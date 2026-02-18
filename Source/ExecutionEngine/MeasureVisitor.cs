using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using Microsoft.BaseTypes;

namespace Microsoft.Boogie
{
  public class MeasureVisitor : StandardVisitor
  {
    protected Graph<Implementation> callGraph;

    private readonly Program program;
    private readonly ExecutionEngineOptions options;
    private readonly CivlTypeChecker civlTypeChecker;
    private readonly string bplFileName;

    public MeasureVisitor(
      Program program,
      ExecutionEngineOptions options,
      CivlTypeChecker civlTypeChecker,
      string bplFileName)
    {
      this.program = program;
      this.options = options;
      this.civlTypeChecker = civlTypeChecker;
      this.bplFileName = bplFileName;

      callGraph = Program.BuildTransitiveCallGraph(options, program);

      CheckRecursiveProceduresHaveMeasure();

      foreach (var proc in program.Procedures)
      {
        VisitProcedure(proc);
      }

      foreach (var impl in program.Implementations)
      {
        VisitImplementation2(impl);
      }
    }

    // ------------------------------------------------------------
    // Require measure exists on recursive procedures
    // ------------------------------------------------------------
    private void CheckRecursiveProceduresHaveMeasure()
    {
      foreach (var edge in callGraph.Edges)
      {
        if (edge.Item1 != edge.Item2)
        {
          continue;
        }

        var impl = edge.Item1;
        var proc = impl?.Proc;

        if (proc == null)
        {
          continue;
        }

        if (proc.Measure == null || proc.Measure.Count == 0)
        {
          var tok = proc.tok;

          if (proc is YieldProcedureDecl yp &&
              yp.MoverType.HasValue &&
              yp.MoverType.Value == MoverType.Left)
          {
            civlTypeChecker.checkingContext.Error(
              tok,
              $"Left-mover recursive procedures must have a measure annotation: {proc.Name}");
          }
          else
          {
            civlTypeChecker.checkingContext.Error(
              tok,
              $"Recursive procedures must have a measure annotation: {proc.Name}");
          }
        }
      }
    }

    // ------------------------------------------------------------
    // Add measure > 0 requirement at procedure entry
    // ------------------------------------------------------------
    public override Procedure VisitProcedure(Procedure node)
    {
      if (node.Measure != null)
      {
        foreach (var mes in node.Measure)
        {
          var zero = new LiteralExpr(Token.NoToken, BigNum.ZERO);
          var gt = Expr.Gt(mes.Condition, zero);

          var req = new Requires(node.tok, false, gt, "measure must be > 0");
          node.Requires.Add(req);
        }
      }

      return base.VisitProcedure(node);
    }

    // ------------------------------------------------------------
    // Substitute formals -> actuals safely
    // ------------------------------------------------------------
    private static Dictionary<Variable, Expr>
      BuildFormalToActualMap(CallCmd call)
    {
      var map = new Dictionary<Variable, Expr>();

      var formals = call.Proc.InParams;
      var actuals = call.Ins;

      int n = Math.Min(formals.Count, actuals.Count);

      for (int i = 0; i < n; i++)
      {
        map[formals[i]] = actuals[i];
      }

      return map;
    }

    private sealed class SimpleSubstituter : StandardVisitor
    {
      private readonly Dictionary<Variable, Expr> map;

      public SimpleSubstituter(Dictionary<Variable, Expr> map)
      {
        this.map = map;
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        if (node.Decl is Variable v && map.TryGetValue(v, out var repl))
        {
          return repl;
        }

        return base.VisitIdentifierExpr(node);
      }
    }

    private static Expr ApplySubstitution(
      Expr expr,
      Dictionary<Variable, Expr> subst)
    {
      if (expr == null || subst.Count == 0)
      {
        return expr;
      }

      var s = new SimpleSubstituter(subst);
      return s.VisitExpr(expr);
    }

    // ------------------------------------------------------------
    // Inject correct measure check
    // ------------------------------------------------------------
    public Implementation VisitImplementation2(Implementation impl)
    {
      if (impl?.Proc == null)
      {
        return impl;
      }

      var newBlocks = new List<Block>();

      foreach (var block in impl.Blocks)
      {
        var newCmds = new List<Cmd>();

        foreach (var cmd in block.Cmds)
        {
          newCmds.Add(cmd);

          if (cmd is CallCmd call &&
              call.Proc != null &&
              call.Proc.Measure != null &&
              impl.Proc.Measure != null &&
              call.Proc.Measure.Count > 0)
          {
            bool recursive =
              callGraph.Edges.Any(e =>
                e.Item1 == impl &&
                e.Item2.Proc == call.Proc);

            if (!recursive)
            {
              continue;
            }

            var subst = BuildFormalToActualMap(call);

            Expr decreasing = Expr.False;
            Expr equalPrefix = Expr.True;

            for (int i = 0; i < call.Proc.Measure.Count; i++)
            {
              var calleeMeasure =
                ApplySubstitution(call.Proc.Measure[i].Condition, subst);

              var callerMeasure =
                impl.Proc.Measure[i].Condition;

              var less =
                Expr.Lt(calleeMeasure, callerMeasure);

              var term =
                Expr.And(equalPrefix, less);

              decreasing =
                Expr.Or(decreasing, term);

              equalPrefix =
                Expr.And(equalPrefix,
                  Expr.Eq(calleeMeasure, callerMeasure));
            }

            newCmds.Add(
              new AssertCmd(
                call.tok,
                decreasing,
                new MeasureDescription(),
                null));
          }
        }

        newBlocks.Add(
          new Block(
            block.tok,
            block.Label,
            newCmds,
            block.TransferCmd));
      }

      impl.Blocks = newBlocks;

      return impl;
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      return base.VisitCallCmd(node);
    }
  }
}
