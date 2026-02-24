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
    private readonly CoreOptions options;
    public readonly CheckingContext checkingContext = new CheckingContext(null);

    public MeasureVisitor(Program program, CoreOptions options)
    {
      this.program = program;
      this.options = options;
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
      var alreadyChecked = new List<Implementation>();

      foreach (var edge in callGraph.Edges)
      {
        var currentEdgeOrNull = callGraph.Edges.FirstOrDefault(
          e => e.Item1 == edge.Item1 && e.Item2 == edge.Item2,
          Tuple.Create<Implementation, Implementation>(null, null));

        if (currentEdgeOrNull != Tuple.Create<Implementation, Implementation>(null, null))
        {
          var impl1 = edge.Item1;
          var proc1 = impl1.Proc;
          var impl2 = edge.Item2;
          var proc2 = impl2.Proc;
          var tok1 = proc1.tok;
          var tok2 = proc2.tok;

          if (alreadyChecked.Contains(impl1))
          {
            if (proc1 is YieldProcedureDecl yp &&
                yp.MoverType.HasValue &&
                yp.MoverType.Value == MoverType.Left)
            {
              if (proc1.Measure == null || proc1.Measure.Count == 0)
              {
                checkingContext.Error(
                  tok1,
                  "Left-mover recursive procedures must have a measure annotation: {proc1.Name}");
              }
            }
            else
            {
              checkingContext.Error(
                tok1,
                "Recursive procedures must have a measure annotation: {proc1.Name}");
            }
          }

          if (alreadyChecked.Contains(impl2))
          {
            if (proc2 is YieldProcedureDecl yp2 &&
                yp2.MoverType.HasValue &&
                yp2.MoverType.Value == MoverType.Left)
            {
              if (proc2.Measure == null || proc2.Measure.Count == 0)
              {
                checkingContext.Error(
                  tok2,
                  "Left-mover recursive procedures must have a measure annotation: {proc2.Name}");
              }
            }
            else
            {
              checkingContext.Error(
                tok2,
                "Recursive procedures must have a measure annotation: {proc2.Name}");
            }
          }

          alreadyChecked.Add(impl1);
          alreadyChecked.Add(impl2);
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

          if (callCmd.Proc.InParams.Count != callCmd.Ins.Count)
          {
            throw new InvalidOperationException(
              "Call to {callCmd.Proc.Name} has {callCmd.Ins.Count} actuals but {callCmd.Proc.InParams.Count} formals.");
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
      return impl;
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      return base.VisitCallCmd(node);
    }
  }
}