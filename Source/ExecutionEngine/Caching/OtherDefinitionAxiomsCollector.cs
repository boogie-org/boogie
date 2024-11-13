using System;
using System.Collections.Generic;

namespace Microsoft.Boogie;

sealed class OtherDefinitionAxiomsCollector : ReadOnlyVisitor
{
  private ExecutionEngineOptions options;
  Axiom currentAxiom;
  Trigger currentTrigger;

  public OtherDefinitionAxiomsCollector(ExecutionEngineOptions options)
  {
    this.options = options;
  }

  public static void Collect(ExecutionEngineOptions options, IEnumerable<Axiom> axioms)
  {
    var start = DateTime.UtcNow;

    var v = new OtherDefinitionAxiomsCollector(options);
    foreach (var a in axioms)
    {
      v.currentAxiom = a;
      v.VisitExpr(a.Expr);
      v.currentAxiom = null;
    }

    var end = DateTime.UtcNow;
    if (options.TraceCachingForDebugging)
    {
      options.OutputWriter.WriteLine("Collected other definition axioms within {0:F0} ms.",
        end.Subtract(start).TotalMilliseconds);
    }
  }

  public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
  {
    currentTrigger = node.Triggers;
    while (currentTrigger != null)
    {
      foreach (var e in currentTrigger.Tr)
      {
        VisitExpr(e);
      }

      currentTrigger = currentTrigger.Next;
    }

    return base.VisitQuantifierExpr(node);
  }

  public override Expr VisitNAryExpr(NAryExpr node)
  {
    var funCall = node.Fun as FunctionCall;
    if (funCall != null && funCall.Func != null && funCall.Func.Checksum != null && funCall.Func.Checksum != "stable")
    {
      if (funCall.ArgumentCount == 0 || currentTrigger != null)
      {
        // We found a function call within a trigger of a quantifier expression, or the function does not take any
        // arguments so we don't expect it ever to sit inside a quantifier.
        funCall.Func.OtherDefinitionAxioms.Add(currentAxiom);
      }
    }

    return base.VisitNAryExpr(node);
  }
}