using System;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

sealed class DependencyCollector : ReadOnlyVisitor
{
  private DeclWithFormals currentDeclaration;
  private Axiom currentAxiom;

  public static void Collect(ExecutionEngineOptions options, Program program)
  {
    var start = DateTime.UtcNow;

    var dc = new DependencyCollector();
    dc.VisitProgram(program);

    var end = DateTime.UtcNow;
    if (options.TraceCachingForDebugging)
    {
      options.OutputWriter.WriteLine("Collected dependencies within {0:F0} ms.", end.Subtract(start).TotalMilliseconds);
    }
  }

  public static bool CanExpressOldSpecs(Procedure oldProc, Program newProg, bool ignoreModifiesClauses = false)
  {
    Contract.Requires(oldProc != null && newProg != null);

    var funcs = newProg.Functions;
    var globals = newProg.GlobalVariables;
    return oldProc.DependenciesCollected
           && (oldProc.FunctionDependencies == null || oldProc.FunctionDependencies.All(dep =>
             funcs.Any(f => f.Name == dep.Name && f.DependencyChecksum == dep.DependencyChecksum)))
           && (ignoreModifiesClauses || oldProc.Modifies.All(m => globals.Any(g => g.Name == m.Name)));
  }

  public override Procedure VisitProcedure(Procedure node)
  {
    currentDeclaration = node;

    foreach (var param in node.InParams)
    {
      if (param.TypedIdent != null && param.TypedIdent.WhereExpr != null)
      {
        VisitExpr(param.TypedIdent.WhereExpr);
      }
    }

    var result = base.VisitProcedure(node);
    node.DependenciesCollected = true;
    currentDeclaration = null;
    return result;
  }

  public override Implementation VisitImplementation(Implementation node)
  {
    currentDeclaration = node;

    foreach (var param in node.InParams)
    {
      if (param.TypedIdent != null && param.TypedIdent.WhereExpr != null)
      {
        VisitExpr(param.TypedIdent.WhereExpr);
      }
    }

    if (node.Proc != null)
    {
      node.AddProcedureDependency(node.Proc);
    }

    var result = base.VisitImplementation(node);
    node.DependenciesCollected = true;
    currentDeclaration = null;
    return result;
  }

  public override Axiom VisitAxiom(Axiom node)
  {
    if (node.DependenciesCollected)
    {
      if (currentDeclaration != null && node.FunctionDependencies != null)
      {
        foreach (var f in node.FunctionDependencies)
        {
          currentDeclaration.AddFunctionDependency(f);
        }
      }

      return node;
    }

    currentAxiom = node;
    var result = base.VisitAxiom(node);
    node.DependenciesCollected = true;
    currentAxiom = null;
    return result;
  }

  public override Function VisitFunction(Function node)
  {
    currentDeclaration = node;

    if (node.DefinitionAxiom != null)
    {
      VisitAxiom(node.DefinitionAxiom);
    }

    if (node.OtherDefinitionAxioms != null)
    {
      foreach (var a in node.OtherDefinitionAxioms)
      {
        if (a != node.DefinitionAxiom)
        {
          VisitAxiom(a);
        }
      }
    }

    var result = base.VisitFunction(node);
    node.DependenciesCollected = true;
    currentDeclaration = null;
    return result;
  }

  public override Cmd VisitCallCmd(CallCmd node)
  {
    if (currentDeclaration != null)
    {
      currentDeclaration.AddProcedureDependency(node.Proc);
    }

    return base.VisitCallCmd(node);
  }

  public override Expr VisitNAryExpr(NAryExpr node)
  {
    var funCall = node.Fun as FunctionCall;
    if (funCall != null)
    {
      if (currentDeclaration != null)
      {
        currentDeclaration.AddFunctionDependency(funCall.Func);
      }

      if (currentAxiom != null)
      {
        currentAxiom.AddFunctionDependency(funCall.Func);
      }
    }

    return base.VisitNAryExpr(node);
  }
}