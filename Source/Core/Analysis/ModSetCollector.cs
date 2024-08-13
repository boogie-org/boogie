using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class ModSetCollector : ReadOnlyVisitor
{
  private CoreOptions options;
  private Procedure enclosingProc;

  private Dictionary<Procedure, HashSet<Variable>> modSets;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(cce.NonNullDictionaryAndValues(modSets));
    Contract.Invariant(Contract.ForAll(modSets.Values, v => cce.NonNullElements(v)));
  }

  public ModSetCollector(CoreOptions options)
  {
    this.options = options;
    modSets = new Dictionary<Procedure, HashSet<Variable>>();
  }

  private bool moreProcessingRequired;

  public void DoModSetAnalysis(Program program)
  {
    Contract.Requires(program != null);

    if (options.Trace)
    {
//          Console.WriteLine();
//          Console.WriteLine("Running modset analysis ...");
//          int procCount = 0;
//          foreach (Declaration/*!*/ decl in program.TopLevelDeclarations)
//          {
//              Contract.Assert(decl != null);
//              if (decl is Procedure)
//                  procCount++;
//          }
//          Console.WriteLine("Number of procedures = {0}", procCount);*/
    }

    HashSet<Procedure /*!*/> implementedProcs = new HashSet<Procedure /*!*/>();
    foreach (var impl in program.Implementations)
    {
      if (impl.Proc != null)
      {
        implementedProcs.Add(impl.Proc);
      }
    }

    foreach (var proc in program.Procedures)
    {
      if (!implementedProcs.Contains(proc))
      {
        enclosingProc = proc;
        foreach (var expr in proc.Modifies)
        {
          Contract.Assert(expr != null);
          ProcessVariable(expr.Decl);
        }

        enclosingProc = null;
      }
      else
      {
        modSets.Add(proc, new HashSet<Variable>());
      }
    }

    moreProcessingRequired = true;
    while (moreProcessingRequired)
    {
      moreProcessingRequired = false;
      this.Visit(program);
    }

    foreach (Procedure x in modSets.Keys)
    {
      x.Modifies = new List<IdentifierExpr>();
      foreach (Variable v in modSets[x])
      {
        x.Modifies.Add(new IdentifierExpr(v.tok, v));
      }
    }

#if DEBUG_PRINT
      options.OutputWriter.WriteLine("Number of procedures with nonempty modsets = {0}", modSets.Keys.Count);
      foreach (Procedure/*!*/ x in modSets.Keys) {
        Contract.Assert(x != null);
        options.OutputWriter.Write("{0} : ", x.Name);
        bool first = true;
        foreach (Variable/*!*/ y in modSets[x]) {
          Contract.Assert(y != null);
          if (first)
            first = false;
          else
            options.OutputWriter.Write(", ");
          options.OutputWriter.Write("{0}", y.Name);
        }
        options.OutputWriter.WriteLine("");
      options.OutputWriter
#endif
  }

  public override Implementation VisitImplementation(Implementation node)
  {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<Implementation>() != null);
    enclosingProc = node.Proc;
    Implementation /*!*/
      ret = base.VisitImplementation(node);
    Contract.Assert(ret != null);
    enclosingProc = null;

    return ret;
  }

  public override Cmd VisitAssignCmd(AssignCmd assignCmd)
  {
    Contract.Ensures(Contract.Result<Cmd>() != null);
    Cmd ret = base.VisitAssignCmd(assignCmd);
    foreach (AssignLhs lhs in assignCmd.Lhss)
    {
      Contract.Assert(lhs != null);
      ProcessVariable(lhs.DeepAssignedVariable);
    }

    return ret;
  }

  public override Cmd VisitUnpackCmd(UnpackCmd unpackCmd)
  {
    Contract.Ensures(Contract.Result<Cmd>() != null);
    Cmd ret = base.VisitUnpackCmd(unpackCmd);
    foreach (var expr in unpackCmd.Lhs.Args)
    {
      ProcessVariable(((IdentifierExpr)expr).Decl);
    }
    return ret;
  }
    
  public override Cmd VisitHavocCmd(HavocCmd havocCmd)
  {
    Contract.Ensures(Contract.Result<Cmd>() != null);
    Cmd ret = base.VisitHavocCmd(havocCmd);
    foreach (IdentifierExpr expr in havocCmd.Vars)
    {
      Contract.Assert(expr != null);
      ProcessVariable(expr.Decl);
    }

    return ret;
  }

  public override Cmd VisitCallCmd(CallCmd callCmd)
  {
    //Contract.Requires(callCmd != null);
    Contract.Ensures(Contract.Result<Cmd>() != null);
    Cmd ret = base.VisitCallCmd(callCmd);
    foreach (IdentifierExpr ie in callCmd.Outs)
    {
      if (ie != null)
      {
        ProcessVariable(ie.Decl);
      }
    }

    Procedure callee = callCmd.Proc;
    if (callee == null)
    {
      return ret;
    }

    if (modSets.ContainsKey(callee))
    {
      foreach (Variable var in modSets[callee])
      {
        ProcessVariable(var);
      }
    }

    return ret;
  }

  private void ProcessVariable(Variable var)
  {
    Procedure /*!*/
      localProc = cce.NonNull(enclosingProc);
    if (var == null)
    {
      return;
    }

    if (!(var is GlobalVariable))
    {
      return;
    }

    if (!modSets.ContainsKey(localProc))
    {
      modSets[localProc] = new HashSet<Variable /*!*/>();
    }

    if (modSets[localProc].Contains(var))
    {
      return;
    }

    moreProcessingRequired = true;
    modSets[localProc].Add(var);
  }

  public override Expr VisitCodeExpr(CodeExpr node)
  {
    // don't go into the code expression, since it can only modify variables local to the code expression,
    // and the mod-set analysis is interested in global variables
    return node;
  }
}