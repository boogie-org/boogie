using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class ModSetCollector : ReadOnlyVisitor
{
  private CoreOptions options;
  private Procedure enclosingProc;

  private Dictionary<Procedure, HashSet<Variable>> modSets;

  public ModSetCollector(CoreOptions options)
  {
    this.options = options;
    modSets = new Dictionary<Procedure, HashSet<Variable>>();
  }

  private bool moreProcessingRequired;

  public void CollectModifies(Program program)
  {
    var implementedProcs = new HashSet<Procedure>(program.Implementations.Where(impl => impl.Proc != null).Select(impl => impl.Proc));
    program.Procedures.Where(proc =>
      proc.GetType() == typeof(Procedure) || proc is ActionDecl || (proc is YieldProcedureDecl yieldProcedureDecl && yieldProcedureDecl.HasMoverType))
      .ForEach(proc =>
      {
        modSets.Add(proc, new HashSet<Variable>());
      });
    foreach (var proc in modSets.Keys)
    {
      enclosingProc = proc;
      foreach (var expr in proc.Modifies)
      {
        ProcessVariable(expr.Decl);
      }
      enclosingProc = null;
    }

    moreProcessingRequired = true;
    while (moreProcessingRequired)
    {
      moreProcessingRequired = false;
      this.Visit(program);
    }

    foreach (Procedure x in modSets.Keys)
    {
      if (x.Modifies == null)
      {
        x.Modifies = new List<IdentifierExpr>();
      }
      foreach (Variable v in modSets[x].Except(x.Modifies.Select(y => y.Decl)))
      {
        x.Modifies.Add(new IdentifierExpr(v.tok, v));
      }
    }

#if DEBUG_PRINT
      options.OutputWriter.WriteLine("Number of procedures with nonempty modsets = {0}", modSets.Keys.Count);
      foreach (Procedure x in modSets.Keys)
      {
        Contract.Assert(x != null);
        options.OutputWriter.Write("{0} : ", x.Name);
        bool first = true;
        foreach (var y in modSets[x])
        {
          if (first)
          {
            first = false;
          }
          else
          {
            options.OutputWriter.Write(", ");
          }
          options.OutputWriter.Write("{0}", y.Name);
        }
        options.OutputWriter.WriteLine("");
      }
#endif
  }

  public override Implementation VisitImplementation(Implementation node)
  {
    if (!modSets.ContainsKey(node.Proc))
    {
      return node;
    }
    enclosingProc = node.Proc;
    Implementation ret = base.VisitImplementation(node);
    enclosingProc = null;
    return ret;
  }

  public override Cmd VisitAssignCmd(AssignCmd assignCmd)
  {
    Cmd ret = base.VisitAssignCmd(assignCmd);
    foreach (AssignLhs lhs in assignCmd.Lhss)
    {
      ProcessVariable(lhs.DeepAssignedVariable);
    }
    return ret;
  }

  public override Cmd VisitUnpackCmd(UnpackCmd unpackCmd)
  {
    Cmd ret = base.VisitUnpackCmd(unpackCmd);
    foreach (var expr in unpackCmd.Lhs.Args)
    {
      ProcessVariable(((IdentifierExpr)expr).Decl);
    }
    return ret;
  }
    
  public override Cmd VisitHavocCmd(HavocCmd havocCmd)
  {
    Cmd ret = base.VisitHavocCmd(havocCmd);
    foreach (IdentifierExpr expr in havocCmd.Vars)
    {
      ProcessVariable(expr.Decl);
    }
    return ret;
  }

  public override Cmd VisitCallCmd(CallCmd callCmd)
  {
    Cmd ret = base.VisitCallCmd(callCmd);
    if (callCmd.IsAsync && !callCmd.HasAttribute(CivlAttributes.SYNC))
    {
      return ret;
    }
    foreach (IdentifierExpr ie in callCmd.Outs)
    {
      Debug.Assert(ie != null);
      ProcessVariable(ie.Decl);
    }
    Procedure callee = callCmd.Proc;
    Debug.Assert(callee != null);
    if (enclosingProc is YieldProcedureDecl callerDecl &&
        callee is YieldProcedureDecl calleeDecl && !calleeDecl.HasMoverType && calleeDecl.RefinedAction != null)
    {
      callee = calleeDecl.RefinedActionAtLayer(callerDecl.Layer);
    }
    if (modSets.ContainsKey(callee))
    {
      foreach (Variable var in modSets[callee])
      {
        ProcessVariable(var);
      }
    }
    if (CivlPrimitives.IsPrimitive(callee))
    {
      var modifiedArgument = CivlPrimitives.ModifiedArgument(callCmd)?.Decl;
      if (modifiedArgument != null)
      {
        ProcessVariable(modifiedArgument);
      }
    }
    return ret;
  }

  private void ProcessVariable(Variable var)
  {
    Debug.Assert(var != null);
    if (var is GlobalVariable && modSets[enclosingProc].Add(var))
    {
      moreProcessingRequired = true;
    }
  }

  public override Expr VisitCodeExpr(CodeExpr node)
  {
    // don't go into the code expression, since it can only modify variables local to the code expression,
    // and the mod-set analysis is interested in global variables
    return node;
  }
}