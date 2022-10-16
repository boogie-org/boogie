using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class LinearTypeChecker : ReadOnlyVisitor
  {
    public Program program;
    private CheckingContext checkingContext;
    private CivlTypeChecker civlTypeChecker;
    private Dictionary<string, LinearDomain> domainNameToLinearDomain;
    private Dictionary<Type, LinearDomain> linearTypeToLinearDomain;
    private Dictionary<Absy, HashSet<Variable>> availableLinearVars;

    public LinearTypeChecker(CivlTypeChecker civlTypeChecker)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.program = civlTypeChecker.program;
      this.checkingContext = civlTypeChecker.checkingContext;
      this.availableLinearVars = new Dictionary<Absy, HashSet<Variable>>();
    }
    
    #region Visitor Implementation

    private IEnumerable<Variable> LinearGlobalVariables =>
      program.GlobalVariables.Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.ORDINARY);

    public override Implementation VisitImplementation(Implementation node)
    {
      var proc = node.Proc;
      if (civlTypeChecker.IsAction(proc) ||
          civlTypeChecker.IsLemmaProcedure(proc))
      {
        return node;
      }

      node.PruneUnreachableBlocks(civlTypeChecker.Options);
      node.ComputePredecessorsForBlocks();
      GraphUtil.Graph<Block> graph = Program.GraphFromImpl(node);
      graph.ComputeLoops();

      var linearGlobalVariables = LinearGlobalVariables;
      HashSet<Variable> start = new HashSet<Variable>(linearGlobalVariables.Union(node.InParams.Where(v =>
      {
        var kind = LinearDomainCollector.FindLinearKind(v);
        return kind == LinearKind.LINEAR || kind == LinearKind.LINEAR_IN;
      })));

      var oldErrorCount = checkingContext.ErrorCount;
      var impl = base.VisitImplementation(node);
      if (oldErrorCount < checkingContext.ErrorCount)
      {
        return impl;
      }

      Stack<Block> dfsStack = new Stack<Block>();
      HashSet<Block> dfsStackAsSet = new HashSet<Block>();
      availableLinearVars[node.Blocks[0]] = start;
      dfsStack.Push(node.Blocks[0]);
      dfsStackAsSet.Add(node.Blocks[0]);
      while (dfsStack.Count > 0)
      {
        Block b = dfsStack.Pop();
        dfsStackAsSet.Remove(b);
        HashSet<Variable> end = PropagateAvailableLinearVarsAcrossBlock(b);
        if (b.TransferCmd is GotoCmd gotoCmd)
        {
          foreach (Block target in gotoCmd.labelTargets)
          {
            if (!availableLinearVars.ContainsKey(target))
            {
              availableLinearVars[target] = new HashSet<Variable>(end);
              dfsStack.Push(target);
              dfsStackAsSet.Add(target);
            }
            else
            {
              var savedAvailableVars = new HashSet<Variable>(availableLinearVars[target]);
              availableLinearVars[target].IntersectWith(end);
              if (savedAvailableVars.IsProperSupersetOf(availableLinearVars[target]) && !dfsStackAsSet.Contains(target))
              {
                dfsStack.Push(target);
                dfsStackAsSet.Add(target);
              }
            }
          }
        }
        else
        {
          linearGlobalVariables.Except(end).Iter(g =>
          {
            Error(b.TransferCmd, $"Global variable {g.Name} must be available at a return");
          });
          node.InParams.Except(end).Where(v =>
          {
            var kind = LinearDomainCollector.FindLinearKind(v);
            return kind == LinearKind.LINEAR || kind == LinearKind.LINEAR_OUT;
          }).Iter(v => { Error(b.TransferCmd, $"Input variable {v.Name} must be available at a return"); });
          node.OutParams.Except(end).Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.ORDINARY)
            .Iter(v => { Error(b.TransferCmd, $"Output variable {v.Name} must be available at a return"); });
        }
      }

      if (graph.Reducible)
      {
        foreach (Block header in graph.Headers)
        {
          foreach (GlobalVariable g in linearGlobalVariables.Except(availableLinearVars[header]))
          {
            Error(header, $"Global variable {g.Name} must be available at a loop head");
          }
        }
      }

      return impl;
    }

    private void Error(Absy node, string message)
    {
      checkingContext.Error(node, message);
    }
    
    private void AddAvailableVars(CallCmd callCmd, HashSet<Variable> start)
    {
      callCmd.Outs.Where(ie => LinearDomainCollector.FindLinearKind(ie.Decl) != LinearKind.ORDINARY)
        .Iter(ie => start.Add(ie.Decl));
      for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
      {
        if (callCmd.Ins[i] is IdentifierExpr ie)
        {
          if (LinearDomainCollector.FindLinearKind(callCmd.Proc.InParams[i]) == LinearKind.LINEAR_OUT)
          {
            start.Add(ie.Decl);
          }
        }
      }
    }

    private void AddAvailableVars(ParCallCmd parCallCmd, HashSet<Variable> start)
    {
      foreach (CallCmd callCmd in parCallCmd.CallCmds)
      {
        AddAvailableVars(callCmd, start);
      }
    }

    private HashSet<Variable> PropagateAvailableLinearVarsAcrossBlock(Block b)
    {
      var linearGlobalVariables = LinearGlobalVariables;
      HashSet<Variable> start = new HashSet<Variable>(availableLinearVars[b]);
      foreach (Cmd cmd in b.Cmds)
      {
        if (cmd is AssignCmd assignCmd)
        {
          for (int i = 0; i < assignCmd.Lhss.Count; i++)
          {
            if (LinearDomainCollector.FindLinearKind(assignCmd.Lhss[i].DeepAssignedVariable) == LinearKind.ORDINARY)
            {
              continue;
            }
            IdentifierExpr ie = assignCmd.Rhss[i] as IdentifierExpr;
            if (!start.Contains(ie.Decl))
            {
              Error(ie, "unavailable source for a linear read");
            }
            else
            {
              start.Remove(ie.Decl);
            }
          }
          assignCmd.Lhss
            .Where(assignLhs =>
              LinearDomainCollector.FindLinearKind(assignLhs.DeepAssignedVariable) != LinearKind.ORDINARY)
            .Iter(assignLhs => start.Add(assignLhs.DeepAssignedVariable));
        }
        else if (cmd is CallCmd callCmd)
        {
          linearGlobalVariables.Except(start).Iter(g =>
          {
            Error(cmd, $"Global variable {g.Name} must be available at a call");
          });
          for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
          {
            Variable param = callCmd.Proc.InParams[i];
            LinearKind paramKind = LinearDomainCollector.FindLinearKind(param);
            if (paramKind == LinearKind.ORDINARY)
            {
              continue;
            }
            IdentifierExpr ie = callCmd.Ins[i] as IdentifierExpr;
            if (start.Contains(ie.Decl))
            {
              if (callCmd.IsAsync || paramKind == LinearKind.LINEAR_IN)
              {
                start.Remove(ie.Decl);
              }
            }
            else
            {
              if (paramKind == LinearKind.LINEAR_OUT)
              {
                start.Add(ie.Decl);
              }
              else
              {
                Error(ie, "unavailable source for a linear read");
              }
            }
          }
          AddAvailableVars(callCmd, start);
          availableLinearVars[callCmd] = new HashSet<Variable>(start);
        }
        else if (cmd is ParCallCmd parCallCmd)
        {
          linearGlobalVariables.Except(start).Iter(g =>
          {
            Error(cmd, $"Global variable {g.Name} must be available at a call");
          });
          foreach (CallCmd parCallCallCmd in parCallCmd.CallCmds)
          {
            for (int i = 0; i < parCallCallCmd.Proc.InParams.Count; i++)
            {
              Variable param = parCallCallCmd.Proc.InParams[i];
              LinearKind paramKind = LinearDomainCollector.FindLinearKind(param);
              if (paramKind == LinearKind.ORDINARY)
              {
                continue;
              }
              IdentifierExpr ie = parCallCallCmd.Ins[i] as IdentifierExpr;
              if (start.Contains(ie.Decl))
              {
                if (paramKind == LinearKind.LINEAR_IN)
                {
                  start.Remove(ie.Decl);
                }
              }
              else
              {
                if (paramKind == LinearKind.LINEAR_OUT)
                {
                  start.Add(ie.Decl);
                }
                else
                {
                  Error(ie, "unavailable source for a linear read");
                }
              }
            }
          }
          AddAvailableVars(parCallCmd, start);
          availableLinearVars[parCallCmd] = new HashSet<Variable>(start);
        }
        else if (cmd is HavocCmd havocCmd)
        {
          havocCmd.Vars.Where(ie => LinearDomainCollector.FindLinearKind(ie.Decl) != LinearKind.ORDINARY)
            .Iter(ie => start.Remove(ie.Decl));
        }
        else if (cmd is YieldCmd)
        {
          linearGlobalVariables.Except(start).Iter(g =>
          {
            Error(cmd, $"Global variable {g.Name} must be available at a yield");
          });
          availableLinearVars[cmd] = new HashSet<Variable>(start);
        }
      }

      return start;
    }
    
    public override Cmd VisitAssignCmd(AssignCmd node)
    {
      HashSet<Variable> rhsVars = new HashSet<Variable>();
      for (int i = 0; i < node.Lhss.Count; i++)
      {
        AssignLhs lhs = node.Lhss[i];
        Variable lhsVar = lhs.DeepAssignedVariable;
        string domainName = LinearDomainCollector.FindDomainName(lhsVar);
        if (domainName == null)
        {
          continue;
        }
        if (!(lhs is SimpleAssignLhs))
        {
          Error(node, $"Only simple assignment allowed on linear variable {lhsVar.Name}");
          continue;
        }
        IdentifierExpr rhs = node.Rhss[i] as IdentifierExpr;
        if (rhs == null)
        {
          Error(node, $"Only variable can be assigned to linear variable {lhsVar.Name}");
          continue;
        }
        string rhsDomainName = LinearDomainCollector.FindDomainName(rhs.Decl);
        if (rhsDomainName == null)
        {
          Error(node, $"Only linear variable can be assigned to linear variable {lhsVar.Name}");
          continue;
        }
        if (domainName != rhsDomainName)
        {
          Error(node,
            $"Linear variable of domain {rhsDomainName} cannot be assigned to linear variable of domain {domainName}");
          continue;
        }
        if (rhsVars.Contains(rhs.Decl))
        {
          Error(node, $"Linear variable {rhs.Decl.Name} can occur only once in the right-hand-side of an assignment");
          continue;
        }
        rhsVars.Add(rhs.Decl);
      }
      return base.VisitAssignCmd(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      HashSet<Variable> inVars = new HashSet<Variable>();
      for (int i = 0; i < node.Proc.InParams.Count; i++)
      {
        Variable formal = node.Proc.InParams[i];
        string domainName = LinearDomainCollector.FindDomainName(formal);
        if (domainName == null)
        {
          continue;
        }
        IdentifierExpr actual = node.Ins[i] as IdentifierExpr;
        if (actual == null)
        {
          Error(node.Ins[i], $"Only variable can be passed to linear parameter {formal.Name}");
          continue;
        }
        string actualDomainName = LinearDomainCollector.FindDomainName(actual.Decl);
        if (actualDomainName == null)
        {
          Error(actual, $"Only a linear argument can be passed to linear parameter {formal.Name}");
          continue;
        }
        if (domainName != actualDomainName)
        {
          Error(actual, "The domains of formal and actual parameters must be the same");
          continue;
        }
        if (actual.Decl is GlobalVariable)
        {
          Error(actual, "Only local linear variable can be an actual input parameter of a procedure call");
          continue;
        }
        if (inVars.Contains(actual.Decl))
        {
          Error(node, $"Linear variable {actual.Decl.Name} can occur only once as an input parameter");
          continue;
        }
        inVars.Add(actual.Decl);
      }

      for (int i = 0; i < node.Proc.OutParams.Count; i++)
      {
        IdentifierExpr actual = node.Outs[i];
        string actualDomainName = LinearDomainCollector.FindDomainName(actual.Decl);
        if (actualDomainName == null)
        {
          continue;
        }
        Variable formal = node.Proc.OutParams[i];
        string domainName = LinearDomainCollector.FindDomainName(formal);
        if (domainName == null)
        {
          Error(node, "Only a linear variable can be passed to a linear parameter");
          continue;
        }
        if (domainName != actualDomainName)
        {
          Error(node, "The domains of formal and actual parameters must be the same");
          continue;
        }
        if (actual.Decl is GlobalVariable)
        {
          Error(node, "Only local linear variable can be actual output parameter of a procedure call");
        }
      }
      return base.VisitCallCmd(node);
    }

    public override Variable VisitVariable(Variable node)
    {
      var kind = LinearDomainCollector.FindLinearKind(node);
      if ((kind == LinearKind.LINEAR_IN || kind == LinearKind.LINEAR_OUT) && 
          (node is GlobalVariable || node is LocalVariable || (node is Formal formal && !formal.InComing)))
      {
        checkingContext.Error(node, "Variable must be declared linear (as opposed to linear_in or linear_out)");
      }
      return node;
    }

    #endregion

    #region Useful public methods
    
    public IEnumerable<LinearDomain> NamedLinearDomains => domainNameToLinearDomain.Values;

    public IEnumerable<LinearDomain> LinearDomains => domainNameToLinearDomain.Values.Union(linearTypeToLinearDomain.Values);
    
    public LinearDomain FindDomain(Variable v)
    {
      var domainName = LinearDomainCollector.FindDomainName(v);
      if (domainName == null)
      {
        return linearTypeToLinearDomain[v.TypedIdent.Type];
      }
      return domainNameToLinearDomain[domainName];
    }

    public Formal LinearDomainInFormal(LinearDomain domain)
    {
      return civlTypeChecker.Formal("linear_" + domain.DomainName + "_in", domain.mapTypeBool, true);
    }

    public LocalVariable LinearDomainAvailableLocal(LinearDomain domain)
    {
      return civlTypeChecker.LocalVariable("linear_" + domain.DomainName + "_available", domain.mapTypeBool);
    }

    public void TypeCheck(Dictionary<string, LinearDomain> domainNameToLinearDomain, Dictionary<Type, LinearDomain> linearTypeToLinearDomain)
    {
      this.domainNameToLinearDomain = domainNameToLinearDomain;
      this.linearTypeToLinearDomain = linearTypeToLinearDomain;
      this.VisitProgram(program);
      foreach (var absy in this.availableLinearVars.Keys)
      {
        availableLinearVars[absy].RemoveWhere(v => v is GlobalVariable);
      }
    }

    public ISet<Variable> AvailableLinearVars(Absy absy)
    {
      if (availableLinearVars.ContainsKey(absy))
      {
        return availableLinearVars[absy];
      }
      else
      {
        return new HashSet<Variable>();
      }
    }

    public IEnumerable<Expr> DisjointnessExprForEachDomain(IEnumerable<Variable> scope)
    {
      var domainToScope = LinearDomains.ToDictionary(domain => domain, _ => new HashSet<Variable>());
      scope.Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.ORDINARY).Iter(v => domainToScope[FindDomain(v)].Add(v));
      foreach (var domain in domainToScope.Keys)
      {
        yield return DisjointnessExprForPermissions(
          domain,
          PermissionExprForEachVariable(domain, domainToScope[domain]));
      }
    }

    public IEnumerable<Expr> PermissionExprForEachVariable(LinearDomain domain, IEnumerable<Variable> scope)
    {
      foreach (Variable v in scope)
      {
        Expr expr = ExprHelper.FunctionCall(domain.collectors[v.TypedIdent.Type], Expr.Ident(v));
        yield return expr;
      }
    }

    private ConcurrencyOptions Options => civlTypeChecker.Options;

    public Expr DisjointnessExprForPermissions(LinearDomain domain, IEnumerable<Expr> permissionsExprs)
    {
      Expr expr = Expr.True;
      if (permissionsExprs.Count() > 1)
      {
        int count = 0;
        List<Expr> subsetExprs = new List<Expr>();
        BoundVariable partition = civlTypeChecker.BoundVariable($"partition_{domain.DomainName}", domain.mapTypeInt);
        foreach (Expr e in permissionsExprs)
        {
          subsetExprs.Add(SubsetExpr(domain, e, partition, count));
          count++;
        }

        expr = ExprHelper.ExistsExpr(new List<Variable> {partition}, Expr.And(subsetExprs));
      }
      return expr;
    }

    public Expr UnionExprForPermissions(LinearDomain domain, IEnumerable<Expr> permissionExprs)
    {
      var expr = ExprHelper.FunctionCall(domain.mapConstBool, Expr.False);
      foreach (Expr e in permissionExprs)
      {
        expr = ExprHelper.FunctionCall(domain.mapOr, e, expr);
      }
      return expr;
    }

    private Expr SubsetExpr(LinearDomain domain, Expr ie, Variable partition, int partitionCount)
    {
      Expr e = ExprHelper.FunctionCall(domain.mapConstInt, Expr.Literal(partitionCount));
      e = ExprHelper.FunctionCall(domain.mapEqInt, Expr.Ident(partition), e);
      e = ExprHelper.FunctionCall(domain.mapImp, ie, e);
      e = Expr.Eq(e, ExprHelper.FunctionCall(domain.mapConstBool, Expr.True));
      return e;
    }

    #endregion

    #region Annotation Eraser

    public void EraseLinearAnnotations()
    {
      new LinearTypeEraser().VisitProgram(program);
    }

    public class LinearTypeEraser : ReadOnlyVisitor
    {
      public override Variable VisitVariable(Variable node)
      {
        CivlAttributes.RemoveLinearAttributes(node);
        return base.VisitVariable(node);
      }

      public override Function VisitFunction(Function node)
      {
        CivlAttributes.RemoveLinearAttributes(node);
        return base.VisitFunction(node);
      }

      public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
      {
        CivlAttributes.RemoveLinearAttributes(node);
        return base.VisitTypeCtorDecl(node);
      }

      public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
      {
        CivlAttributes.RemoveLinearAttributes(node);
        return base.VisitTypeSynonymDecl(node);
      }
    }

    #endregion
  }
}
