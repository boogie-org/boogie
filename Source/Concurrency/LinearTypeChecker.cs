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
      // other fields are initialized in the TypeCheck method
    }
    
    #region Visitor Implementation

    private IEnumerable<Variable> LinearGlobalVariables =>
      program.GlobalVariables.Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.ORDINARY);
    
    private Procedure enclosingProc;

    public override Implementation VisitImplementation(Implementation node)
    {
      enclosingProc = node.Proc;
      
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
            if (SkipCheck(v))
            {
              return false;
            }
            var kind = LinearDomainCollector.FindLinearKind(v);
            return kind == LinearKind.LINEAR || kind == LinearKind.LINEAR_OUT;
          }).Iter(v => { Error(b.TransferCmd, $"Input variable {v.Name} must be available at a return"); });
          node.OutParams.Except(end).Where(v => !SkipCheck(v))
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
            var lhsVar = assignCmd.Lhss[i].DeepAssignedVariable;
            if (SkipCheck(lhsVar))
            {
              continue;
            }
            var rhsExpr = assignCmd.Rhss[i];
            var lhsDomainName = LinearDomainCollector.FindDomainName(lhsVar);
            if (rhsExpr is IdentifierExpr ie)
            {
              if (!start.Contains(ie.Decl))
              {
                Error(ie, "unavailable source for a linear read");
              }
              else
              {
                start.Remove(ie.Decl);
              }
            }
            else
            {
              // pack
              var args = ((NAryExpr)rhsExpr).Args.Cast<IdentifierExpr>().Select(arg => arg.Decl)
                .Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.ORDINARY);
              if (args.Any(v => !start.Contains(v)))
              {
                Error(rhsExpr, "unavailable source for a linear read");
              }
              else
              {
                start.ExceptWith(args);
              }
            }
          }
          assignCmd.Lhss
            .Where(assignLhs =>
              LinearDomainCollector.FindLinearKind(assignLhs.DeepAssignedVariable) != LinearKind.ORDINARY)
            .Iter(assignLhs => start.Add(assignLhs.DeepAssignedVariable));
        }
        else if (cmd is UnpackCmd unpackCmd)
        {
          if (unpackCmd.UnpackedLhs.Any(arg => !SkipCheck(arg.Decl)))
          {
            var ie = unpackCmd.Rhs as IdentifierExpr;
            if (!start.Contains(ie.Decl))
            {
              Error(ie, "unavailable source for a linear read");
            }
            else
            {
              start.Remove(ie.Decl);
              unpackCmd.UnpackedLhs
                .Where(arg => LinearDomainCollector.FindLinearKind(arg.Decl) != LinearKind.ORDINARY)
                .Iter(arg => start.Add(arg.Decl));
            }
          }
        }
        else if (cmd is CallCmd callCmd)
        {
          if (!IsPrimitive(callCmd.Proc))
          {
            linearGlobalVariables.Except(start).Iter(g =>
            {
              Error(cmd, $"Global variable {g.Name} must be available at a call");
            });
          }
          for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
          {
            Variable param = callCmd.Proc.InParams[i];
            LinearKind paramKind = LinearDomainCollector.FindLinearKind(param);
            if (paramKind == LinearKind.ORDINARY)
            {
              continue;
            }
            var ie = IsPrimitive(callCmd.Proc) && paramKind == LinearKind.LINEAR
              ? ExtractRootFromAccessPathExpr(callCmd.Ins[i])
              : callCmd.Ins[i] as IdentifierExpr;
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
                Error(ie, $"unavailable source {ie} for linear parameter at position {i}");
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
                  Error(ie, $"unavailable source {ie} for linear parameter at position {i}");
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

    private bool IsPrimitive(DeclWithFormals decl)
    {
      if (program.monomorphizer == null)
      {
        return false;
      }
      return LinearRewriter.IsPrimitive(program.monomorphizer.GetOriginalDecl(decl));
    }
    
    private LinearDomain FindDomain(Variable v)
    {
      var domainName = LinearDomainCollector.FindDomainName(v);
      if (domainName != null)
      {
        return domainNameToLinearDomain[domainName];
      }
      if (linearTypeToLinearDomain.ContainsKey(v.TypedIdent.Type))
      {
        return linearTypeToLinearDomain[v.TypedIdent.Type];
      }
      return null;
    }
    
    // SkipCheck is selectively applied at a few places to allow the type checker 
    // to be used whether the code uses name or type domains.
    private bool SkipCheck(Variable v)
    {
      var lhsKind = LinearDomainCollector.FindLinearKind(v);
      if (lhsKind == LinearKind.ORDINARY)
      {
        return true;
      }
      if (LinearDomainCollector.FindDomainName(v) == null)
      {
        return false;
      }
      return civlTypeChecker.IsAction(enclosingProc) || civlTypeChecker.IsLemmaProcedure(enclosingProc);
    }

    private IdentifierExpr ExtractRootFromAccessPathExpr(Expr expr)
    {
      if (expr is IdentifierExpr identifierExpr)
      {
        return identifierExpr;
      }
      if (expr is NAryExpr nAryExpr)
      {
        if (nAryExpr.Fun is FieldAccess)
        {
          return ExtractRootFromAccessPathExpr(nAryExpr.Args[0]);
        }
        if (nAryExpr.Fun is MapSelect)
        {
          var mapExpr = nAryExpr.Args[0];
          if (mapExpr is NAryExpr lmapValExpr &&
              lmapValExpr.Fun is FieldAccess &&
              lmapValExpr.Args[0].Type is CtorType ctorType &&
              program.monomorphizer.GetOriginalDecl(ctorType.Decl).Name == "Lmap")
          {
            return ExtractRootFromAccessPathExpr(lmapValExpr.Args[0]);
          }
        }
      }
      return null;
    }
    
    private IdentifierExpr ModifiedArgument(CallCmd callCmd)
    {
      switch (program.monomorphizer.GetOriginalDecl(callCmd.Proc).Name)
      {
        case "Lmap_Empty":
          return null;
        case "Lmap_Split":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[1]);
        case "Lmap_Transfer":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[1]);
        case "Lmap_Read":
          return null;
        case "Lmap_Write":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[0]);
        case "Lmap_Add":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[0]);
        case "Lmap_Remove":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[0]);
        case "Lset_Empty":
          return null;
        case "Lset_Split":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[1]);
        case "Lset_Transfer":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[1]);
        case "Lval_Split":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[1]);
        case "Lval_Transfer":
          return ExtractRootFromAccessPathExpr(callCmd.Ins[1]);
        default:
          throw new cce.UnreachableException();
      }
    }

    public override Cmd VisitAssignCmd(AssignCmd node)
    {
      HashSet<Variable> rhsVars = new HashSet<Variable>();
      for (int i = 0; i < node.Lhss.Count; i++)
      {
        var lhs = node.Lhss[i];
        var lhsVar = lhs.DeepAssignedVariable;
        if (SkipCheck(lhsVar))
        {
          continue;
        }
        if (!(lhs is SimpleAssignLhs))
        {
          Error(node, $"Only simple assignment allowed on linear variable {lhsVar.Name}");
          continue;
        }
        var rhsExpr = node.Rhss[i];
        var lhsDomainName = LinearDomainCollector.FindDomainName(lhsVar);
        if (rhsExpr is IdentifierExpr rhs)
        {
          var rhsKind = LinearDomainCollector.FindLinearKind(rhs.Decl);
          if (rhsKind == LinearKind.ORDINARY)
          {
            Error(node, $"Only linear variable can be assigned to linear variable {lhsVar.Name}");
            continue;
          }
          if (LinearDomainCollector.FindDomainName(lhsVar) != LinearDomainCollector.FindDomainName(rhs.Decl))
          {
            Error(node, "The domains of source and target of assignment must be the same");
            continue;
          }
          if (rhsVars.Contains(rhs.Decl))
          {
            Error(node, $"Linear variable {rhs.Decl.Name} can occur only once in the right-hand-side of an assignment");
            continue;
          }
          rhsVars.Add(rhs.Decl);
        }
        else if (lhsDomainName == null && rhsExpr is NAryExpr nAryExpr && nAryExpr.Fun is FunctionCall functionCall && functionCall.Func is DatatypeConstructor)
        {
          // pack
          var args = nAryExpr.Args.OfType<IdentifierExpr>();
          if (args.Count() < nAryExpr.Args.Count)
          {
            Error(node, $"A source of pack must be a variable");
          }
          else if (args.Any(arg => LinearDomainCollector.FindDomainName(arg.Decl) != null))
          {
            Error(node, $"A target of pack must not be a linear variable of name domain");
          }
          else
          {
            rhsVars.UnionWith(args.Select(arg => arg.Decl)
              .Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.ORDINARY));
          }
        }
        else
        {
          Error(node, $"Only variable can be assigned to linear variable {lhsVar.Name}");
        }
      }
      return base.VisitAssignCmd(node);
    }

    public override Cmd VisitUnpackCmd(UnpackCmd node)
    {
      if (node.UnpackedLhs.Any(arg => !SkipCheck(arg.Decl)))
      {
        if (node.UnpackedLhs.Any(arg => LinearDomainCollector.FindDomainName(arg.Decl) != null))
        {
          Error(node, $"A target of unpack must not be a linear variable of name domain");
        }
        else
        {
          IdentifierExpr rhs = node.Rhs as IdentifierExpr;
          if (rhs == null || LinearDomainCollector.FindLinearKind(rhs.Decl) == LinearKind.ORDINARY)
          {
            Error(node, $"The source for unpack must be a linear variable");
          }
          else if (LinearDomainCollector.FindDomainName(rhs.Decl) != null)
          {
            Error(node, $"The source for unpack must be a linear variable of type domain");
          }
        }
      }
      return base.VisitUnpackCmd(node);
    }
    
    public override Cmd VisitParCallCmd(ParCallCmd node)
    {
      if (node.CallCmds.Any(callCmd => IsPrimitive(callCmd.Proc)))
      {
        Error(node, "linear primitives may not be invoked in a parallel call");
        return node;
      }
      return base.VisitParCallCmd(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      var isPrimitive = IsPrimitive(node.Proc);
      HashSet<Variable> inVars = new HashSet<Variable>();
      for (int i = 0; i < node.Proc.InParams.Count; i++)
      {
        var formal = node.Proc.InParams[i];
        var formalKind = LinearDomainCollector.FindLinearKind(formal);
        if (formalKind == LinearKind.ORDINARY)
        {
          continue;
        }
        var isLinearParamInPrimitiveCall = isPrimitive && formalKind == LinearKind.LINEAR;
        var actual = isLinearParamInPrimitiveCall ? ExtractRootFromAccessPathExpr(node.Ins[i]) : node.Ins[i] as IdentifierExpr;
        if (actual == null)
        {
          if (isLinearParamInPrimitiveCall)
          {
            Error(node, $"Invalid access path expression passed to linear parameter: {node.Ins[i]}");
          }
          else
          {
            Error(node, $"Only variable can be passed to linear parameter: {node.Ins[i]}");
          }
          continue;
        }
        var actualKind = LinearDomainCollector.FindLinearKind(actual.Decl);
        if (actualKind == LinearKind.ORDINARY)
        {
          Error(node, $"Only linear variable can be passed to linear parameter: {actual}");
          continue;
        }
        if (LinearDomainCollector.FindDomainName(formal) != LinearDomainCollector.FindDomainName(actual.Decl))
        {
          Error(node, $"The domains of parameter {formal} and argument {actual} must be the same");
          continue;
        }
        if (actual.Decl is GlobalVariable && !IsPrimitive(node.Proc))
        {
          Error(node, $"Only local linear variable can be an argument to a procedure call: {actual}");
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
        var actualKind = LinearDomainCollector.FindLinearKind(actual.Decl);
        if (actualKind == LinearKind.ORDINARY)
        {
          continue;
        }
        Variable formal = node.Proc.OutParams[i];
        var formalKind = LinearDomainCollector.FindLinearKind(formal);
        if (formalKind == LinearKind.ORDINARY)
        {
          Error(node, "Only a linear variable can be passed to a linear parameter");
          continue;
        }
        if (LinearDomainCollector.FindDomainName(formal) != LinearDomainCollector.FindDomainName(actual.Decl))
        {
          Error(node, "The domains of formal and actual parameters must be the same");
        }
      }

      if (isPrimitive)
      {
        var modifiedArgument = ModifiedArgument(node)?.Decl;
        if (modifiedArgument != null)
        {
          if (modifiedArgument is Formal formal && formal.InComing)
          {
            Error(node, $"Primitive assigns to input variable: {formal}");
          }
          else if (modifiedArgument is GlobalVariable &&
                   !civlTypeChecker.IsYieldingProcedure(enclosingProc) &&
                   enclosingProc.Modifies.All(v => v.Decl != modifiedArgument))
          {
            Error(node,
              $"Primitive assigns to a global variable that is not in the enclosing procedure's modifies clause: {modifiedArgument}");
          }
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
    
    public IEnumerable<LinearDomain> NameLinearDomains => domainNameToLinearDomain.Values;

    public IEnumerable<LinearDomain> TypeLinearDomains => linearTypeToLinearDomain.Values;

    public IEnumerable<LinearDomain> LinearDomains => domainNameToLinearDomain.Values.Union(linearTypeToLinearDomain.Values);

    public void TypeCheck()
    {
      (this.domainNameToLinearDomain, this.linearTypeToLinearDomain) = LinearDomainCollector.Collect(program, checkingContext);
      this.availableLinearVars = new Dictionary<Absy, HashSet<Variable>>();
      this.VisitProgram(program);
      foreach (var absy in this.availableLinearVars.Keys)
      {
        availableLinearVars[absy].RemoveWhere(v => v is GlobalVariable);
      }
      if (checkingContext.ErrorCount == 0 && program.monomorphizer != null)
      {
        var impls = program.TopLevelDeclarations.OfType<Implementation>().ToList();
        impls.Iter(impl =>
        {
          int? LayerNum(Procedure proc)
          {
            if (!civlTypeChecker.IsYieldingProcedure(proc))
            {
              return null;
            }
            var layers = civlTypeChecker.FindLayers(proc.Attributes);
            if (layers.Count == 0)
            {
              return null;
            }
            return layers[0];
          }
          var linearRewriter = new LinearRewriter(civlTypeChecker.Options, program.monomorphizer, impl.Proc.Modifies, LayerNum(impl.Proc));
          impl.Blocks.Iter(block => block.Cmds = linearRewriter.RewriteCmdSeq(block.Cmds));
        }); 
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

    public IEnumerable<Variable> FilterVariables(LinearDomain domain, IEnumerable<Variable> scope)
    {
      return scope.Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.ORDINARY && FindDomain(v) == domain);
    }
    
    public IEnumerable<Expr> DisjointnessExprForEachDomain(IEnumerable<Variable> scope)
    {
      return LinearDomains.Select(domain =>
        DisjointnessExprForPermissions(domain, PermissionExprForEachVariable(domain, FilterVariables(domain, scope))));
    }

    public Dictionary<LinearDomain, IEnumerable<Expr>> PermissionExprs(IEnumerable<Variable> availableVars)
    {
      return LinearDomains.ToDictionary<LinearDomain, LinearDomain, IEnumerable<Expr>>(domain => domain,
        domain => PermissionExprForEachVariable(domain, availableVars));
    }

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

    private IEnumerable<Expr> PermissionExprForEachVariable(LinearDomain domain, IEnumerable<Variable> scope)
    {
      return FilterVariables(domain, scope)
        .Select(v => ExprHelper.FunctionCall(domain.collectors[v.TypedIdent.Type], Expr.Ident(v)));
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
