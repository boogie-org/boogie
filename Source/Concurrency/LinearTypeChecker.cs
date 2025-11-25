using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class LinearTypeChecker : ReadOnlyVisitor
  {
    public static LinearKind[] InKinds = {LinearKind.LINEAR, LinearKind.LINEAR_IN};
    public static LinearKind[] OutKinds = {LinearKind.LINEAR, LinearKind.LINEAR_OUT};

    public Program program;
    private CheckingContext checkingContext;
    private CivlTypeChecker civlTypeChecker;
    private Dictionary<Type, ActionDecl> pendingAsyncTypeToActionDecl;
    private Dictionary<Type, LinearDomain> permissionTypeToLinearDomain;
    private Dictionary<Type, Dictionary<Type, Function>> collectors;
    private Dictionary<Absy, HashSet<Variable>> availableLinearVars;

    public LinearTypeChecker(CivlTypeChecker civlTypeChecker)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.program = civlTypeChecker.program;
      this.checkingContext = civlTypeChecker.checkingContext;
      this.pendingAsyncTypeToActionDecl = new ();
      foreach (var actionDecl in program.TopLevelDeclarations.OfType<ActionDecl>().Where(actionDecl => actionDecl.MaybePendingAsync))
      {
        pendingAsyncTypeToActionDecl[actionDecl.PendingAsyncType] = actionDecl;
      }
      // other fields are initialized in the TypeCheck method
    }

    #region Visitor Implementation

    private IEnumerable<Variable> LinearGlobalVariables =>
      program.GlobalVariables.Where(v => FindLinearKind(v) != LinearKind.ORDINARY);
    
    private Procedure enclosingProc;

    private void Error(Absy node, string message)
    {
      checkingContext.Error(node, message);
    }
    
    private bool IsOrdinaryType(Type type)
    {
      return !collectors.ContainsKey(type);
    }

    private bool IsOrdinary(Variable v)
    {
      return IsOrdinaryType(v.TypedIdent.Type) || FindLinearKind(v) == LinearKind.ORDINARY;
    }

    private static bool IsPrimitiveLinearType(Type type)
    {
      if (type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(datatypeTypeCtorDecl);
        var typeName = originalTypeCtorDecl.Name;
        return typeName == "One" || typeName == "Set" || typeName == "Map";
      }
      return false;
    }

    private static void AddAvailableVars(CallCmd callCmd, HashSet<Variable> start)
    {
      callCmd.Outs.Where(ie => FindLinearKind(ie.Decl) != LinearKind.ORDINARY)
        .ForEach(ie => start.Add(ie.Decl));
      for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
      {
        if (callCmd.Ins[i] is IdentifierExpr ie)
        {
          if (FindLinearKind(callCmd.Proc.InParams[i]) == LinearKind.LINEAR_OUT)
          {
            start.Add(ie.Decl);
          }
        }
      }
    }

    private static void AddAvailableVars(ParCallCmd parCallCmd, HashSet<Variable> start)
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
          var lhsVarsToAdd = new HashSet<Variable>();
          for (int i = 0; i < assignCmd.Lhss.Count; i++)
          {
            var lhs = assignCmd.Lhss[i];
            var lhsVar = lhs.DeepAssignedVariable;
            // assignment may violate the disjointness invariant
            // therefore, drop lhsVar from the set of available variables
            // but possibly add it to lhsVarsToAdd (added to start later)
            start.Remove(lhsVar);
            if (lhs is not SimpleAssignLhs || IsOrdinaryType(lhs.Type))
            {
              continue;
            }
            var rhsExpr = assignCmd.Rhss[i];
            if (rhsExpr is IdentifierExpr ie)
            {
              if (start.Contains(ie.Decl))
              {
                start.Remove(ie.Decl);
                lhsVarsToAdd.Add(lhsVar);
              }
            }
            else if (rhsExpr is NAryExpr { Fun: FunctionCall { Func: DatatypeConstructor constructor } } nAryExpr &&
                      !IsPrimitiveLinearType(rhsExpr.Type))
            {
              // pack
              for (int j = 0; j < constructor.InParams.Count; j++)
              {
                var field = constructor.InParams[j];
                if (IsOrdinaryType(field.TypedIdent.Type))
                {
                  continue;
                }
                var arg = nAryExpr.Args[j];
                if (arg is IdentifierExpr { Decl: Variable v })
                {
                  start.Remove(v);
                }
              }
              lhsVarsToAdd.Add(lhsVar);
            }
          }
          start.UnionWith(lhsVarsToAdd);
        }
        else if (cmd is UnpackCmd unpackCmd)
        {
          if (!IsOrdinaryType(unpackCmd.Rhs.Type))
          {
            var ie = unpackCmd.Rhs as IdentifierExpr;
            if (start.Contains(ie.Decl))
            {
              start.Remove(ie.Decl);
              unpackCmd.UnpackedLhs
                .Where(arg => !IsOrdinaryType(arg.Type))
                .ForEach(arg => start.Add(arg.Decl));
            }
          }
        }
        else if (cmd is CallCmd callCmd)
        {
          var isPrimitive = CivlPrimitives.IsPrimitive(callCmd.Proc);
          if (!isPrimitive)
          {
            linearGlobalVariables.Except(start).ForEach(g =>
            {
              Error(cmd, $"global variable {g.Name} must be available at a call");
            });
          }
          for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
          {
            Variable param = callCmd.Proc.InParams[i];
            if (IsOrdinary(param))
            {
              continue;
            }
            LinearKind paramKind = FindLinearKind(param);
            var ie = isPrimitive && paramKind == LinearKind.LINEAR
                      ? CivlPrimitives.ExtractRootFromAccessPathExpr(callCmd.Ins[i])
                      : callCmd.Ins[i] as IdentifierExpr;
            if (paramKind == LinearKind.LINEAR_OUT)
            {
              start.Add(ie.Decl);
            }
            else if (start.Contains(ie.Decl))
            {
              if (callCmd.IsAsync || paramKind == LinearKind.LINEAR_IN)
              {
                start.Remove(ie.Decl);
              }
            }
            else
            {
              Error(ie, $"unavailable source {ie} for linear parameter at position {i}");
            }
          }
          var originalProc = (Procedure)Monomorphizer.GetOriginalDecl(callCmd.Proc);
          if (originalProc.Name == "create_asyncs")
          {
            var attr = QKeyValue.FindAttribute(callCmd.Attributes, x => x.Key == "linear");
            if (attr != null)
            {
              attr.Params.OfType<IdentifierExpr>().ForEach(ie => {
                if (start.Contains(ie.Decl))
                {
                  start.Remove(ie.Decl);
                }
                else
                {
                  Error(ie, $"unavailable linear source");
                }
              });
            }
          }
          AddAvailableVars(callCmd, start);
          availableLinearVars[callCmd] = new HashSet<Variable>(start);
        }
        else if (cmd is ParCallCmd parCallCmd)
        {
          linearGlobalVariables.Except(start).ForEach(g =>
          {
            Error(cmd, $"global variable {g.Name} must be available at a call");
          });
          foreach (CallCmd parCallCallCmd in parCallCmd.CallCmds)
          {
            for (int i = 0; i < parCallCallCmd.Proc.InParams.Count; i++)
            {
              Variable param = parCallCallCmd.Proc.InParams[i];
              LinearKind paramKind = FindLinearKind(param);
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
          havocCmd.Vars.Where(ie => FindLinearKind(ie.Decl) != LinearKind.ORDINARY)
            .ForEach(ie => start.Remove(ie.Decl));
        }
      }

      return start;
    }

    public override Procedure VisitYieldInvariantDecl(YieldInvariantDecl node)
    {
      foreach (var v in node.InParams)
      {
        var linearKind = FindLinearKind(v);
        if (linearKind == LinearKind.LINEAR_IN || linearKind == LinearKind.LINEAR_OUT)
        {
          Error(v, "parameter to yield invariant may only be :linear");
        }
      }
      return base.VisitYieldInvariantDecl(node);
    }

    public override Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
    {
      node.YieldRequires.ForEach(callCmd =>
      {
        var kinds = new List<LinearKind> { LinearKind.LINEAR, LinearKind.LINEAR_IN };
        CheckLinearParameters(callCmd,
          new HashSet<Variable>(node.InParams.Union(node.OutParams)
            .Where(p => kinds.Contains(FindLinearKind(p)))));
      });
      node.YieldEnsures.ForEach(callCmd =>
      {
        var kinds = new List<LinearKind> { LinearKind.LINEAR, LinearKind.LINEAR_OUT };
        CheckLinearParameters(callCmd,
          new HashSet<Variable>(node.InParams.Union(node.OutParams)
            .Where(p => kinds.Contains(FindLinearKind(p)))));
      });
      node.YieldPreserves.ForEach(callCmd =>
      {
        var kinds = new List<LinearKind> { LinearKind.LINEAR };
        CheckLinearParameters(callCmd,
          new HashSet<Variable>(node.InParams.Union(node.OutParams)
            .Where(p => kinds.Contains(FindLinearKind(p)))));
      });
      return base.VisitYieldProcedureDecl(node);
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      if (CivlPrimitives.IsPrimitive(node))
      {
        return node;
      }

      enclosingProc = node.Proc;
      
      node.PruneUnreachableBlocks(civlTypeChecker.Options);
      node.ComputePredecessorsForBlocks();
      GraphUtil.Graph<Block> graph = Program.GraphFromImpl(node);
      graph.ComputeLoops();

      var linearGlobalVariables = LinearGlobalVariables;
      HashSet<Variable> start = new HashSet<Variable>(linearGlobalVariables.Union(node.InParams.Where(v =>
      {
        var kind = FindLinearKind(v);
        return kind == LinearKind.LINEAR || kind == LinearKind.LINEAR_IN;
      })));

      var oldErrorCount = checkingContext.ErrorCount;
      // Visit relevant fields of node directly rather than calling VisitImplementation to
      // avoid visiting node.Proc (which would cause Procedure's to be visited more than once)
      VisitVariableSeq(node.LocVars);
      VisitBlockList(node.Blocks);
      var impl = (Implementation) this.VisitDeclWithFormals(node);
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
          foreach (Block target in gotoCmd.LabelTargets)
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
          linearGlobalVariables.Except(end).Where(v => !IsOrdinary(v)).ForEach(g =>
          {
            Error(b.TransferCmd, $"global variable {g.Name} must be available at a return");
          });
          node.InParams.Except(end).Where(v =>
          {
            var kind = FindLinearKind(v);
            return kind == LinearKind.LINEAR || kind == LinearKind.LINEAR_OUT;
          }).Where(v => !IsOrdinary(v)).ForEach(v => 
          { 
            Error(b.TransferCmd, $"input variable {v.Name} must be available at a return");
          });
          node.OutParams.Except(end).Where(v => !IsOrdinary(v)).ForEach(v =>
          {
            Error(b.TransferCmd, $"output variable {v.Name} must be available at a return");
          });
        }
      }

      if (graph.Reducible)
      {
        foreach (Block header in graph.Headers)
        {
          foreach (GlobalVariable g in linearGlobalVariables.Except(availableLinearVars[header]))
          {
            Error(header, $"global variable {g.Name} must be available at a loop head");
          }
        }
      }

      return impl;
    }

    public override Cmd VisitAssignCmd(AssignCmd node)
    {
      HashSet<Variable> rhsVars = new HashSet<Variable>();
      for (int i = 0; i < node.Lhss.Count; i++)
      {
        var lhs = node.Lhss[i];
        if (lhs is not SimpleAssignLhs || IsOrdinaryType(lhs.Type))
        {
          continue;
        }
        var rhsExpr = node.Rhss[i];
        if (rhsExpr is IdentifierExpr rhs)
        {
          if (rhsVars.Contains(rhs.Decl))
          {
            Error(rhs, $"linear variable {rhs.Decl.Name} can occur at most once as the source of an assignment");
          }
          else
          {
            rhsVars.Add(rhs.Decl);
          }
        }
        else if (rhsExpr is NAryExpr { Fun: FunctionCall { Func: DatatypeConstructor constructor } } nAryExpr &&
                  !IsPrimitiveLinearType(rhsExpr.Type))
        {
          // pack
          for (int j = 0; j < constructor.InParams.Count; j++)
          {
            var field = constructor.InParams[j];
            if (IsOrdinaryType(field.TypedIdent.Type))
            {
              continue;
            }
            var arg = nAryExpr.Args[j];
            if (arg is not IdentifierExpr ie)
            {
              Error(arg, $"pack argument for linear field {field} must be a variable");
            }
            else if (rhsVars.Contains(ie.Decl))
            {
              Error(arg, $"linear variable {ie.Decl.Name} can occur at most once as the source of an assignment");
            }
            else
            {
              rhsVars.Add(ie.Decl);
            }
          }
        }
      }
      return base.VisitAssignCmd(node);
    }

    public override Cmd VisitUnpackCmd(UnpackCmd node)
    {
      if (!IsOrdinaryType(node.Rhs.Type) && node.Rhs is not IdentifierExpr)
      {
        Error(node, $"source for unpack must be a linear variable");
      }
      return base.VisitUnpackCmd(node);
    }
    
    public override Cmd VisitCallCmd(CallCmd node)
    {
      var isPrimitive = CivlPrimitives.IsPrimitive(node.Proc);
      var inVars = new HashSet<Variable>();
      var globalInVars = new HashSet<Variable>();
      for (int i = 0; i < node.Proc.InParams.Count; i++)
      {
        var formal = node.Proc.InParams[i];
        var formalKind = FindLinearKind(formal);
        if (IsOrdinary(formal))
        {
          continue;
        }
        var isInoutLinearParamInPrimitiveCall = isPrimitive && formalKind == LinearKind.LINEAR;
        var actual = isInoutLinearParamInPrimitiveCall 
                      ? CivlPrimitives.ExtractRootFromAccessPathExpr(node.Ins[i]) 
                      : node.Ins[i] as IdentifierExpr;
        if (actual == null)
        {
          if (isInoutLinearParamInPrimitiveCall)
          {
            Error(node, $"invalid access path expression passed to inout linear parameter: {node.Ins[i]}");
          }
          else
          {
            Error(node, $"only variable can be passed to linear parameter: {node.Ins[i]}");
          }
          continue;
        }
        if (actual.Decl is GlobalVariable && !node.Proc.IsPure)
        {
          Error(node, $"only local linear variable can be an argument to a procedure call: {actual}");
          continue;
        }
        if (inVars.Contains(actual.Decl))
        {
          Error(node, $"linear variable {actual.Decl.Name} can occur only once as an input parameter");
          continue;
        }
        inVars.Add(actual.Decl);
        if (actual.Decl is GlobalVariable && formalKind == LinearKind.LINEAR_IN)
        {
          globalInVars.Add(actual.Decl);
        }
      }

      var globalOutVars = node.Outs.Select(ie => ie.Decl).ToHashSet();
      globalInVars.Except(globalOutVars).ForEach(v =>
      {
        Error(node, $"global variable passed as input to pure call but not received as output: {v}");
      });

      if (isPrimitive)
      {
        var modifiedArgument = CivlPrimitives.ModifiedArgument(node)?.Decl;
        if (modifiedArgument != null)
        {
          if (modifiedArgument is Formal formal && formal.InComing)
          {
            Error(node, $"primitive assigns to input variable: {formal}");
          }
          else if (node.Outs.Any(ie => ie.Decl == modifiedArgument))
          {
            Error(node, $"primitive assigns to input variable that is also an output variable: {modifiedArgument}");
          }
          else if (modifiedArgument is GlobalVariable &&
                    enclosingProc is not YieldProcedureDecl &&
                    enclosingProc.Modifies.All(v => v.Decl != modifiedArgument))
          {
            var str = enclosingProc is ActionDecl ? "action's" : "procedure's";
            Error(node,
              $"primitive assigns to a global variable that is not in the enclosing {str} modifies clause: {modifiedArgument}");
          }
        }
      }

      var originalProc = (Procedure)Monomorphizer.GetOriginalDecl(node.Proc);
      if (originalProc.Name == "create_multi_asyncs" || originalProc.Name == "create_asyncs")
      {
        var actionDecl = GetActionDeclFromCreateAsyncs(node);
        if (originalProc.Name == "create_multi_asyncs")
        {
          foreach (var inParam in actionDecl.InParams.Where(inParam => FindLinearKind(inParam) != LinearKind.ORDINARY))
          {
            Error(node, $"linear parameters not allowed on pending async");
          }
        }
        else if (originalProc.Name == "create_asyncs")
        {
          var linearArgumentTypes = new List<Type>();
          foreach (var inParam in actionDecl.InParams.Where(inParam => FindLinearKind(inParam) != LinearKind.ORDINARY))
          {
            if (inParam.TypedIdent.Type is CtorType ctorType)
            {
              var originalTypeCtorDecl = Monomorphizer.GetOriginalDecl(ctorType.Decl);
              if (originalTypeCtorDecl.Name == "One")
              {
                var typeInstantiation = civlTypeChecker.program.monomorphizer.GetTypeInstantiation(ctorType.Decl);
                var setType = TypeHelper.CtorType(civlTypeChecker.program.monomorphizer.InstantiateTypeCtorDecl("Set", typeInstantiation));
                linearArgumentTypes.Add(setType);
                continue;
              }
              else if (originalTypeCtorDecl.Name == "Set")
              {
                linearArgumentTypes.Add(ctorType);
                continue;
              }
            }
            Error(node, $"linear parameter must be of type One or Set");
          }
          var attr = QKeyValue.FindAttribute(node.Attributes, x => x.Key == "linear");
          var attrParams = attr == null ? new List<object>() : attr.Params;
          var identifierExprs = attrParams.OfType<IdentifierExpr>().ToList();
          if (identifierExprs.Count != attrParams.Count())
          {
            Error(node, $"each linear source must be a variable");
          }
          else if (identifierExprs.Count != linearArgumentTypes.Count)
          {
            Error(node, $"number of linear sources must match the number of linear parameters");
          }
          else
          {
            foreach (var (ie, type) in identifierExprs.Zip(linearArgumentTypes))
            {
              if (ie.Decl is LocalVariable || ie.Decl is Formal)
              {
                if (!ie.Decl.TypedIdent.Type.Equals(type))
                {
                  Error(ie, $"expected type {type}");
                }
              }
              else
              {
                Error(ie, $"expected local or formal variable");
              }
            }
          }
        }
      }
      return base.VisitCallCmd(node);
    }

    public override Cmd VisitParCallCmd(ParCallCmd node)
    {
      if (node.CallCmds.Any(callCmd => CivlPrimitives.IsPrimitive(callCmd.Proc)))
      {
        Error(node, "linear primitives may not be invoked in a parallel call");
        return node;
      }
      HashSet<Variable> parallelCallInputVars = new HashSet<Variable>();
      foreach (CallCmd callCmd in node.CallCmds.Where(callCmd => callCmd.Proc is not YieldInvariantDecl))
      {
        for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
        {
          if (FindLinearKind(callCmd.Proc.InParams[i]) == LinearKind.ORDINARY)
          {
            continue;
          }
          if (callCmd.Ins[i] is IdentifierExpr actual)
          {
            if (parallelCallInputVars.Contains(actual.Decl))
            {
              Error(node,
                $"linear variable can occur only once as an input parameter of a parallel call: {actual.Decl.Name}");
            }
            else
            {
              parallelCallInputVars.Add(actual.Decl);
            }
          }
        }
      }
      foreach (CallCmd callCmd in node.CallCmds.Where(callCmd => callCmd.Proc is YieldInvariantDecl))
      {
        for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
        {
          if (FindLinearKind(callCmd.Proc.InParams[i]) == LinearKind.ORDINARY)
          {
            continue;
          }
          if (callCmd.Ins[i] is IdentifierExpr actual && parallelCallInputVars.Contains(actual.Decl))
          {
            Error(node,
              $"linear variable cannot be an input parameter to both a yield invariant and a procedure in a parallel call: {actual.Decl.Name}");
          }
        }
      }
      return base.VisitParCallCmd(node);
    }

    public override Variable VisitVariable(Variable node)
    {
      var kind = FindLinearKind(node);
      if ((kind == LinearKind.LINEAR_IN || kind == LinearKind.LINEAR_OUT) && 
          (node is GlobalVariable || node is LocalVariable || (node is Formal formal && !formal.InComing)))
      {
        checkingContext.Error(node, "variable must be declared linear (as opposed to linear_in or linear_out)");
      }
      return node;
    }

    #endregion

    #region Useful public methods

    public ConcurrencyOptions Options => civlTypeChecker.Options;
    
    public static LinearKind FindLinearKind(Variable v)
    {
      if (QKeyValue.FindAttribute(v.Attributes, x => x.Key == CivlAttributes.LINEAR) != null)
      {
        return LinearKind.LINEAR;
      }
      if (QKeyValue.FindAttribute(v.Attributes, x => x.Key == CivlAttributes.LINEAR_IN) != null)
      {
        return LinearKind.LINEAR_IN;
      }
      if (QKeyValue.FindAttribute(v.Attributes, x => x.Key == CivlAttributes.LINEAR_OUT) != null)
      {
        return LinearKind.LINEAR_OUT;
      }
      return LinearKind.ORDINARY;
    }

    public int CheckLinearParameters(CallCmd callCmd, HashSet<Variable> availableLinearVarsAtCallCmd)
    {
      int errorCount = 0;
      foreach (var (ie, formal) in callCmd.Ins.Zip(callCmd.Proc.InParams))
      {
        if (FindLinearKind(formal) == LinearKind.ORDINARY)
        {
          continue;
        }
        if (ie is IdentifierExpr actual && !availableLinearVarsAtCallCmd.Contains(actual.Decl))
        {
          Error(actual, "argument must be available");
          errorCount++;
        }
      }
      return errorCount;
    }
    
    public IEnumerable<LinearDomain> LinearDomains => permissionTypeToLinearDomain.Values;

    public void TypeCheck()
    {
      (this.permissionTypeToLinearDomain, this.collectors) = LinearDomainCollector.Collect(this);
      this.availableLinearVars = new Dictionary<Absy, HashSet<Variable>>();
      this.VisitProgram(program);
      foreach (var absy in this.availableLinearVars.Keys)
      {
        availableLinearVars[absy].RemoveWhere(v => v is GlobalVariable);
      }
      if (checkingContext.ErrorCount == 0 && program.monomorphizer != null)
      {
        var impls = program.TopLevelDeclarations.OfType<Implementation>().ToList();
        impls.ForEach(impl =>
        {
          if (impl.Proc is not YieldProcedureDecl)
          {
            LinearRewriter.Rewrite(civlTypeChecker, impl);
          }
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

    public IEnumerable<Expr> PermissionExprs(LinearDomain domain, IEnumerable<Variable> scope)
    {
      return FilterVariables(domain, scope)
        .Select(v => ExprHelper.FunctionCall(collectors[v.TypedIdent.Type][domain.permissionType], Expr.Ident(v)));
    }

    public IEnumerable<Expr> DisjointnessExprForEachDomain(IEnumerable<Variable> scope)
    {
      return LinearDomains.Select(domain => DisjointnessExprForPermissions(domain, PermissionExprs(domain, scope)));
    }

    public Expr DisjointnessExprForPermissions(LinearDomain domain, IEnumerable<Expr> permissionsExprs)
    {
      Expr expr = Expr.True;
      if (permissionsExprs.Count() > 1)
      {
        int count = 0;
        List<Expr> subsetExprs = new List<Expr>();
        BoundVariable partition = civlTypeChecker.BoundVariable($"partition_{domain.permissionType}", domain.mapTypeInt);
        foreach (Expr e in permissionsExprs)
        {
          subsetExprs.Add(SubsetExpr(domain, e, partition, count));
          count++;
        }
        expr = ExprHelper.ExistsExpr(new List<Variable> {partition}, Expr.And(subsetExprs));
      }
      return expr;
    }

    public IEnumerable<Expr> MapWellFormedExpressions(IEnumerable<Variable> scope)
    {
      var monomorphizer = civlTypeChecker.program.monomorphizer;
      if (monomorphizer == null)
      {
        return Enumerable.Empty<Expr>();
      }
      return scope.Where(v =>
        {
          if (v.TypedIdent.Type is not CtorType ctorType)
          {
            return false;
          }
          var declName = Monomorphizer.GetOriginalDecl(ctorType.Decl).Name;
          if (declName is "Map")
          {
            return true;
          }
          return false;
        }).Select(v =>
        {
          var ctorType = (CtorType)v.TypedIdent.Type;
          var declName = Monomorphizer.GetOriginalDecl(ctorType.Decl).Name;
          var func = MapWellFormedFunction(monomorphizer, ctorType.Decl);
          return ExprHelper.FunctionCall(func, Expr.Ident(v));
        });
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

    private IEnumerable<Variable> FilterVariables(LinearDomain domain, IEnumerable<Variable> scope)
    {
      return scope.Where(v => 
        FindLinearKind(v) != LinearKind.ORDINARY &&
        collectors.ContainsKey(v.TypedIdent.Type) &&
        collectors[v.TypedIdent.Type].ContainsKey(domain.permissionType));
    }
    
    private Expr SubsetExpr(LinearDomain domain, Expr ie, Variable partition, int partitionCount)
    {
      Expr e = ExprHelper.FunctionCall(domain.mapConstInt, Expr.Literal(partitionCount));
      e = ExprHelper.FunctionCall(domain.mapEqInt, Expr.Ident(partition), e);
      e = ExprHelper.FunctionCall(domain.mapImp, ie, e);
      e = Expr.Eq(e, ExprHelper.FunctionCall(domain.mapConstBool, Expr.True));
      return e;
    }

    private Function MapWellFormedFunction(Monomorphizer monomorphizer, TypeCtorDecl typeCtorDecl)
    {
      var typeInstantiation = monomorphizer.GetTypeInstantiation(typeCtorDecl);
      var typeParamInstantiationMap = new Dictionary<string, Type>() { { "T", typeInstantiation[0] }, { "U", typeInstantiation[1] } };
      return monomorphizer.InstantiateFunction("Map_WellFormed", typeParamInstantiationMap);
    }

    public ActionDecl GetActionDeclFromCreateAsyncs(CallCmd callCmd)
    {
      var pendingAsyncType = civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
      return pendingAsyncTypeToActionDecl[pendingAsyncType];
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

  public class LinearStoreVisitor : ReadOnlyVisitor
  {
    private bool hasLinearStoreAccess = false;

    public static bool HasLinearStoreAccess(Expr expr)
    {
      var heapLookupVisitor = new LinearStoreVisitor();
      heapLookupVisitor.Visit(expr);
      return heapLookupVisitor.hasLinearStoreAccess;
    }

    public static bool HasLinearStoreAccess(AssignLhs assignLhs)
    {
      var heapLookupVisitor = new LinearStoreVisitor();
      heapLookupVisitor.Visit(assignLhs);
      return heapLookupVisitor.hasLinearStoreAccess;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      CheckType(node.Type);
      return base.VisitIdentifierExpr(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      CheckType(node.Type);
      return base.VisitNAryExpr(node);
    }

    private void CheckType(Type type)
    {
      if (type is not CtorType ctorType)
      {
        return;
      }
      var typeCtorDeclName = Monomorphizer.GetOriginalDecl(ctorType.Decl).Name;
      if (typeCtorDeclName == "Map")
      {
        hasLinearStoreAccess = true;
      }
    }
  }
}
