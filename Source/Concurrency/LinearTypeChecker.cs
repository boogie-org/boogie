using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  /// <summary>
  /// Type checker for linear type annotations.
  /// 
  /// The functionality is basically grouped into four parts (see #region's).
  /// 1) TypeCheck parses linear type attributes, sets up the data structures,
  ///    and performs a dataflow check on procedure implementations.
  /// 2) Useful public methods to generate expressions for permissions, their disjointness,
  ///    and their union.
  /// 3) Generation of linearity-invariant checker procedures for atomic actions.
  /// 4) Erasure procedure to remove all linearity attributes
  ///    (invoked after all other Civl transformations).
  /// </summary>
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

    public IEnumerable<LinearDomain> LinearDomains => domainNameToLinearDomain.Values;
    
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
      var domainName = domain.DomainName;
      return civlTypeChecker.Formal("linear_" + domainName + "_in", domainNameToLinearDomain[domainName].mapTypeBool, true);
    }

    public LocalVariable LinearDomainAvailableLocal(LinearDomain domain)
    {
      var domainName = domain.DomainName;
      return civlTypeChecker.LocalVariable("linear_" + domainName + "_available", domainNameToLinearDomain[domainName].mapTypeBool);
    }

    public void TypeCheck()
    {
      (this.domainNameToLinearDomain, this.linearTypeToLinearDomain) = LinearDomainCollector.Collect(program, civlTypeChecker);
      this.VisitProgram(program);
      foreach (Absy absy in this.availableLinearVars.Keys)
      {
        availableLinearVars[absy].RemoveWhere(v => v is GlobalVariable);
      }
    }
    
    #region Visitor Implementation

    private IEnumerable<Variable> LinearGlobalVariables =>
      program.GlobalVariables.Where(v => LinearDomainCollector.FindLinearKind(v) != LinearKind.ORDINARY);

    public override Implementation VisitImplementation(Implementation node)
    {
      var linearGlobalVariables = LinearGlobalVariables;
      
      if (civlTypeChecker.procToAtomicAction.ContainsKey(node.Proc) ||
          civlTypeChecker.procToIntroductionAction.ContainsKey(node.Proc) ||
          civlTypeChecker.procToIsAbstraction.ContainsKey(node.Proc) ||
          civlTypeChecker.procToIsInvariant.ContainsKey(node.Proc) ||
          civlTypeChecker.procToLemmaProc.ContainsKey(node.Proc))
      {
        return node;
      }

      node.PruneUnreachableBlocks(civlTypeChecker.Options);
      node.ComputePredecessorsForBlocks();
      GraphUtil.Graph<Block> graph = Program.GraphFromImpl(node);
      graph.ComputeLoops();

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

    #region Linearity Invariant Checker

    public void AddCheckers(List<Declaration> decls)
    {
      foreach (var action in Enumerable.Concat<Action>(civlTypeChecker.procToAtomicAction.Values,
        civlTypeChecker.procToIntroductionAction.Values))
      {
        AddChecker(action, decls);
      }
    }

    private static LinearKind[] InKinds = {LinearKind.LINEAR, LinearKind.LINEAR_IN};
    private static LinearKind[] OutKinds = {LinearKind.LINEAR, LinearKind.LINEAR_OUT};

    private class LinearityCheck
    {
      public string domainName;
      public Expr assume;
      public Expr assert;
      public string message;
      public string checkName;

      public LinearityCheck(string domainName, Expr assume, Expr assert, string message, string checkName)
      {
        this.domainName = domainName;
        this.assume = assume;
        this.assert = assert;
        this.message = message;
        this.checkName = checkName;
      }
    }

    private void AddChecker(Action action, List<Declaration> decls)
    {
      // Note: The implementation should be used as the variables in the
      //       gate are bound to implementation and not to the procedure.
      Implementation impl = action.impl;
      List<Variable> inputs = impl.InParams;
      List<Variable> outputs = impl.OutParams;

      List<Variable> locals = new List<Variable>(2);
      var paLocal1 = civlTypeChecker.LocalVariable("pa1", civlTypeChecker.pendingAsyncType);
      var paLocal2 = civlTypeChecker.LocalVariable("pa2", civlTypeChecker.pendingAsyncType);
      var pa1 = Expr.Ident(paLocal1);
      var pa2 = Expr.Ident(paLocal2);
      
      if (civlTypeChecker.pendingAsyncType != null)
      {
        locals.Add(paLocal1);
        locals.Add(paLocal2);
      }

      List<Requires> requires = action.gate.Select(a => new Requires(false, a.Expr)).ToList();
      List<LinearityCheck> linearityChecks = new List<LinearityCheck>();

      foreach (var domain in domainNameToLinearDomain.Values)
      {
        // Linear in vars
        var inVars = inputs.Union(action.modifiedGlobalVars)
          .Where(x => InKinds.Contains(LinearDomainCollector.FindLinearKind(x)))
          .Where(x => FindDomain(x) == domain)
          .Select(Expr.Ident)
          .ToList();
        
        // Linear out vars
        var outVars = inputs.Union(outputs).Union(action.modifiedGlobalVars)
          .Where(x => OutKinds.Contains(LinearDomainCollector.FindLinearKind(x)))
          .Where(x => FindDomain(x) == domain)
          .Select(Expr.Ident)
          .ToList();

        // First kind
        // Permissions in linear output variables are a subset of permissions in linear input variables.
        if (outVars.Count > 0)
        {
          linearityChecks.Add(new LinearityCheck(
            domain.DomainName,
            null,
            OutPermsSubsetInPerms(domain, inVars, outVars),
            $"Potential linearity violation in outputs for domain {domain.DomainName}.",
            "variables"));
        }

        if (action is AtomicAction atomicAction && atomicAction.HasPendingAsyncs)
        {
          var PAs = Expr.Ident(atomicAction.impl.OutParams.Last());
          
          foreach (var pendingAsync in atomicAction.pendingAsyncs)
          {
            var pendingAsyncLinearParams = PendingAsyncLinearParams(domain, pendingAsync, pa1);

            if (pendingAsyncLinearParams.Count == 0)
            {
              continue;
            }

            // Second kind
            // Permissions in linear output variables + linear inputs of a single pending async
            // are a subset of permissions in linear input variables.
            var exactlyOnePA = Expr.And(
              ExprHelper.IsConstructor(pa1, pendingAsync.pendingAsyncCtor.Name),
              Expr.Eq(Expr.Select(PAs, pa1), Expr.Literal(1)));
            var outSubsetInExpr = OutPermsSubsetInPerms(domain, inVars, pendingAsyncLinearParams.Union(outVars));
            linearityChecks.Add(new LinearityCheck(
              domain.DomainName,
              exactlyOnePA,
              outSubsetInExpr,
              $"Potential linearity violation in outputs and pending async of {pendingAsync.proc.Name} for domain {domain.DomainName}.",
              $"single_{pendingAsync.proc.Name}"));

            // Third kind
            // If there are two identical pending asyncs, then their input permissions mut be empty.
            var twoIdenticalPAs = Expr.And(
              ExprHelper.IsConstructor(pa1, pendingAsync.pendingAsyncCtor.Name),
              Expr.Ge(Expr.Select(PAs, pa1), Expr.Literal(2)));
            var emptyPerms = OutPermsSubsetInPerms(domain, Enumerable.Empty<Expr>(), pendingAsyncLinearParams);
            linearityChecks.Add(new LinearityCheck(
              domain.DomainName,
              twoIdenticalPAs,
              emptyPerms,
              $"Potential linearity violation in identical pending asyncs of {pendingAsync.proc.Name} for domain {domain.DomainName}.",
              $"identical_{pendingAsync.proc.Name}"));
          }

          var pendingAsyncs = atomicAction.pendingAsyncs.ToList();
          for (int i = 0; i < pendingAsyncs.Count; i++)
          {
            var pendingAsync1 = pendingAsyncs[i];
            for (int j = i; j < pendingAsyncs.Count; j++)
            {
              var pendingAsync2 = pendingAsyncs[j];

              var pendingAsyncLinearParams1 = PendingAsyncLinearParams(domain, pendingAsync1, pa1);
              var pendingAsyncLinearParams2 = PendingAsyncLinearParams(domain, pendingAsync2, pa2);
              
              if (pendingAsyncLinearParams1.Count == 0 || pendingAsyncLinearParams2.Count == 0)
              {
                continue;
              }

              // Fourth kind
              // Input permissions of two non-identical pending asyncs (possibly of the same action)
              // are a subset of permissions in linear input variables.
              var membership = Expr.And(
                Expr.Neq(pa1, pa2),
                Expr.And(
                  ExprHelper.IsConstructor(pa1, pendingAsync1.pendingAsyncCtor.Name),
                  ExprHelper.IsConstructor(pa2, pendingAsync2.pendingAsyncCtor.Name)));

              var existing = Expr.And(
                Expr.Ge(Expr.Select(PAs, pa1), Expr.Literal(1)),
                Expr.Ge(Expr.Select(PAs, pa2), Expr.Literal(1)));

              var noDuplication = OutPermsSubsetInPerms(domain, inVars, pendingAsyncLinearParams1.Union(pendingAsyncLinearParams2));

              linearityChecks.Add(new LinearityCheck(
                domain.DomainName,
                Expr.And(membership, existing),
                noDuplication,
                $"Potential lnearity violation in pending asyncs of {pendingAsync1.proc.Name} and {pendingAsync2.proc.Name} for domain {domain.DomainName}.",
                $"distinct_{pendingAsync1.proc.Name}_{pendingAsync2.proc.Name}"));
            }
          }
        }
      }

      if (linearityChecks.Count == 0)
      {
        return;
      }

      // Create checker blocks
      List<Block> checkerBlocks = new List<Block>(linearityChecks.Count);
      foreach (var lc in linearityChecks)
      {
        List<Cmd> cmds = new List<Cmd>(2);
        if (lc.assume != null)
        {
          cmds.Add(CmdHelper.AssumeCmd(lc.assume));
        }
        cmds.Add(CmdHelper.AssertCmd(action.proc.tok, lc.assert, lc.message));
        var block = BlockHelper.Block($"{lc.domainName}_{lc.checkName}", cmds);
        CivlUtil.ResolveAndTypecheck(Options, block, ResolutionContext.State.Two);
        checkerBlocks.Add(block);
      }
      
      // Create init blocks
      List<Block> blocks = new List<Block>(linearityChecks.Count + 1);
      blocks.Add(
        BlockHelper.Block(
          "init",
          new List<Cmd> { CmdHelper.CallCmd(action.proc, inputs, outputs) },
          checkerBlocks));
      blocks.AddRange(checkerBlocks);

      // Create the whole check procedure
      string checkerName = civlTypeChecker.AddNamePrefix($"LinearityChecker_{action.proc.Name}");
      Procedure linCheckerProc = DeclHelper.Procedure(checkerName,
        inputs, outputs, requires, action.proc.Modifies, new List<Ensures>());
      Implementation linCheckImpl = DeclHelper.Implementation(linCheckerProc,
        inputs, outputs, locals, blocks);
      decls.Add(linCheckImpl);
      decls.Add(linCheckerProc);
    }

    private List<Expr> PendingAsyncLinearParams(LinearDomain domain, AtomicAction pendingAsync, IdentifierExpr pa)
    {
      var pendingAsyncLinearParams = new List<Expr>();

      for (int i = 0; i < pendingAsync.proc.InParams.Count; i++)
      {
        var inParam = pendingAsync.proc.InParams[i];
        if (InKinds.Contains(LinearDomainCollector.FindLinearKind(inParam)) && FindDomain(inParam) == domain)
        {
          var pendingAsyncParam = ExprHelper.FieldAccess(pa, pendingAsync.pendingAsyncCtor.InParams[i].Name);
          pendingAsyncLinearParams.Add(pendingAsyncParam);
        }
      }

      // These expressions must be typechecked since the types are needed later in PermissionMultiset.
      CivlUtil.ResolveAndTypecheck(Options, pendingAsyncLinearParams);
      
      return pendingAsyncLinearParams;
    }

    private Expr OutPermsSubsetInPerms(LinearDomain domain, IEnumerable<Expr> ins, IEnumerable<Expr> outs)
    {
      Expr inMultiset = ExprHelper.Old(PermissionMultiset(domain, ins));
      Expr outMultiset = PermissionMultiset(domain, outs);
      Expr subsetExpr = ExprHelper.FunctionCall(domain.mapLe, outMultiset, inMultiset);
      return Expr.Eq(subsetExpr, ExprHelper.FunctionCall(domain.mapConstBool, Expr.True));
    }

    private Expr PermissionMultiset(LinearDomain domain, IEnumerable<Expr> exprs)
    {
      var terms = exprs.Select(x =>
        ExprHelper.FunctionCall(domain.mapIteInt,
          ExprHelper.FunctionCall(domain.collectors[x.Type], x),
          domain.MapConstInt(1),
          domain.MapConstInt(0))).ToList<Expr>();

      if (terms.Count == 0)
      {
        return domain.MapConstInt(0);
      }

      return terms.Aggregate((x, y) => ExprHelper.FunctionCall(domain.mapAdd, x, y));
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
