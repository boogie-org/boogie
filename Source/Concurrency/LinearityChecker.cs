using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie;
class LinearityChecker 
{
    private CivlTypeChecker civlTypeChecker;
    private LinearTypeChecker linearTypeChecker => civlTypeChecker.linearTypeChecker;

    private LinearityChecker(CivlTypeChecker civlTypeChecker)
    {
        this.civlTypeChecker = civlTypeChecker;
    }

    public static void AddCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      var linearityChecker = new LinearityChecker(civlTypeChecker);
      foreach (var action in Enumerable.Concat<Action>(civlTypeChecker.procToAtomicAction.Values,
        civlTypeChecker.procToIntroductionAction.Values))
      {
        linearityChecker.AddChecker(action, decls);
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

      foreach (var domain in linearTypeChecker.NameLinearDomains)
      {
        // Linear in vars
        var inVars = linearTypeChecker.FilterVariables(domain,inputs.Union(action.modifiedGlobalVars))
          .Where(x => InKinds.Contains(LinearDomainCollector.FindLinearKind(x))).Select(Expr.Ident).ToList();
        
        // Linear out vars
        var outVars = linearTypeChecker.FilterVariables(domain, inputs.Union(outputs).Union(action.modifiedGlobalVars))
          .Where(x => OutKinds.Contains(LinearDomainCollector.FindLinearKind(x))).Select(Expr.Ident).ToList();

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
        CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, block, ResolutionContext.State.Two);
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
      var pendingAsyncLinearParams = linearTypeChecker.FilterVariables(domain, pendingAsync.proc.InParams)
        .Where(v => InKinds.Contains(LinearDomainCollector.FindLinearKind(v)))
        .Select(v => ExprHelper.FieldAccess(pa, v.Name)).ToList<Expr>();
      // These expressions must be typechecked since the types are needed later in PermissionMultiset.
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, pendingAsyncLinearParams);
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
}