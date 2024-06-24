using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie;

public class LinearityCheck
    {
      public LinearDomain domain;
      public Expr assume;
      public Expr assert;
      public string message;
      public string checkName;

      public LinearityCheck(LinearDomain domain, Expr assume, Expr assert, string message, string checkName)
      {
        this.domain = domain;
        this.assume = assume;
        this.assert = assert;
        this.message = message;
        this.checkName = checkName;
      }
}

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
      foreach (var action in civlTypeChecker.MoverActions)
      {
        linearityChecker.AddChecker(action, decls);
      }
    }

    private IdentifierExpr PAs(Action action, int pendingAsyncIndex)
    {
      return Expr.Ident(action.Impl.OutParams[action.PendingAsyncStartIndex + pendingAsyncIndex]);
    }
    
    private void AddChecker(Action action, List<Declaration> decls)
    {
      if (action is not Action { HasPendingAsyncs: true } atomicAction)
      {
        return;
      }
      var pendingAsyncs = new List<ActionDecl>(atomicAction.PendingAsyncs);
      // Note: The implementation should be used as the variables in the
      //       gate are bound to implementation and not to the procedure.
      Implementation impl = action.Impl;
      List<Variable> inputs = impl.InParams;
      List<Variable> outputs = impl.OutParams;

      var locals = new List<Variable>();
      var ctorTypeToFirstPA = new Dictionary<CtorType, IdentifierExpr>();
      var ctorTypeToSecondPA = new Dictionary<CtorType, IdentifierExpr>();
      pendingAsyncs.ForEach(y =>
      {
        var paLocal1 = civlTypeChecker.LocalVariable($"pa1_{y.PendingAsyncType.Decl.Name}", y.PendingAsyncType);
        var paLocal2 = civlTypeChecker.LocalVariable($"pa2_{y.PendingAsyncType.Decl.Name}", y.PendingAsyncType);
        locals.Add(paLocal1);
        locals.Add(paLocal2);
        ctorTypeToFirstPA[y.PendingAsyncType] = Expr.Ident(paLocal1);
        ctorTypeToSecondPA[y.PendingAsyncType] = Expr.Ident(paLocal2);
      });
      
      // Linear in vars
      var inVars = inputs.Union(action.ModifiedGlobalVars)
          .Where(x => LinearTypeChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(x)))
          .Select(Expr.Ident).ToList();
      // Linear out vars
      var outVars = inputs.Union(outputs).Union(action.ModifiedGlobalVars)
          .Where(x => LinearTypeChecker.OutKinds.Contains(LinearTypeChecker.FindLinearKind(x)))
          .Select(Expr.Ident).ToList();

      var inputDisjointnessExprs = linearTypeChecker.DisjointnessExprForEachDomain(
        inputs.Union(action.ModifiedGlobalVars)
        .Where(x => LinearTypeChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(x))));
      List<Requires> requires = action.Gate.Select(a => new Requires(false, a.Expr))
          .Concat(inputDisjointnessExprs.Select(expr => new Requires(false, expr)))
          .ToList();

      List<LinearityCheck> linearityChecks = new List<LinearityCheck>();
      foreach (var domain in linearTypeChecker.LinearDomains)
      {
        for (int i = 0; i < pendingAsyncs.Count; i++)
        {
          var pendingAsync = pendingAsyncs[i];
          var pa1 = ctorTypeToFirstPA[pendingAsync.PendingAsyncType];
          var pa2 = ctorTypeToSecondPA[pendingAsync.PendingAsyncType];
          var pendingAsyncLinearParams = PendingAsyncLinearParams(pendingAsync, pa1);

          if (pendingAsyncLinearParams.Count == 0)
          {
            continue;
          }

          // First kind
          // Input permission of a pending async is a subset of permissions in input variables.
          var existingExpr = Expr.And(
            ExprHelper.IsConstructor(pa1, pendingAsync.PendingAsyncCtor.Name),
            Expr.Ge(Expr.Select(PAs(atomicAction, i), pa1), Expr.Literal(1)));
          var outSubsetInExpr = OutPermsSubsetInPerms(domain, inVars, pendingAsyncLinearParams);
          linearityChecks.Add(new LinearityCheck(
            domain,
            existingExpr,
            outSubsetInExpr,
            $"Out-of-thin-air permissions of type {domain.permissionType} in pending async of {pendingAsync.Name}",
            $"out_of_thin_air_{pendingAsync.Name}"));

          // Second kind
          // Input permission of a pending async is disjoint from permissions in output variables.
          var noDuplicationExpr = DisjointPerms(domain, outVars, pendingAsyncLinearParams);
          linearityChecks.Add(new LinearityCheck(
            domain,
            existingExpr,
            noDuplicationExpr,
            $"Duplication of permissions of type {domain.permissionType} in calling context (globals, linear outputs, or linear/linear_out inputs) and pending async of {pendingAsync.Name}",
            $"duplication_{pendingAsync.Name}"));
        }
        
        for (int i = 0; i < pendingAsyncs.Count; i++)
        {
          var pendingAsync1 = pendingAsyncs[i];
          var pa1 = ctorTypeToFirstPA[pendingAsync1.PendingAsyncType];
          for (int j = i; j < pendingAsyncs.Count; j++)
          {
            var pendingAsync2 = pendingAsyncs[j];
            var pa2 = ctorTypeToSecondPA[pendingAsync2.PendingAsyncType];
            var pendingAsyncLinearParams1 = PendingAsyncLinearParams(pendingAsync1, pa1);
            var pendingAsyncLinearParams2 = PendingAsyncLinearParams(pendingAsync2, pa2);
            
            if (pendingAsyncLinearParams1.Count == 0 || pendingAsyncLinearParams2.Count == 0)
            {
              continue;
            }

            // Third kind
            // Input permissions of two pending asyncs (possibly of the same action) are disjoint.
            var membershipExpr = Expr.And(
              i == j ? Expr.Neq(pa1, pa2) : Expr.True,
              Expr.And(
                ExprHelper.IsConstructor(pa1, pendingAsync1.PendingAsyncCtor.Name),
                ExprHelper.IsConstructor(pa2, pendingAsync2.PendingAsyncCtor.Name)));

            var existingExpr = Expr.And(
              Expr.Ge(Expr.Select(PAs(atomicAction, i), pa1), Expr.Literal(1)),
              Expr.Ge(Expr.Select(PAs(atomicAction, j), pa2), Expr.Literal(1)));

            var noDuplicationExpr = DisjointPerms(domain, pendingAsyncLinearParams1, pendingAsyncLinearParams2);

            linearityChecks.Add(new LinearityCheck(
              domain,
              Expr.And(membershipExpr, existingExpr),
              noDuplicationExpr,
              $"Duplication of permissions of type {domain.permissionType} in pending asyncs of {pendingAsync1.Name} and {pendingAsync2.Name}",
              $"duplication_{pendingAsync1.Name}_{pendingAsync2.Name}"));
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
        cmds.Add(CmdHelper.AssertCmd(action.tok, lc.assert, lc.message));
        var block = BlockHelper.Block($"{lc.domain.permissionType}_{lc.checkName}", cmds);
        CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, block, ResolutionContext.State.Two);
        checkerBlocks.Add(block);
      }
      
      // Create init blocks
      List<Block> blocks = new List<Block>(linearityChecks.Count + 1);
      blocks.Add(
        BlockHelper.Block(
          "init",
          new List<Cmd>() { CmdHelper.CallCmd(action.Impl.Proc, inputs, outputs) },
          checkerBlocks));
      blocks.AddRange(checkerBlocks);

      // Create the whole check procedure
      string checkerName = civlTypeChecker.AddNamePrefix($"LinearityChecker_{action.Name}");
      Procedure linCheckerProc = DeclHelper.Procedure(checkerName,
        inputs, outputs, requires, action.Impl.Proc.Modifies, new List<Ensures>());
      Implementation linCheckImpl = DeclHelper.Implementation(linCheckerProc,
        inputs, outputs, locals, blocks);
      decls.Add(linCheckImpl);
      decls.Add(linCheckerProc);
    }

    private List<Expr> PendingAsyncLinearParams(ActionDecl pendingAsync, IdentifierExpr pa)
    {
      var pendingAsyncLinearParams = pendingAsync.InParams
        .Where(v => LinearTypeChecker.InKinds.Contains(LinearTypeChecker.FindLinearKind(v)))
        .Select(v => ExprHelper.FieldAccess(pa, v.Name)).ToList<Expr>();
      // These expressions must be typechecked since the types are needed later in PermissionMultiset.
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, pendingAsyncLinearParams);
      return pendingAsyncLinearParams;
    }

    private Expr OutPermsSubsetInPerms(LinearDomain domain, IEnumerable<Expr> ins, IEnumerable<Expr> outs)
    {
      var inPermissionSet = ExprHelper.Old(linearTypeChecker.UnionExprForPermissions(domain, linearTypeChecker.PermissionExprs(domain, ins)));
      var outPermissionSet = linearTypeChecker.UnionExprForPermissions(domain, linearTypeChecker.PermissionExprs(domain, outs));
      return linearTypeChecker.SubsetExprForPermissions(domain, outPermissionSet, inPermissionSet);
    }

    private Expr DisjointPerms(LinearDomain domain, IEnumerable<Expr> set1, IEnumerable<Expr> set2) {
      var expr1 = linearTypeChecker.UnionExprForPermissions(domain, linearTypeChecker.PermissionExprs(domain, set1));
      var expr2 = linearTypeChecker.UnionExprForPermissions(domain, linearTypeChecker.PermissionExprs(domain, set2));
      return Expr.Eq(
        ExprHelper.FunctionCall(domain.mapAnd, expr1, expr2),
        ExprHelper.FunctionCall(domain.mapConstBool, Expr.False));
    }
}