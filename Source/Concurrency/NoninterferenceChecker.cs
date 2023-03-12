using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
  public static class NoninterferenceChecker
  {
    public static string PermissionCollectorFormalName(LinearDomain domain)
    {
      return "linear_" + domain.DomainName + "_in";
    }
    
    public static string PermissionCollectorLocalName(LinearDomain domain)
    {
      return "linear_" + domain.DomainName + "_available";
    }
    
    public static List<Declaration> CreateNoninterferenceCheckers(
      CivlTypeChecker civlTypeChecker,
      int layerNum,
      AbsyMap absyMap,
      YieldInvariantDecl yieldInvariantDecl,
      List<Variable> declLocalVariables)
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      var domainToHoleVar = new Dictionary<LinearDomain, Variable>();
      Dictionary<Variable, Variable> localVarMap = new Dictionary<Variable, Variable>();
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      List<Variable> locals = new List<Variable>();
      List<Variable> inputs = new List<Variable>();
      foreach (var domain in linearTypeChecker.LinearDomains)
      {
        var inParam = civlTypeChecker.Formal(PermissionCollectorFormalName(domain), domain.mapTypeBool, true);
        inputs.Add(inParam);
        domainToHoleVar[domain] = inParam;
      }

      foreach (Variable local in declLocalVariables.Union(yieldInvariantDecl.InParams).Union(yieldInvariantDecl.OutParams))
      {
        var copy = CopyLocal(local);
        locals.Add(copy);
        localVarMap[local] = copy;
        map[local] = Expr.Ident(copy);
      }

      Dictionary<Variable, Expr> oldLocalMap = new Dictionary<Variable, Expr>();
      Dictionary<Variable, Expr> assumeMap = new Dictionary<Variable, Expr>(map);
      foreach (Variable g in civlTypeChecker.GlobalVariables)
      {
        var copy = OldGlobalLocal(civlTypeChecker, g);
        locals.Add(copy);
        oldLocalMap[g] = Expr.Ident(copy);
        Formal f = SnapshotGlobalFormal(civlTypeChecker, g);
        inputs.Add(f);
        assumeMap[g] = Expr.Ident(f);
      }

      var linearPermissionInstrumentation = new LinearPermissionInstrumentation(civlTypeChecker,
        layerNum, absyMap, domainToHoleVar, localVarMap);
      var yieldInfos = new List<YieldInfo>();
      var noninterferenceCheckerName = $"yield_{yieldInvariantDecl.Name}";
      if (yieldInvariantDecl.Requires.Count > 0)
      {
        var disjointnessCmds = linearPermissionInstrumentation.ProcDisjointnessAndWellFormedAssumeCmds(yieldInvariantDecl, true);
        var yieldPredicates = yieldInvariantDecl.Requires.Select(requires =>
          requires.Free
            ? (PredicateCmd)new AssumeCmd(requires.tok, requires.Condition)
            : (PredicateCmd)new AssertCmd(requires.tok, requires.Condition)).ToList();
        yieldInfos.Add(new YieldInfo(disjointnessCmds, yieldPredicates));
      }

      var filteredYieldInfos = yieldInfos.Where(info =>
        info.invariantCmds.Any(predCmd => new GlobalAccessChecker().AccessesGlobal(predCmd.Expr)));
      if (!filteredYieldInfos.Any())
      {
        return new List<Declaration>();
      }

      Substitution assumeSubst = Substituter.SubstitutionFromDictionary(assumeMap);
      Substitution oldSubst = Substituter.SubstitutionFromDictionary(oldLocalMap);
      Substitution subst = Substituter.SubstitutionFromDictionary(map);
      List<Block> noninterferenceCheckerBlocks = new List<Block>();
      List<Block> labelTargets = new List<Block>();
      Block noninterferenceCheckerBlock = BlockHelper.Block("exit", new List<Cmd>());
      labelTargets.Add(noninterferenceCheckerBlock);
      noninterferenceCheckerBlocks.Add(noninterferenceCheckerBlock);
      int yieldCount = 0;
      foreach (var kv in filteredYieldInfos)
      {
        var newCmds = new List<Cmd>(kv.disjointnessCmds);
        foreach (var predCmd in kv.invariantCmds)
        {
          var newExpr = Substituter.ApplyReplacingOldExprs(assumeSubst, oldSubst, predCmd.Expr);
          newCmds.Add(new AssumeCmd(predCmd.tok, newExpr));
        }

        foreach (var predCmd in kv.invariantCmds)
        {
          if (predCmd is AssertCmd)
          {
            var newExpr = Substituter.ApplyReplacingOldExprs(subst, oldSubst, predCmd.Expr);
            AssertCmd assertCmd = new AssertCmd(predCmd.tok, newExpr, predCmd.Attributes);
            assertCmd.Description = new FailureOnlyDescription("Non-interference check failed");
            newCmds.Add(assertCmd);
          }
        }

        newCmds.Add(CmdHelper.AssumeCmd(Expr.False));
        noninterferenceCheckerBlock = BlockHelper.Block("L" + yieldCount++, newCmds);
        labelTargets.Add(noninterferenceCheckerBlock);
        noninterferenceCheckerBlocks.Add(noninterferenceCheckerBlock);
      }

      noninterferenceCheckerBlocks.Insert(0, BlockHelper.Block("enter", new List<Cmd>(), labelTargets));

      // Create the yield checker procedure
      noninterferenceCheckerName = civlTypeChecker.AddNamePrefix($"NoninterferenceChecker_{noninterferenceCheckerName}");
      var noninterferenceCheckerProc = DeclHelper.Procedure(noninterferenceCheckerName,
        inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
      CivlUtil.AddInlineAttribute(noninterferenceCheckerProc);

      // Create the yield checker implementation
      var noninterferenceCheckerImpl = DeclHelper.Implementation(noninterferenceCheckerProc,
        inputs, new List<Variable>(), locals, noninterferenceCheckerBlocks);
      return new List<Declaration> {noninterferenceCheckerProc, noninterferenceCheckerImpl};
    }

    private static LocalVariable CopyLocal(Variable v)
    {
      var copy = VarHelper.LocalVariable(v.Name, v.TypedIdent.Type);
      if (v.Attributes != null)
      {
        copy.Attributes = (QKeyValue)v.Attributes.Clone();
      }
      return copy;
    }

    private static Formal SnapshotGlobalFormal(CivlTypeChecker civlTypeChecker, Variable v)
    {
      return civlTypeChecker.Formal($"snapshot_{v.Name}", v.TypedIdent.Type, true);
    }

    private static LocalVariable OldGlobalLocal(CivlTypeChecker civlTypeChecker, Variable v)
    {
      return civlTypeChecker.LocalVariable($"old_{v.Name}", v.TypedIdent.Type);
    }
  }

  class YieldInfo
  {
    public List<Cmd> disjointnessCmds;
    public List<PredicateCmd> invariantCmds;

    public YieldInfo(List<Cmd> disjointnessCmds, List<PredicateCmd> invariantCmds)
    {
      this.disjointnessCmds = disjointnessCmds;
      this.invariantCmds = invariantCmds;
    }
  }

  class GlobalAccessChecker : ReadOnlyVisitor
  {
    private bool accessesGlobal;
    private int insideOldExpr;

    public GlobalAccessChecker()
    {
      this.accessesGlobal = false;
      this.insideOldExpr = 0;
    }

    public bool AccessesGlobal(Expr expr)
    {
      Visit(expr);
      return accessesGlobal;
    }

    public override Expr VisitOldExpr(OldExpr node)
    {
      insideOldExpr++;
      base.VisitOldExpr(node);
      insideOldExpr--;
      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (node.Decl is GlobalVariable && insideOldExpr == 0)
      {
        accessesGlobal = true;
      }

      return node;
    }
  }
}