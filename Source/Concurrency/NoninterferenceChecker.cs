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
      DeclWithFormals decl,
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

      foreach (Variable local in declLocalVariables.Union(decl.InParams).Union(decl.OutParams))
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
      List<YieldInfo> yieldInfos = null;
      string noninterferenceCheckerName = null;
      if (decl is Implementation impl)
      {
        noninterferenceCheckerName = $"impl_{absyMap.Original(impl).Name}_{layerNum}";
        yieldInfos = CollectYields(civlTypeChecker, absyMap, layerNum, impl).Select(kv =>
          new YieldInfo(linearPermissionInstrumentation.DisjointnessAssumeCmds(kv.Key, false), kv.Value)).ToList();
      }
      else if (decl is Procedure proc)
      {
        yieldInfos = new List<YieldInfo>();
        if (civlTypeChecker.procToYieldInvariant.ContainsKey(proc))
        {
          noninterferenceCheckerName = $"yield_{proc.Name}";
          if (proc.Requires.Count > 0)
          {
            var disjointnessCmds = linearPermissionInstrumentation.ProcDisjointnessAssumeCmds(proc, true);
            var yieldPredicates = proc.Requires.Select(requires =>
              requires.Free
                ? (PredicateCmd) new AssumeCmd(requires.tok, requires.Condition)
                : (PredicateCmd) new AssertCmd(requires.tok, requires.Condition)).ToList();
            yieldInfos.Add(new YieldInfo(disjointnessCmds, yieldPredicates));
          }
        }
        else
        {
          noninterferenceCheckerName = $"proc_{absyMap.Original(proc).Name}_{layerNum}";
          if (proc.Requires.Count > 0)
          {
            var entryDisjointnessCmds =
              linearPermissionInstrumentation.ProcDisjointnessAssumeCmds(proc, true);
            var entryYieldPredicates = proc.Requires.Select(requires =>
              requires.Free
                ? (PredicateCmd) new AssumeCmd(requires.tok, requires.Condition)
                : (PredicateCmd) new AssertCmd(requires.tok, requires.Condition)).ToList();
            yieldInfos.Add(new YieldInfo(entryDisjointnessCmds, entryYieldPredicates));
          }

          if (proc.Ensures.Count > 0)
          {
            var exitDisjointnessCmds =
              linearPermissionInstrumentation.ProcDisjointnessAssumeCmds(proc, false);
            var exitYieldPredicates = proc.Ensures.Select(ensures =>
              ensures.Free
                ? (PredicateCmd) new AssumeCmd(ensures.tok, ensures.Condition)
                : (PredicateCmd) new AssertCmd(ensures.tok, ensures.Condition)).ToList();
            yieldInfos.Add(new YieldInfo(exitDisjointnessCmds, exitYieldPredicates));
          }
        }
      }
      else
      {
        Debug.Assert(false);
      }

      var filteredYieldInfos = yieldInfos.Where(info =>
        info.invariantCmds.Any(predCmd => new GlobalAccessChecker().AccessesGlobal(predCmd.Expr)));
      if (filteredYieldInfos.Count() == 0)
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

    private static Dictionary<Absy, List<PredicateCmd>> CollectYields(CivlTypeChecker civlTypeChecker,
      AbsyMap absyMap, int layerNum, Implementation impl)
    {
      var allYieldPredicates = new Dictionary<Absy, List<PredicateCmd>>();
      List<PredicateCmd> yieldPredicates = new List<PredicateCmd>();
      foreach (Block b in impl.Blocks)
      {
        Absy absy = null;
        var originalBlock = absyMap.Original(b);
        if (civlTypeChecker.yieldingLoops.ContainsKey(originalBlock) &&
            civlTypeChecker.yieldingLoops[originalBlock].layers.Contains(layerNum))
        {
          absy = b;
        }

        foreach (Cmd cmd in b.Cmds)
        {
          if (absy != null)
          {
            if (cmd is PredicateCmd)
            {
              yieldPredicates.Add(cmd as PredicateCmd);
            }
            else
            {
              allYieldPredicates[absy] = yieldPredicates;
              yieldPredicates = new List<PredicateCmd>();
              absy = null;
            }
          }

          if (cmd is YieldCmd ycmd)
          {
            absy = ycmd;
          }
        }

        if (absy != null)
        {
          allYieldPredicates[absy] = yieldPredicates;
          yieldPredicates = new List<PredicateCmd>();
        }
      }

      return allYieldPredicates;
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