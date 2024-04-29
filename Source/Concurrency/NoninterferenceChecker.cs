using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public static class NoninterferenceChecker
  {
    public static string PermissionCollectorFormalName(LinearDomain domain)
    {
      return $"linear_{domain.permissionType}_in";
    }
    
    public static string PermissionCollectorLocalName(LinearDomain domain)
    {
      return $"linear_{domain.permissionType}_available";
    }

    public static List<Declaration> CreateNoninterferenceCheckerDecls(
      CivlTypeChecker civlTypeChecker,
      int layerNum,
      AbsyMap absyMap,
      YieldInvariantDecl yieldInvariantDecl,
      List<Variable> declLocalVariables)
    {
      if (!yieldInvariantDecl.Requires.Any())
      {
        return new List<Declaration>();
      }

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

      foreach (Variable local in declLocalVariables.Union(yieldInvariantDecl.InParams)
                 .Union(yieldInvariantDecl.OutParams))
      {
        var copy = CopyLocal(local);
        locals.Add(copy);
        localVarMap[local] = copy;
        map[local] = Expr.Ident(copy);
      }

      Dictionary<Variable, Expr> assumeMap = new Dictionary<Variable, Expr>(map);
      foreach (Variable g in civlTypeChecker.GlobalVariables)
      {
        Formal f = SnapshotGlobalFormal(civlTypeChecker, g);
        inputs.Add(f);
        assumeMap[g] = Expr.Ident(f);
      }

      var linearPermissionInstrumentation = new LinearPermissionInstrumentation(civlTypeChecker,
        layerNum, absyMap, domainToHoleVar, localVarMap);
      var noninterferenceCheckerName = $"yield_{yieldInvariantDecl.Name}";
      var disjointnessCmds =
        linearPermissionInstrumentation.ProcDisjointnessAndWellFormedAssumeCmds(yieldInvariantDecl, true);
      var invariantCmds = yieldInvariantDecl.Requires.Select(requires =>
        requires.Free
          ? (PredicateCmd)new AssumeCmd(requires.tok, requires.Condition)
          : (PredicateCmd)new AssertCmd(requires.tok, requires.Condition)).ToList();

      Substitution assumeSubst = Substituter.SubstitutionFromDictionary(assumeMap);
      Substitution subst = Substituter.SubstitutionFromDictionary(map);
      List<Block> noninterferenceCheckerBlocks = new List<Block>();
      List<Block> labelTargets = new List<Block>();
      Block noninterferenceCheckerBlock = BlockHelper.Block("exit", new List<Cmd>());
      labelTargets.Add(noninterferenceCheckerBlock);
      noninterferenceCheckerBlocks.Add(noninterferenceCheckerBlock);

      var newCmds = new List<Cmd>(disjointnessCmds);
      foreach (var predCmd in invariantCmds)
      {
        var newExpr = Substituter.Apply(assumeSubst, predCmd.Expr);
        newCmds.Add(new AssumeCmd(predCmd.tok, newExpr));
      }
      foreach (var predCmd in invariantCmds)
      {
        if (predCmd is AssertCmd)
        {
          var newExpr = Substituter.Apply(subst, predCmd.Expr);
          AssertCmd assertCmd = new AssertCmd(predCmd.tok, newExpr, predCmd.Attributes);
          assertCmd.Description = new FailureOnlyDescription("Non-interference check failed");
          newCmds.Add(assertCmd);
        }
      }
      newCmds.Add(CmdHelper.AssumeCmd(Expr.False));
      noninterferenceCheckerBlock = BlockHelper.Block("L", newCmds);
      labelTargets.Add(noninterferenceCheckerBlock);
      noninterferenceCheckerBlocks.Add(noninterferenceCheckerBlock);
      noninterferenceCheckerBlocks.Insert(0, BlockHelper.Block("enter", new List<Cmd>(), labelTargets));

      // Create the yield checker procedure
      noninterferenceCheckerName =
        civlTypeChecker.AddNamePrefix($"NoninterferenceChecker_{noninterferenceCheckerName}");
      var noninterferenceCheckerProc = DeclHelper.Procedure(noninterferenceCheckerName,
        inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
      CivlUtil.AddInlineAttribute(noninterferenceCheckerProc);

      // Create the yield checker implementation
      var noninterferenceCheckerImpl = DeclHelper.Implementation(noninterferenceCheckerProc,
        inputs, new List<Variable>(), locals, noninterferenceCheckerBlocks);
      return new List<Declaration> { noninterferenceCheckerProc, noninterferenceCheckerImpl };
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
  }
}