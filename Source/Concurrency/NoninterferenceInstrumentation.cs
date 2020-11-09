using System.Collections.Generic;

namespace Microsoft.Boogie
{
  interface NoninterferenceInstrumentation
  {
    List<Variable> NewLocalVars { get; }
    List<Cmd> CreateInitCmds(Implementation impl);
    List<Cmd> CreateUpdatesToPermissionCollector(Absy absy);
    List<Cmd> CreateCallToYieldProc();
  }

  class NoneNoninterferenceInstrumentation : NoninterferenceInstrumentation
  {
    public List<Variable> NewLocalVars => new List<Variable>();

    public List<Cmd> CreateInitCmds(Implementation impl)
    {
      return new List<Cmd>();
    }

    public List<Cmd> CreateUpdatesToPermissionCollector(Absy absy)
    {
      return new List<Cmd>();
    }

    public List<Cmd> CreateCallToYieldProc()
    {
      return new List<Cmd>();
    }
  }

  class SomeNoninterferenceInstrumentation : NoninterferenceInstrumentation
  {
    private CivlTypeChecker civlTypeChecker;
    private LinearTypeChecker linearTypeChecker;
    private LinearPermissionInstrumentation linearPermissionInstrumentation;
    private Dictionary<Variable, Variable> oldGlobalMap;
    private Procedure yieldProc;

    private List<Variable> newLocalVars;
    private Dictionary<string, Variable> domainNameToHoleVar;

    public SomeNoninterferenceInstrumentation(
      CivlTypeChecker civlTypeChecker,
      LinearTypeChecker linearTypeChecker,
      LinearPermissionInstrumentation linearPermissionInstrumentation,
      Dictionary<Variable, Variable> oldGlobalMap,
      Procedure yieldProc)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.linearTypeChecker = linearTypeChecker;
      this.linearPermissionInstrumentation = linearPermissionInstrumentation;
      this.oldGlobalMap = oldGlobalMap;
      this.yieldProc = yieldProc;
      this.newLocalVars = new List<Variable>();
      this.domainNameToHoleVar = new Dictionary<string, Variable>();
      foreach (string domainName in linearTypeChecker.linearDomains.Keys)
      {
        Variable l = linearTypeChecker.LinearDomainAvailableLocal(domainName);
        domainNameToHoleVar[domainName] = l;
        newLocalVars.Add(l);
      }
    }

    public List<Variable> NewLocalVars => newLocalVars;

    public List<Cmd> CreateInitCmds(Implementation impl)
    {
      Dictionary<string, Expr> domainNameToExpr = linearPermissionInstrumentation.PermissionExprs(impl);
      List<IdentifierExpr> lhss = new List<IdentifierExpr>();
      List<Expr> rhss = new List<Expr>();
      foreach (string domainName in linearTypeChecker.linearDomains.Keys)
      {
        lhss.Add(Expr.Ident(domainNameToHoleVar[domainName]));
        rhss.Add(domainNameToExpr[domainName]);
      }

      var initCmds = new List<Cmd>();
      if (lhss.Count > 0)
      {
        initCmds.Add(CmdHelper.AssignCmd(lhss, rhss));
      }

      return initCmds;
    }

    public List<Cmd> CreateUpdatesToPermissionCollector(Absy absy)
    {
      Dictionary<string, Expr> domainNameToExpr = linearPermissionInstrumentation.PermissionExprs(absy);
      List<IdentifierExpr> lhss = new List<IdentifierExpr>();
      List<Expr> rhss = new List<Expr>();
      foreach (var domainName in linearTypeChecker.linearDomains.Keys)
      {
        lhss.Add(Expr.Ident(domainNameToHoleVar[domainName]));
        rhss.Add(domainNameToExpr[domainName]);
      }

      var cmds = new List<Cmd>();
      if (lhss.Count > 0)
      {
        cmds.Add(CmdHelper.AssignCmd(lhss, rhss));
      }

      return cmds;
    }

    public List<Cmd> CreateCallToYieldProc()
    {
      List<Variable> inputs = new List<Variable>();
      foreach (string domainName in linearTypeChecker.linearDomains.Keys)
      {
        inputs.Add(domainNameToHoleVar[domainName]);
      }

      foreach (Variable g in civlTypeChecker.GlobalVariables)
      {
        inputs.Add(oldGlobalMap[g]);
      }

      CallCmd yieldCallCmd = CmdHelper.CallCmd(yieldProc, inputs, new List<Variable>());
      return new List<Cmd> {yieldCallCmd};
    }
  }
}