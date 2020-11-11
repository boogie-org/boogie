using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class LinearPermissionInstrumentation
  {
    private CivlTypeChecker civlTypeChecker;
    private int layerNum;
    private AbsyMap absyMap;
    private Dictionary<string, Variable> domainNameToHoleVar;
    private Dictionary<Variable, Variable> localVarMap;

    public LinearPermissionInstrumentation(
      CivlTypeChecker civlTypeChecker,
      int layerNum,
      AbsyMap absyMap,
      Dictionary<string, Variable> domainNameToHoleVar,
      Dictionary<Variable, Variable> localVarMap)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.layerNum = layerNum;
      this.absyMap = absyMap;
      this.domainNameToHoleVar = domainNameToHoleVar;
      this.localVarMap = localVarMap;
    }

    public LinearPermissionInstrumentation(
      CivlTypeChecker civlTypeChecker,
      int layerNum,
      AbsyMap absyMap)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.layerNum = layerNum;
      this.absyMap = absyMap;
      this.domainNameToHoleVar = new Dictionary<string, Variable>();
      this.localVarMap = new Dictionary<Variable, Variable>();
    }

    public List<Cmd> ProcDisjointnessAssumeCmds(Procedure proc, bool atEntry)
    {
      IEnumerable<Variable> availableVars = atEntry
        ? FilterInParams(proc.InParams)
        : FilterInOutParams(proc.InParams.Union(proc.OutParams));
      return DisjointnessExprs(availableVars).Select(expr => CmdHelper.AssumeCmd(expr)).ToList<Cmd>();
    }

    public List<Cmd> DisjointnessAssumeCmds(Absy absy, bool addGlobals)
    {
      var availableVars = AvailableLinearLocalVars(absy).Union(addGlobals ? LinearGlobalVars() : new List<Variable>());
      return DisjointnessExprs(availableVars).Select(expr => CmdHelper.AssumeCmd(expr)).ToList<Cmd>();
    }

    public List<Expr> DisjointnessExprs(Absy absy, bool addGlobals)
    {
      var availableVars = AvailableLinearLocalVars(absy).Union(addGlobals ? LinearGlobalVars() : new List<Variable>());
      return DisjointnessExprs(availableVars);
    }

    public Dictionary<string, Expr> PermissionExprs(Absy absy)
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      var domainNameToScope = new Dictionary<string, HashSet<Variable>>();
      foreach (var domainName in linearTypeChecker.linearDomains.Keys)
      {
        domainNameToScope[domainName] = new HashSet<Variable>();
      }

      var availableVars = AvailableLinearLocalVars(absy).Union(LinearGlobalVars());
      foreach (var v in availableVars)
      {
        var domainName = linearTypeChecker.FindDomainName(v);
        domainNameToScope[domainName].Add(MapVariable(v));
      }

      var domainNameToExpr = new Dictionary<string, Expr>();
      foreach (var domainName in domainNameToScope.Keys)
      {
        var permissionExprs =
          linearTypeChecker.PermissionExprForEachVariable(domainName, domainNameToScope[domainName]);
        domainNameToExpr[domainName] = linearTypeChecker.UnionExprForPermissions(domainName, permissionExprs);
      }

      return domainNameToExpr;
    }

    public void AddDisjointnessAssumptions(Implementation impl, HashSet<Procedure> yieldingProcs)
    {
      // calls and parallel calls
      foreach (var b in impl.Blocks)
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in b.Cmds)
        {
          newCmds.Add(cmd);
          if (cmd is ParCallCmd)
          {
            newCmds.AddRange(DisjointnessAssumeCmds(cmd, true));
          }
        }

        b.Cmds = newCmds;
      }

      // loop headers
      impl.PruneUnreachableBlocks();
      impl.ComputePredecessorsForBlocks();
      var graph = Program.GraphFromImpl(impl);
      graph.ComputeLoops();
      if (!graph.Reducible)
      {
        throw new Exception("Irreducible flow graphs are unsupported.");
      }

      var loopHeaders = new HashSet<Block>(graph.Headers);
      foreach (var header in loopHeaders)
      {
        var newCmds = DisjointnessAssumeCmds(header, true);
        newCmds.AddRange(header.Cmds);
        header.Cmds = newCmds;
      }
    }

    private List<Expr> DisjointnessExprs(IEnumerable<Variable> availableVars)
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      var domainNameToScope = new Dictionary<string, HashSet<Variable>>();
      foreach (var domainName in linearTypeChecker.linearDomains.Keys)
      {
        domainNameToScope[domainName] = new HashSet<Variable>();
      }

      foreach (var v in availableVars)
      {
        var domainName = linearTypeChecker.FindDomainName(v);
        domainNameToScope[domainName].Add(MapVariable(v));
      }

      var newExprs = new List<Expr>();
      foreach (var domainName in linearTypeChecker.linearDomains.Keys)
      {
        var permissionExprs =
          linearTypeChecker
            .PermissionExprForEachVariable(domainName, domainNameToScope[domainName])
            .Union(
              domainNameToHoleVar.ContainsKey(domainName)
                ? new List<Expr> {Expr.Ident(domainNameToHoleVar[domainName])}
                : new List<Expr>());
        var expr = linearTypeChecker.DisjointnessExprForPermissions(domainName, permissionExprs);
        if (!expr.Equals(Expr.True))
        {
          newExprs.Add(expr);
        }
      }

      return newExprs;
    }

    private IEnumerable<Variable> AvailableLinearLocalVars(Absy absy)
    {
      if (absy is Implementation impl)
      {
        return FilterInParams(absyMap.OriginalOrInput(impl).InParams);
      }

      if (absy is Procedure proc)
      {
        return FilterInParams(absyMap.OriginalOrInput(proc).InParams);
      }

      return civlTypeChecker.linearTypeChecker.AvailableLinearVars(absyMap[absy]).Where(v =>
        !(v is GlobalVariable) &&
        civlTypeChecker.LocalVariableLayerRange(v).Contains(layerNum));
    }

    private IEnumerable<Variable> FilterInParams(IEnumerable<Variable> locals)
    {
      return Filter(locals, x => x == LinearKind.LINEAR || x == LinearKind.LINEAR_IN);
    }

    private IEnumerable<Variable> FilterInOutParams(IEnumerable<Variable> locals)
    {
      return Filter(locals, x => x == LinearKind.LINEAR || x == LinearKind.LINEAR_OUT);
    }

    private IEnumerable<Variable> Filter(IEnumerable<Variable> locals, Predicate<LinearKind> pred)
    {
      return locals.Where(v =>
        pred(civlTypeChecker.linearTypeChecker.FindLinearKind(v)) &&
        civlTypeChecker.LocalVariableLayerRange(v).Contains(layerNum));
    }

    private IEnumerable<Variable> LinearGlobalVars()
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      return linearTypeChecker.program.GlobalVariables.Where(v =>
        linearTypeChecker.FindLinearKind(v) == LinearKind.LINEAR &&
        civlTypeChecker.GlobalVariableLayerRange(v).Contains(layerNum));
    }

    private Variable MapVariable(Variable v)
    {
      return localVarMap.ContainsKey(v) ? localVarMap[v] : v;
    }
  }
}