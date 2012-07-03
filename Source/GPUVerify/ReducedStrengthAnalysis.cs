using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Linq;

namespace GPUVerify {

class ReducedStrengthAnalysis {

  GPUVerifier verifier;
  Implementation impl;
  VariableDefinitionAnalysis varDefs;

  Dictionary<Variable, List<Tuple<object, Expr>>> multiDefMap = new Dictionary<Variable, List<Tuple<object, Expr>>>();
  Dictionary<string, ModStrideConstraint> strideConstraintMap = new Dictionary<string, ModStrideConstraint>();
  Dictionary<object, List<string>> loopCounterMap = new Dictionary<object, List<string>>();

  ReducedStrengthAnalysis(GPUVerifier v, Implementation i) {
    verifier = v;
    impl = i;
    varDefs = verifier.varDefAnalyses[impl];
  }

  void AddAssignment(object regionId, AssignLhs lhs, Expr rhs) {
    if (lhs is SimpleAssignLhs) {
      var sLhs = (SimpleAssignLhs)lhs;
      var theVar = sLhs.DeepAssignedVariable;
      List<Tuple<object, Expr>> defs;
      if (multiDefMap.ContainsKey(theVar))
        defs = multiDefMap[theVar];
      else
        defs = multiDefMap[theVar] = new List<Tuple<object, Expr>>();
      defs.Add(new Tuple<object, Expr>(regionId, rhs));
    }
  }

  void AnalyseRegion(IRegion region) {
    foreach (var c in region.CmdsChildRegions()) {
      var ac = c as AssignCmd;
      if (ac != null) {
        foreach (var a in ac.Lhss.Zip(ac.Rhss)) {
          AddAssignment(region.Identifier(), a.Item1, a.Item2);
        }
      }
      var child = c as IRegion;
      if (child != null)
        AnalyseRegion(child);
    }
  }

  void Analyse() {
    AnalyseRegion(verifier.RootRegion(impl));
    foreach (var v in multiDefMap.Keys) {
      var defs = multiDefMap[v];
      if (defs.Count != 2)
        continue;
      bool def0IsConst, def1IsConst;
      var def0 = varDefs.SubstDefinitions(defs[0].Item2, impl.Name, out def0IsConst);
      var def1 = varDefs.SubstDefinitions(defs[1].Item2, impl.Name, out def1IsConst);
      if (def0IsConst && !def1IsConst) {
        AddDefinitionPair(v, def0, def1, defs[1].Item1);
      } else if (!def0IsConst && def1IsConst) {
        AddDefinitionPair(v, def1, def0, defs[0].Item1);
      }
    }
    multiDefMap = null;
  }

  private class StrideForm {
    public StrideForm(Kind kind) { this.kind = kind; this.op = null; }
    public StrideForm(Kind kind, Expr op) { this.kind = kind; this.op = op; }
    public enum Kind { Bottom, Identity, Constant, Product, PowerMul, PowerDiv };
    public Kind kind;
    public Expr op;
  }

  private StrideForm ComputeStrideForm(Variable v, Expr e) {
    Expr lhs, rhs;

    if (e is LiteralExpr)
      return new StrideForm(StrideForm.Kind.Constant, e);

    var ie = e as IdentifierExpr;
    if (ie != null) {
      if (ie.Decl is Constant)
        return new StrideForm(StrideForm.Kind.Constant, e);
      if (ie.Decl == v)
        return new StrideForm(StrideForm.Kind.Identity, e);
    }

    if (GPUVerifier.IsBVAdd(e, out lhs, out rhs)) {
      var lhssf = ComputeStrideForm(v, lhs);
      var rhssf = ComputeStrideForm(v, rhs);
      if (lhssf.kind == StrideForm.Kind.Constant &&
          rhssf.kind == StrideForm.Kind.Constant)
        return new StrideForm(StrideForm.Kind.Constant, e);
      else if (lhssf.kind == StrideForm.Kind.Constant &&
               rhssf.kind == StrideForm.Kind.Identity)
        return new StrideForm(StrideForm.Kind.Product, lhs);
      else if (lhssf.kind == StrideForm.Kind.Identity &&
               rhssf.kind == StrideForm.Kind.Constant)
        return new StrideForm(StrideForm.Kind.Product, rhs);
      else if (lhssf.kind == StrideForm.Kind.Constant &&
               rhssf.kind == StrideForm.Kind.Product)
        return new StrideForm(StrideForm.Kind.Product, verifier.MakeBVAdd(lhs, rhssf.op));
      else if (lhssf.kind == StrideForm.Kind.Product &&
               rhssf.kind == StrideForm.Kind.Constant)
        return new StrideForm(StrideForm.Kind.Product, verifier.MakeBVAdd(lhssf.op, rhs));
      else
        return new StrideForm(StrideForm.Kind.Bottom);
    }

    var ne = e as NAryExpr;
    if (ne != null) {
      foreach (Expr op in ne.Args)
        if (ComputeStrideForm(v, op).kind != StrideForm.Kind.Constant)
          return new StrideForm(StrideForm.Kind.Bottom);
      return new StrideForm(StrideForm.Kind.Constant, e);
    }

    return new StrideForm(StrideForm.Kind.Bottom);
  }

  private void AddDefinitionPair(Variable v, Expr constDef, Expr nonConstDef, object nonConstId) {
    var sf = ComputeStrideForm(v, nonConstDef);
    if (sf.kind == StrideForm.Kind.Product) {
      var sc = new ModStrideConstraint(sf.op, constDef);
      if (!sc.IsBottom()) {
        strideConstraintMap[v.Name] = sc;
        List<string> lcs;
        if (loopCounterMap.ContainsKey(nonConstId))
          lcs = loopCounterMap[nonConstId];
        else
          lcs = loopCounterMap[nonConstId] = new List<string>();
        lcs.Add(v.Name);
      }
    }
  }

  public StrideConstraint GetStrideConstraint(string varName) {
    int id;
    var strippedVarName = GPUVerifier.StripThreadIdentifier(varName, out id);
    if (!strideConstraintMap.ContainsKey(strippedVarName))
      return null;

    var msc = strideConstraintMap[strippedVarName];
    if (id == 0)
      return msc;
    return new ModStrideConstraint(verifier.MaybeDualise(msc.mod, id, impl.Name),
                                   verifier.MaybeDualise(msc.modEq, id, impl.Name));
  }

  public IEnumerable<string> StridedLoopCounters(object loopId) {
    if (!loopCounterMap.ContainsKey(loopId))
      return Enumerable.Empty<string>();
    return loopCounterMap[loopId];
  }

  public static ReducedStrengthAnalysis Analyse(GPUVerifier verifier, Implementation impl) {
    var a = new ReducedStrengthAnalysis(verifier, impl);
    a.Analyse();
    return a;
  }
}

}
