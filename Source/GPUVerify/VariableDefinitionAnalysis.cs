using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;

namespace GPUVerify {

using VarDef = Tuple<Expr, bool>;

class VariableDefinitionAnalysis {
  GPUVerifier verifier;
  Implementation impl;

  Dictionary<Variable, VarDef> defMap = new Dictionary<Variable, VarDef>();
  Dictionary<string, VarDef> namedDefMap = new Dictionary<string, VarDef>();
  bool changed;

  VariableDefinitionAnalysis(GPUVerifier v, Implementation i) {
    verifier = v;
    impl = i;
  }

  private class IsConstantVisitor : StandardVisitor {
    public bool isConstant = true;

    public IsConstantVisitor() {}

    public override Expr VisitNAryExpr(NAryExpr expr) {
      if (expr.Fun is MapSelect) {
        isConstant = false;
        return expr;
      } else
        return base.VisitNAryExpr(expr);
    }
  };

  private class IsDerivedFromConstantsVisitor : StandardVisitor {
    private VariableDefinitionAnalysis analysis;
    public bool isDerivedFromConstants = true;

    public IsDerivedFromConstantsVisitor(VariableDefinitionAnalysis a) {
      analysis = a;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr expr) {
      if (expr.Decl is Constant)
        return expr;
      if (!analysis.defMap.ContainsKey(expr.Decl) || !analysis.defMap[expr.Decl].Item2)
        isDerivedFromConstants = false;
      return expr;
    }
  };

  bool IsConstant(Expr e) {
    var v = new IsConstantVisitor();
    v.Visit(e);
    return v.isConstant;
  }

  bool IsDerivedFromConstants(Expr e) {
    var v = new IsDerivedFromConstantsVisitor(this);
    v.Visit(e);
    return v.isDerivedFromConstants;
  }

  void UpdateDefMap(Variable v, Expr def, bool isConstant) {
    if (!defMap.ContainsKey(v)) {
      changed = true;
      defMap[v] = new VarDef(def, isConstant);
      return;
    }

    var d = defMap[v];
    if (d.Item1 != def || d.Item2 != isConstant) {
      changed = true;
      defMap[v] = new VarDef(def, isConstant);
    }
  }

  void AddAssignment(AssignLhs lhs, Expr rhs) {
    if (lhs is SimpleAssignLhs) {
      var sLhs = (SimpleAssignLhs)lhs;
      var theVar = sLhs.DeepAssignedVariable;
      if ((defMap.ContainsKey(theVar) && defMap[theVar].Item1 != rhs) || !IsConstant(rhs)) {
        UpdateDefMap(theVar, null, false);
      } else {
        UpdateDefMap(theVar, rhs, IsDerivedFromConstants(rhs));
      }
    }
  }

  void Analyse() {
    do {
      changed = false;
      foreach (var c in verifier.RootRegion(impl).Cmds()) {
        if (c is AssignCmd) {
          var aCmd = (AssignCmd)c;
          foreach (var a in aCmd.Lhss.Zip(aCmd.Rhss)) {
            AddAssignment(a.Item1, a.Item2);
          }
        }
        if (c is HavocCmd) {
          var hCmd = (HavocCmd)c;
          foreach (Variable v in hCmd.Vars)
            UpdateDefMap(v, null, false);
        }
      }
    } while (changed);
  }

  private class BuildNamedDefVisitor : Duplicator {
    private VariableDefinitionAnalysis analysis;

    public BuildNamedDefVisitor(VariableDefinitionAnalysis a) {
      analysis = a;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr expr) {
      if (expr.Decl is Constant)
        return expr;
      return analysis.BuildNamedDefFor(expr.Decl, expr);
    }
  }

  Expr BuildNamedDefFor(Variable v, Expr e = null) {
    VarDef def;
    if (namedDefMap.TryGetValue(v.Name, out def))
      return def.Item1;

    def = defMap[v];
    Expr defExpr;
    if (def.Item1 == null)
      defExpr = e;
    else
      defExpr = (Expr)new BuildNamedDefVisitor(this).Visit(def.Item1.Clone());
    namedDefMap[v.Name] = new VarDef(defExpr, def.Item2);

    return defExpr;
  }

  void BuildNamedDefMap() {
    foreach (var v in defMap.Keys)
      if (defMap[v].Item1 != null)
        BuildNamedDefFor(v);
  }

  private class SubstDefVisitor : Duplicator {
    private VariableDefinitionAnalysis analysis;
    private string procName;
    public bool isSubstitutable = true;
    public bool isConstant = true;

    public SubstDefVisitor(VariableDefinitionAnalysis a, string p) {
      analysis = a;
      procName = p;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr expr) {
      if (expr.Decl is Constant)
        return expr;
      int id;
      var varName = GPUVerifier.StripThreadIdentifier(expr.Decl.Name, out id);
      VarDef def;
      if (!analysis.namedDefMap.TryGetValue(varName, out def)) {
        isSubstitutable = false;
        return null;
      }
      if (!def.Item2)
        isConstant = false;
      if (id == 0)
        return def.Item1;
      else
        return (Expr)new VariableDualiser(id, analysis.verifier.uniformityAnalyser, procName).Visit(def.Item1.Clone());
    }
  }

  public Expr SubstDefinitions(Expr e, string procName, out bool isConstant) {
    var v = new SubstDefVisitor(this, procName);
    Expr result = (Expr)v.Visit(e.Clone());
    isConstant = v.isConstant;
    if (!v.isSubstitutable)
      return null;
    return result;
  }

  public Expr SubstDefinitions(Expr e, string procName) {
    bool isConstant;
    var result = SubstDefinitions(e, procName, out isConstant);
    if (!isConstant)
      return null;
    return result;
  }

  public static VariableDefinitionAnalysis Analyse(GPUVerifier verifier, Implementation impl) {
    var a = new VariableDefinitionAnalysis(verifier, impl);
    a.Analyse();
    a.BuildNamedDefMap();
    a.defMap = null;
    return a;
  }

}

}
