using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Microsoft.Boogie {
  // Build an equivalence relation over the set of program expressions
  // Assignment, equality, function calls and procedure calls are the polymorphic operations 
  // that can be applied to both bitvectors and all other types.
  // Otherwise all bitvector operations are separate
  public class BitVectorAnalysis : StandardVisitor {
    class DisjointSet {
      DisjointSet parent;
      int rank;
      public DisjointSet() {
        this.parent = this;
        this.rank = 0;
      }

      public virtual void Union(DisjointSet that) {
        DisjointSet xRoot = this.Find();
        DisjointSet yRoot = that.Find();
        if (xRoot == yRoot)
          return;

        // x and y are not already in same set. Merge them.
        if (xRoot.rank < yRoot.rank) {
          xRoot.parent = yRoot;
        }
        else if (xRoot.rank > yRoot.rank) {
          yRoot.parent = xRoot;
        }
        else {
          yRoot.parent = xRoot;
          xRoot.rank = xRoot.rank + 1;
        }
      }

      public DisjointSet Find() {
        if (parent == this) {
          return this;
        }
        else {
          parent = parent.Find();
          return parent;
        }
      }
    }

    class MapDisjointSet : DisjointSet {
      DisjointSet[] args;
      DisjointSet result;
      public MapDisjointSet(int arity) 
      : base() {
        args = new DisjointSet[arity];
        for (int i = 0; i < arity; i++) {
          args[i] = null;
        }
        result = null;
      }
      public void UnifyArgs(DisjointSet[] thatArgs) {
        Debug.Assert(this.args.Length == thatArgs.Length);
        for (int i = 0; i < args.Length; i++) {
          if (this.args[i] == null) {
            this.args[i] = thatArgs[i];
          }
          else {
            this.args[i].Union(thatArgs[i]);
          }
        }
      }
      public void UnifyResult(DisjointSet thatResult) {
        if (this.result == null) {
          this.result = thatResult;
        }
        else {
          this.result.Union(thatResult);
        }
      }
      public override void Union(DisjointSet that) {
        base.Union(that);
        MapDisjointSet thatMap = that as MapDisjointSet;
        Debug.Assert(thatMap != null);
        thatMap.UnifyArgs(this.args);
        thatMap.UnifyResult(this.result);
      }
    }

    private Dictionary<Expr, DisjointSet> exprToDisjointSet = new Dictionary<Expr, DisjointSet>();
    private Dictionary<Variable, DisjointSet> varToDisjointSet = new Dictionary<Variable, DisjointSet>();
    private Expr uniqueBvExpr = new IdentifierExpr(Token.NoToken, "UniqueBvExpr");

    private DisjointSet MakeDisjointSet(Expr expr) {
      if (!exprToDisjointSet.ContainsKey(expr)) {
        if (expr.Type == null) {
          expr.Resolve(new ResolutionContext(null));
          expr.Typecheck(new TypecheckingContext(null));
        }
        MapType mapType = expr.Type as MapType;
        if (mapType != null) {
          exprToDisjointSet[expr] = new MapDisjointSet(mapType.Arguments.Length);
        }
        else {
          exprToDisjointSet[expr] = new DisjointSet();
        }
      }
      return exprToDisjointSet[expr];
    }

    private DisjointSet MakeDisjointSet(Variable var) {
      if (!varToDisjointSet.ContainsKey(var)) {
        MapType mapType = var.TypedIdent.Type as MapType;
        if (mapType != null) {
          varToDisjointSet[var] = new MapDisjointSet(mapType.Arguments.Length);
        }
        else {
          varToDisjointSet[var] = new DisjointSet();
        }
      }
      return varToDisjointSet[var];
    }

    public static void DoBitVectorAnalysis(Program program) {
      BitVectorAnalysis bvAnalyzer = new BitVectorAnalysis();
      bvAnalyzer.Visit(program);
    }

    public override Implementation VisitImplementation(Implementation node) {
      for (int i = 0; i < node.InParams.Length; i++) {
        DisjointSet a = MakeDisjointSet(node.InParams[i]);
        DisjointSet b = MakeDisjointSet(node.Proc.InParams[i]);
        a.Union(b);
      }
      return base.VisitImplementation(node);
    }

    public override Cmd VisitAssignCmd(AssignCmd node) {
      AssignCmd simpleAssignCmd = node.AsSimpleAssignCmd;
      List<AssignLhs> lhss = simpleAssignCmd.Lhss;
      List<Expr> rhss = simpleAssignCmd.Rhss;
      foreach (Expr rhs in rhss) {
        VisitExpr(rhs);
      }
      for (int i = 0; i < lhss.Count; i++) {
        SimpleAssignLhs lhs = (SimpleAssignLhs) lhss[i];
        DisjointSet lhsSet = MakeDisjointSet(lhs.AsExpr);
        lhsSet.Union(MakeDisjointSet(rhss[i]));
      }
      return base.VisitAssignCmd(node);
    }

    public override Cmd VisitCallCmd(CallCmd node) {
      for (int i = 0; i < node.Ins.Count; i++) {
        DisjointSet actual = MakeDisjointSet(node.Ins[i]);
        DisjointSet formal = MakeDisjointSet(node.Proc.InParams[i]);
        actual.Union(formal);
      }
      for (int i = 0; i < node.Outs.Count; i++) {
        DisjointSet actual = MakeDisjointSet(node.Outs[i]);
        DisjointSet formal = MakeDisjointSet(node.Proc.OutParams[i]);
        actual.Union(formal);
      }
      return base.VisitCallCmd(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node) {
      FunctionCall fcall = node.Fun as FunctionCall;
      if (fcall != null) {
        Function func = fcall.Func;

        // unify each actual argument with corresponding formal argument
        for (int i = 0; i < node.Args.Length; i++) {
          DisjointSet actual = MakeDisjointSet(node.Args[i]);
          DisjointSet formal = MakeDisjointSet(func.InParams[i]);
          actual.Union(formal);
        }
        
        if (func.FindStringAttribute("bvbuiltin") != null) {
          // unify each actual argument with uniqueBvExpr
          for (int i = 0; i < node.Args.Length; i++) {
            DisjointSet actual = MakeDisjointSet(node.Args[i]);
            actual.Union(MakeDisjointSet(uniqueBvExpr));
          }
        }
      }
      
      MapSelect select = node.Fun as MapSelect;
      if (select != null) {
        int i = 0;
        MapDisjointSet mapDisjointSet = (MapDisjointSet) MakeDisjointSet(node.Args[i]);
        i++;
        DisjointSet[] args = new DisjointSet[node.Args.Length - 1];
        for (; i < node.Args.Length; i++) {
          args[i - 1] = MakeDisjointSet(node.Args[i]);
        }
        mapDisjointSet.UnifyArgs(args);
        mapDisjointSet.UnifyResult(MakeDisjointSet(node));
      }

      MapStore store = node.Fun as MapStore;
      if (store != null) {
        int i = 0;
        MapDisjointSet mapDisjointSet = (MapDisjointSet) MakeDisjointSet(node.Args[i]);
        i++;
        DisjointSet[] args = new DisjointSet[node.Args.Length - 2];
        for (; i < node.Args.Length - 1; i++) {
          args[i - 1] = MakeDisjointSet(node.Args[i]);
        }
        mapDisjointSet.UnifyArgs(args);
        mapDisjointSet.UnifyResult(MakeDisjointSet(node.Args[i]));
        mapDisjointSet.Union(MakeDisjointSet(node));
      }

      return base.VisitNAryExpr(node);
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node) {
      DisjointSet a = MakeDisjointSet(node);
      DisjointSet b = MakeDisjointSet(node.Decl);
      a.Union(b);
      return base.VisitIdentifierExpr(node);
    }
  }
}
