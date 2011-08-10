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
      private DisjointSet[] args;
      public DisjointSet Args(int i) {
        return args[i];
      }
      
      private DisjointSet result;
      public DisjointSet Result { get { return result; } }

      public MapDisjointSet(DisjointSet[] args, DisjointSet result) {
        this.args = args;
        this.result = result;
      }
      
      public override void Union(DisjointSet that) {
        base.Union(that);
        MapDisjointSet thatMap = that as MapDisjointSet;
        Debug.Assert(thatMap != null);
        Debug.Assert(this.args.Length == thatMap.args.Length);
        
        // unify args
        for (int i = 0; i < this.args.Length; i++) {
          if (this.args[i] == null) {
            this.args[i] = thatMap.args[i];
          }
          else if (thatMap.args[i] == null) {
            thatMap.args[i] = this.args[i];
          }
          else {
            this.args[i].Union(thatMap.args[i]);
          }
        }

        // unify result
        if (this.result == null) {
          this.result = thatMap.Result;
        }
        else if (thatMap.result == null) {
          thatMap.result = this.result;
        }
        else {
          this.result.Union(thatMap.result);
        }
      }
    }

    private Dictionary<Expr, DisjointSet> exprToDisjointSet = new Dictionary<Expr, DisjointSet>();
    private Dictionary<Variable, DisjointSet> varToDisjointSet = new Dictionary<Variable, DisjointSet>();
    private DisjointSet uniqueBvSet = new DisjointSet();

    public Type NewType(Variable var) {
      DisjointSet disjointSet = MakeDisjointSet(var);
      return NewType(var.TypedIdent.Type, disjointSet);
    }

    private bool Test(DisjointSet disjointSet) {
      DisjointSet bvRoot = uniqueBvSet.Find();
      if (disjointSet == null)
        return true;
      if (disjointSet.Find() == bvRoot)
        return false;
      return true;
    }

    private Type NewType(Type type, DisjointSet disjointSet) {
      MapType mapType = type as MapType;
      if (mapType == null) {
        if (type is BvType && Test(disjointSet)) {
          return Type.Int;
        }
        else {
          return type;
        }
      }
      else {
        MapDisjointSet mapDisjointSet = disjointSet as MapDisjointSet;
        Debug.Assert(mapDisjointSet != null);
        TypeSeq newArguments = new TypeSeq();
        Type result = NewType(mapType.Result, mapDisjointSet.Result);
        bool newTypeNeeded = (result != mapType.Result);
        for (int i = 0; i < mapType.Arguments.Length; i++) {
          if (mapType.Arguments[i] is BvType && Test(mapDisjointSet.Args(i))) {
            newArguments.Add(Type.Int);
            newTypeNeeded = true;
          }
          else {
            newArguments.Add(mapType.Arguments[i]);
          }
        }
        if (newTypeNeeded) {
          return new MapType(mapType.tok, mapType.TypeParameters, newArguments, result);
        }
        else {
          return mapType;
        }
      }
    }

    private DisjointSet MakeDisjointSet(Type type) {
      MapType mapType = type as MapType;
      if (mapType == null) {
        return new DisjointSet();
      }
      DisjointSet[] args = new DisjointSet[mapType.Arguments.Length];
      for (int i = 0; i < args.Length; i++) {
        args[i] = MakeDisjointSet(mapType.Arguments[i]);
      }
      DisjointSet result = MakeDisjointSet(mapType.Result);
      return new MapDisjointSet(args, result);
    }

    private DisjointSet MakeDisjointSet(Expr expr) {
      if (!exprToDisjointSet.ContainsKey(expr)) {
        Debug.Assert(expr.Type != null);
        exprToDisjointSet[expr] = MakeDisjointSet(expr.Type);
      }
      return exprToDisjointSet[expr];
    }

    private DisjointSet MakeDisjointSet(Variable var) {
      if (!varToDisjointSet.ContainsKey(var)) {
        varToDisjointSet[var] = MakeDisjointSet(var.TypedIdent.Type);
      }
      return varToDisjointSet[var];
    }

    public static void DoBitVectorAnalysis(Program program) {
      BitVectorAnalysis bvAnalyzer = new BitVectorAnalysis();
      bvAnalyzer.Visit(program);
      BvToIntRewriter bvtoIntRewriter = new BvToIntRewriter(bvAnalyzer);
      bvtoIntRewriter.Visit(program);
    }

    public override Implementation VisitImplementation(Implementation node) {
      for (int i = 0; i < node.InParams.Length; i++) {
        DisjointSet a = MakeDisjointSet(node.InParams[i]);
        DisjointSet b = MakeDisjointSet(node.Proc.InParams[i]);
        a.Union(b);
      }
      for (int i = 0; i < node.OutParams.Length; i++) {
        DisjointSet a = MakeDisjointSet(node.OutParams[i]);
        DisjointSet b = MakeDisjointSet(node.Proc.OutParams[i]);
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
      BinaryOperator op = node.Fun as BinaryOperator;
      if (op != null) {
        Debug.Assert(node.Args.Length == 2);
        if (op.Op == BinaryOperator.Opcode.Eq || op.Op == BinaryOperator.Opcode.Neq) {
          MakeDisjointSet(node.Args[0]).Union(MakeDisjointSet(node.Args[1]));
        }
      }

      FunctionCall fcall = node.Fun as FunctionCall;
      if (fcall != null) {
        Function func = fcall.Func;

        // unify each actual argument with corresponding formal argument
        for (int i = 0; i < node.Args.Length; i++) {
          DisjointSet actual = MakeDisjointSet(node.Args[i]);
          DisjointSet formal = MakeDisjointSet(func.InParams[i]);
          actual.Union(formal);
        }
        Debug.Assert(func.OutParams.Length == 1);
        MakeDisjointSet(node).Union(MakeDisjointSet(func.OutParams[0]));

        if (func.FindStringAttribute("bvbuiltin") != null) {
          // unify each actual argument with uniqueBvExpr
          foreach (Expr e in node.Args) {
            DisjointSet actual = MakeDisjointSet(e);
            actual.Union(uniqueBvSet);
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
        mapDisjointSet.Union(new MapDisjointSet(args, MakeDisjointSet(node)));
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
        mapDisjointSet.Union(new MapDisjointSet(args, MakeDisjointSet(node.Args[i])));
        mapDisjointSet.Union(MakeDisjointSet(node));
      }

      return base.VisitNAryExpr(node);
    }

    public override BvConcatExpr VisitBvConcatExpr(BvConcatExpr node) {
      foreach (Expr e in node.Arguments) {
        DisjointSet actual = MakeDisjointSet(e);
        actual.Union(uniqueBvSet);
      }
      return base.VisitBvConcatExpr(node);
    }

    public override BvExtractExpr VisitBvExtractExpr(BvExtractExpr node) {
      DisjointSet disjointSet = MakeDisjointSet(node.Bitvector);
      disjointSet.Union(uniqueBvSet);
      return base.VisitBvExtractExpr(node);
    }

    public override LiteralExpr VisitLiteralExpr(LiteralExpr node) {
      if (node.Val is BvConst) {
        DisjointSet disjointSet = MakeDisjointSet(node);
        disjointSet.Union(uniqueBvSet);
      }
      return base.VisitLiteralExpr(node);
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node) {
      DisjointSet a = MakeDisjointSet(node);
      DisjointSet b = MakeDisjointSet(node.Decl);
      a.Union(b);
      return base.VisitIdentifierExpr(node);
    }
  }

  class BvToIntRewriter : StandardVisitor {
    private BitVectorAnalysis bvAnalyzer;
    public BvToIntRewriter(BitVectorAnalysis bvAnalyzer) {
      this.bvAnalyzer = bvAnalyzer;
    }
    
    public override Constant VisitConstant(Constant node) {
      node.TypedIdent.Type = bvAnalyzer.NewType(node);
      return node;
    }
    
    public override Variable VisitVariable(Variable node) {
      node.TypedIdent.Type = bvAnalyzer.NewType(node);
      return node;
    }

    public override Implementation VisitImplementation(Implementation node) {
      this.VisitVariableSeq(node.LocVars);
      this.VisitVariableSeq(node.InParams);
      this.VisitVariableSeq(node.OutParams);
      return node;
    }

    public override Procedure VisitProcedure(Procedure node) {
      this.VisitVariableSeq(node.InParams);
      this.VisitVariableSeq(node.OutParams);
      return node;
    }
  }
}
