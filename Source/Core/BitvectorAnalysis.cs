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
    private DisjointSet uniqueBv8Set = new DisjointSet();
    private DisjointSet uniqueBv16Set = new DisjointSet();
    private DisjointSet uniqueBv32Set = new DisjointSet();
    private DisjointSet uniqueBv64Set = new DisjointSet();

    public int Bits(Expr expr) {
      DisjointSet disjointSet = MakeDisjointSet(expr);
      if (disjointSet.Find() == uniqueBv8Set.Find())
        return 8;
      if (disjointSet.Find() == uniqueBv16Set.Find())
        return 16;
      if (disjointSet.Find() == uniqueBv32Set.Find())
        return 32;
      if (disjointSet.Find() == uniqueBv64Set.Find())
        return 64;
      return 0;
    }

    public Type NewType(Variable var) {
      DisjointSet disjointSet = MakeDisjointSet(var);
      return NewType(var.TypedIdent.Type, disjointSet);
    }

    /*
    private bool Test(DisjointSet disjointSet) {
      DisjointSet bvRoot = uniqueBvSet.Find();
      if (disjointSet == null)
        return true;
      if (disjointSet.Find() == bvRoot)
        return false;
      return true;
    }
    */

    private Type Test(Type type, DisjointSet disjointSet) {
      if (disjointSet.Find() == uniqueBv8Set.Find())
        return new BvType(8);
      if (disjointSet.Find() == uniqueBv16Set.Find())
        return new BvType(16);
      if (disjointSet.Find() == uniqueBv32Set.Find())
        return new BvType(32);
      if (disjointSet.Find() == uniqueBv64Set.Find())
        return new BvType(64);

      return type;
    }

    private Type NewType(Type type, DisjointSet disjointSet) {
      MapType mapType = type as MapType;
      if (mapType == null) {
        return Test(type, disjointSet);
      }
      else {
        MapDisjointSet mapDisjointSet = disjointSet as MapDisjointSet;
        Debug.Assert(mapDisjointSet != null);
        TypeSeq newArguments = new TypeSeq();
        Type result = NewType(mapType.Result, mapDisjointSet.Result);
        bool newTypeNeeded = (result != mapType.Result);
        for (int i = 0; i < mapType.Arguments.Length; i++) {
          newArguments.Add(Test(mapType.Arguments[i], mapDisjointSet.Args(i)));
          newTypeNeeded = newTypeNeeded || (newArguments[i] != mapType.Arguments[i]);
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
      DuplicateLiteralExpr duplicateLiteralExpr = new DuplicateLiteralExpr();
      duplicateLiteralExpr.Visit(program);

      BitVectorAnalysis bvAnalyzer = new BitVectorAnalysis();
      bvAnalyzer.Visit(program);
      /*
      BvToIntRewriter bvtoIntRewriter = new BvToIntRewriter(bvAnalyzer);
      bvtoIntRewriter.Visit(program);
       */
      IntToBvRewriter intToBvRewriter = new IntToBvRewriter(program, bvAnalyzer);
      intToBvRewriter.Visit(program);
      program.TopLevelDeclarations.Add(intToBvRewriter.bv8Id);
      program.TopLevelDeclarations.Add(intToBvRewriter.bv16Id);
      program.TopLevelDeclarations.Add(intToBvRewriter.bv32Id);
      program.TopLevelDeclarations.Add(intToBvRewriter.bv64Id);
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
        MakeDisjointSet(node.Args[0]).Union(MakeDisjointSet(node.Args[1]));
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

        if (func.Name == "intToBv8") {
          Debug.Assert(node.Args.Length == 1);
          Expr e = node.Args[0];
          DisjointSet actual = MakeDisjointSet(e);
          actual.Union(uniqueBv8Set);
        }

        if (func.Name == "intToBv16") {
          Debug.Assert(node.Args.Length == 1);
          Expr e = node.Args[0];
          DisjointSet actual = MakeDisjointSet(e);
          actual.Union(uniqueBv16Set);
        }

        if (func.Name == "intToBv32") {
          Debug.Assert(node.Args.Length == 1);
          Expr e = node.Args[0];
          DisjointSet actual = MakeDisjointSet(e);
          actual.Union(uniqueBv32Set);
        }

        if (func.Name == "intToBv64") {
          Debug.Assert(node.Args.Length == 1);
          Expr e = node.Args[0];
          DisjointSet actual = MakeDisjointSet(e);
          actual.Union(uniqueBv64Set);
        }

        if (func.Name == "bv8ToInt") {
          Debug.Assert(node.Args.Length == 1);
          DisjointSet actual = MakeDisjointSet(node);
          actual.Union(uniqueBv8Set);
        }

        if (func.Name == "bv16ToInt") {
          Debug.Assert(node.Args.Length == 1);
          DisjointSet actual = MakeDisjointSet(node);
          actual.Union(uniqueBv16Set);
        }

        if (func.Name == "bv32ToInt") {
          Debug.Assert(node.Args.Length == 1);
          DisjointSet actual = MakeDisjointSet(node);
          actual.Union(uniqueBv32Set);
        }

        if (func.Name == "bv64ToInt") {
          Debug.Assert(node.Args.Length == 1);
          DisjointSet actual = MakeDisjointSet(node);
          actual.Union(uniqueBv64Set);
        }
      }

      MapSelect select = node.Fun as MapSelect;
      if (select != null) {
        int i = 0;
        MapDisjointSet mapDisjointSet = (MapDisjointSet)MakeDisjointSet(node.Args[i]);
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
        MapDisjointSet mapDisjointSet = (MapDisjointSet)MakeDisjointSet(node.Args[i]);
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

    /*
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
    */

    public override Expr VisitIdentifierExpr(IdentifierExpr node) {
      DisjointSet a = MakeDisjointSet(node);
      DisjointSet b = MakeDisjointSet(node.Decl);
      a.Union(b);
      return base.VisitIdentifierExpr(node);
    }
  }

  /*
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
  */

  class MyLiteralExpr : LiteralExpr {
    public MyLiteralExpr(IToken tok, bool b) : base(tok, b) { }
    public MyLiteralExpr(IToken tok, Basetypes.BigNum v) : base(tok, v) { }
    public MyLiteralExpr(IToken tok, Basetypes.BigNum v, int b) : base(tok, v, b) { }
    public override bool Equals(object obj) {
      return this == obj;
    }
    public override int GetHashCode() {
      return base.GetHashCode();
    }
  }

  class DuplicateLiteralExpr : StandardVisitor {
    public override LiteralExpr VisitLiteralExpr(LiteralExpr node) {
      LiteralExpr litExpr;
      if (node.Val is bool) {
        litExpr = new MyLiteralExpr(Token.NoToken, (bool)node.Val);
      } else if (node.Val is Basetypes.BigNum) {
        litExpr = new MyLiteralExpr(Token.NoToken, (Basetypes.BigNum)node.Val);
      } else {
        BvConst bvconst = (BvConst) node.Val;
        litExpr = new MyLiteralExpr(Token.NoToken, bvconst.Value, bvconst.Bits); 
      }
      litExpr.Typecheck(new TypecheckingContext(null));
      return litExpr;
    }
  }

  class IntToBvRewriter : StandardVisitor {
    private BitVectorAnalysis bvAnalyzer;
    public Function bv8Id;
    public Function bv16Id;
    public Function bv32Id;
    public Function bv64Id;

    public IntToBvRewriter(Program program, BitVectorAnalysis bvAnalyzer) {
      this.bvAnalyzer = bvAnalyzer;
      
      BvType bv8Type = new BvType(8);
      VariableSeq bv8In = new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in", bv8Type), true));
      Formal bv8Out = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out", bv8Type), false);
      bv8Id = new Function(Token.NoToken, "bv8Id", bv8In, bv8Out);
      bv8Id.Body = new IdentifierExpr(Token.NoToken, bv8In[0]);
      bv8Id.AddAttribute("inline");

      BvType bv16Type = new BvType(16);
      VariableSeq bv16In = new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in", bv16Type), true));
      Formal bv16Out = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out", bv16Type), false);
      bv16Id = new Function(Token.NoToken, "bv16Id", bv16In, bv16Out);
      bv16Id.Body = new IdentifierExpr(Token.NoToken, bv16In[0]);
      bv16Id.AddAttribute("inline");

      BvType bv32Type = new BvType(32);
      VariableSeq bv32In = new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in", bv32Type), true));
      Formal bv32Out = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out", bv32Type), false);
      bv32Id = new Function(Token.NoToken, "bv32Id", bv32In, bv32Out);
      bv32Id.Body = new IdentifierExpr(Token.NoToken, bv32In[0]);
      bv32Id.AddAttribute("inline");

      BvType bv64Type = new BvType(64);
      VariableSeq bv64In = new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in", bv64Type), true));
      Formal bv64Out = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out", bv64Type), false);
      bv64Id = new Function(Token.NoToken, "bv64Id", bv64In, bv64Out);
      bv64Id.Body = new IdentifierExpr(Token.NoToken, bv64In[0]);
      bv64Id.AddAttribute("inline");
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
      return base.VisitImplementation(node);
    }

    public override Procedure VisitProcedure(Procedure node) {
      this.VisitVariableSeq(node.InParams);
      this.VisitVariableSeq(node.OutParams);
      return node;
    }

    public override Expr VisitNAryExpr(NAryExpr node) {
      FunctionCall fcall = node.Fun as FunctionCall;
      if (fcall != null) {
        Function func = fcall.Func;
        if (func.Name == "intToBv8" || func.Name == "bv8ToInt") {
          node.Fun = new FunctionCall(bv8Id);
        }
        if (func.Name == "intToBv16" || func.Name == "bv16ToInt") {
          node.Fun = new FunctionCall(bv16Id);
        }
        if (func.Name == "intToBv32" || func.Name == "bv32ToInt") {
          node.Fun = new FunctionCall(bv32Id);
        }
        if (func.Name == "intToBv64" || func.Name == "bv64ToInt") {
          node.Fun = new FunctionCall(bv64Id);
        }
      }
      return base.VisitNAryExpr(node);
    }

    public override LiteralExpr VisitLiteralExpr(LiteralExpr node) {
      int numBits = bvAnalyzer.Bits(node);
      if (numBits > 0 && node.Val is Basetypes.BigNum) {
        return new LiteralExpr(Token.NoToken, (Basetypes.BigNum)node.Val, numBits);
      }
      else {
        return node;
      }
    }
  }
}
