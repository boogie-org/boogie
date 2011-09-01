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
    private DisjointSet uniqueBv32Set = new DisjointSet();

    public int Bits(Expr expr) {
      DisjointSet disjointSet = MakeDisjointSet(expr);
      if (disjointSet.Find() == uniqueBv32Set.Find())
        return 32;
      return 0;
    }

    public Type NewType(Variable var) {
      DisjointSet disjointSet = MakeDisjointSet(var);
      return NewType(var.TypedIdent.Type, disjointSet);
    }

    public bool IsBv32(Expr expr) {
      DisjointSet disjointSet = MakeDisjointSet(expr);
      return (disjointSet.Find() == uniqueBv32Set.Find());
    }

    private Type NewType(Type type, DisjointSet disjointSet) {
      MapType mapType = type as MapType;
      if (mapType == null) {
        if (disjointSet.Find() == uniqueBv32Set.Find())
          return new BvType(32);
        else
          return type;
      }
      else {
        MapDisjointSet mapDisjointSet = disjointSet as MapDisjointSet;
        Debug.Assert(mapDisjointSet != null);
        TypeSeq newArguments = new TypeSeq();
        Type result = NewType(mapType.Result, mapDisjointSet.Result);
        bool newTypeNeeded = (result != mapType.Result);
        for (int i = 0; i < mapType.Arguments.Length; i++) {
          if (mapDisjointSet.Args(i).Find() == uniqueBv32Set.Find()) {
            newArguments.Add(new BvType(32));
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
      DuplicateLiteralExpr duplicateLiteralExpr = new DuplicateLiteralExpr();
      duplicateLiteralExpr.Visit(program);

      BitVectorAnalysis bvAnalyzer = new BitVectorAnalysis();
      bvAnalyzer.Visit(program);
      IntToBvRewriter intToBvRewriter = new IntToBvRewriter(program, bvAnalyzer);
      intToBvRewriter.Visit(program);
      program.TopLevelDeclarations.Add(intToBvRewriter.bv32Id);
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

    public static bool IsComparisonIntegerFunction(Function func) {
      if (func.Name == "INT_LT")
        return true;
      if (func.Name == "INT_ULT")
        return true;
      if (func.Name == "INT_LEQ")
        return true;
      if (func.Name == "INT_ULEQ")
        return true;
      if (func.Name == "INT_GT")
        return true;
      if (func.Name == "INT_UGT")
        return true;
      if (func.Name == "INT_GEQ")
        return true;
      if (func.Name == "INT_UGEQ")
        return true;
      return false;
    }

    public static bool IsIntegerFunction(Function func) {
      if (func.Name == "INT_EQ")
        return true;
      if (func.Name == "INT_NEQ")
        return true;
      if (func.Name == "INT_ADD")
        return true;
      if (func.Name == "INT_SUB")
        return true;
      if (func.Name == "INT_MULT")
        return true;
      if (func.Name == "INT_DIV")
        return true;
      if (func.Name == "INT_LT")
        return true;
      if (func.Name == "INT_ULT")
        return true;
      if (func.Name == "INT_LEQ")
        return true;
      if (func.Name == "INT_ULEQ")
        return true;
      if (func.Name == "INT_GT")
        return true;
      if (func.Name == "INT_UGT")
        return true;
      if (func.Name == "INT_GEQ")
        return true;
      if (func.Name == "INT_UGEQ")
        return true;
      if (func.Name == "INT_AND")
        return true;
      if (func.Name == "INT_OR")
        return true;
      if (func.Name == "INT_XOR")
        return true;
      if (func.Name == "INT_NOT")
        return true;
      if (func.Name == "MINUS_BOTH_PTR_OR_BOTH_INT")
        return true;
      if (func.Name == "MINUS_LEFT_PTR")
        return true;
      if (func.Name == "PLUS")
        return true;
      if (func.Name == "MULT")
        return true;
      if (func.Name == "DIV")
        return true;
      if (func.Name == "BINARY_BOTH_INT")
        return true;
      return false;
    }

    public static bool IsBv32Function(Function func) {
      if (func.Name == "BV32_EQ")
        return true;
      if (func.Name == "BV32_NEQ")
        return true;
      if (func.Name == "BV32_ADD")
        return true;
      if (func.Name == "BV32_SUB")
        return true;
      if (func.Name == "BV32_MULT")
        return true;
      if (func.Name == "BV32_DIV")
        return true;
      if (func.Name == "BV32_LT")
        return true;
      if (func.Name == "BV32_ULT")
        return true;
      if (func.Name == "BV32_LEQ")
        return true;
      if (func.Name == "BV32_ULEQ")
        return true;
      if (func.Name == "BV32_GT")
        return true;
      if (func.Name == "BV32_UGT")
        return true;
      if (func.Name == "BV32_GEQ")
        return true;
      if (func.Name == "BV32_UGEQ")
        return true;
      if (func.Name == "BV32_AND")
        return true;
      if (func.Name == "BV32_OR")
        return true;
      if (func.Name == "BV32_XOR")
        return true;
      if (func.Name == "BV32_NOT")
        return true;
      if (func.Name == "BV32_MINUS_BOTH_PTR_OR_BOTH_INT")
        return true;
      if (func.Name == "BV32_MINUS_LEFT_PTR")
        return true;
      if (func.Name == "BV32_PLUS")
        return true;
      if (func.Name == "BV32_MULT")
        return true;
      if (func.Name == "BV32_DIV")
        return true;
      if (func.Name == "BV32_BINARY_BOTH_INT")
        return true;
      return false;
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

        if (IsIntegerFunction(func)) {
          DisjointSet x;
          if (IsComparisonIntegerFunction(func))
            x = MakeDisjointSet(node.Args[0]);
          else
            x = MakeDisjointSet(node);
          for (int i = 0; i < node.Args.Length; i++) {
            DisjointSet actual = MakeDisjointSet(node.Args[i]);
            actual.Union(x);
          }
        }

        /*
          for (int i = 0; i < node.Args.Length; i++) {
            DisjointSet actual = MakeDisjointSet(node.Args[i]);
            DisjointSet formal = MakeDisjointSet(func.InParams[i]);
            actual.Union(formal);
          }
          Debug.Assert(func.OutParams.Length == 1);
          MakeDisjointSet(node).Union(MakeDisjointSet(func.OutParams[0]));
        */

        if (func.Name == "intToBv32") {
          Debug.Assert(node.Args.Length == 1);
          Expr e = node.Args[0];
          DisjointSet actual = MakeDisjointSet(e);
          actual.Union(uniqueBv32Set);
        }

        if (func.Name == "bv32ToInt") {
          Debug.Assert(node.Args.Length == 1);
          DisjointSet actual = MakeDisjointSet(node);
          actual.Union(uniqueBv32Set);
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

    public override Expr VisitIdentifierExpr(IdentifierExpr node) {
      DisjointSet a = MakeDisjointSet(node);
      DisjointSet b = MakeDisjointSet(node.Decl);
      a.Union(b);
      return base.VisitIdentifierExpr(node);
    }
  }

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
    public Function bv32Id;
    Dictionary<string, Function> intFunctions;
    Dictionary<string, Function> bv32Functions;
    void DiscoverIntAndBv32Functions(Program program) {
      intFunctions = new Dictionary<string, Function>();
      bv32Functions = new Dictionary<string, Function>();
      foreach (Declaration d in program.TopLevelDeclarations) {
        Function func = d as Function;
        if (func == null) continue;
        if (BitVectorAnalysis.IsIntegerFunction(func)) {
          intFunctions.Add(func.Name, func);
        }
        if (BitVectorAnalysis.IsBv32Function(func)) {
          bv32Functions.Add(func.Name, func);
        }
      }
    }
    string IntToBv32(string name) {
      if (name == "INT_EQ")
        return "BV32_EQ";
      if (name == "INT_NEQ")
        return "BV32_NEQ";
      if (name == "INT_ADD")
        return "BV32_ADD";
      if (name == "INT_SUB")
        return "BV32_SUB";
      if (name == "INT_MULT")
        return "BV32_MULT";
      if (name == "INT_DIV")
        return "BV32_DIV";
      if (name == "INT_LT")
        return "BV32_LT";
      if (name == "INT_ULT")
        return "BV32_ULT";
      if (name == "INT_LEQ")
        return "BV32_LEQ";
      if (name == "INT_ULEQ")
        return "BV32_ULEQ";
      if (name == "INT_GT")
        return "BV32_GT";
      if (name == "INT_UGT")
        return "BV32_UGT";
      if (name == "INT_GEQ")
        return "BV32_GEQ";
      if (name == "INT_UGEQ")
        return "BV32_UGEQ";
      if (name == "INT_AND")
        return "BV32_AND";
      if (name == "INT_OR")
        return "BV32_OR";
      if (name == "INT_XOR")
        return "BV32_XOR";
      if (name == "INT_NOT")
        return "BV32_NOT";
      if (name == "MINUS_BOTH_PTR_OR_BOTH_INT")
        return "BV32_MINUS_BOTH_PTR_OR_BOTH_INT";
      if (name == "MINUS_LEFT_PTR")
        return "BV32_MINUS_LEFT_PTR";
      if (name == "PLUS")
        return "BV32_PLUS";
      if (name == "MULT")
        return "BV32_MULT";
      if (name == "DIV")
        return "BV32_DIV";
      if (name == "BINARY_BOTH_INT")
        return "BV32_BINARY_BOTH_INT";
      System.Diagnostics.Debug.Assert(false);
      return "";
    }
  
    Function IntToBv32(Function func) {
      return bv32Functions[IntToBv32(func.Name)];
    }

    public IntToBvRewriter(Program program, BitVectorAnalysis bvAnalyzer) {
      this.bvAnalyzer = bvAnalyzer;
      DiscoverIntAndBv32Functions(program);

      BvType bv32Type = new BvType(32);
      VariableSeq bv32In = new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in", bv32Type), true));
      Formal bv32Out = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out", bv32Type), false);
      bv32Id = new Function(Token.NoToken, "bv32Id", bv32In, bv32Out);
      bv32Id.Body = new IdentifierExpr(Token.NoToken, bv32In[0]);
      bv32Id.AddAttribute("inline");
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
        if (func.Name == "intToBv32" || func.Name == "bv32ToInt") {
          node.Fun = new FunctionCall(bv32Id);
        }
        else if (BitVectorAnalysis.IsIntegerFunction(func) && bvAnalyzer.IsBv32(node.Args[0])) {
          node.Fun = new FunctionCall(IntToBv32(func));
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
