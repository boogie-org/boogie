//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Basetypes;

// Some visitor skeletons for the VCExpression AST

namespace Microsoft.Boogie.VCExprAST {
  using Microsoft.Boogie;

  [ContractClass(typeof(IVCExprVisitorContracts<,>))]
  public interface IVCExprVisitor<Result, Arg> {
    Result Visit(VCExprLiteral/*!*/ node, Arg arg);
    Result Visit(VCExprNAry/*!*/ node, Arg arg);
    Result Visit(VCExprVar/*!*/ node, Arg arg);
    Result Visit(VCExprQuantifier/*!*/ node, Arg arg);
    Result Visit(VCExprLet/*!*/ node, Arg arg);
  }
  [ContractClassFor(typeof(IVCExprVisitor<,>))]
  public abstract class IVCExprVisitorContracts<Result, Arg> : IVCExprVisitor<Result, Arg> {
    #region IVCExprVisitor Members

    public Result Visit(VCExprLiteral node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result Visit(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result Visit(VCExprVar node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result Visit(VCExprQuantifier node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result Visit(VCExprLet node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    #endregion
  }
  [ContractClass(typeof(IVCExprOpVisitorContracts<,>))]
  public interface IVCExprOpVisitor<Result, Arg> {
    Result VisitNotOp(VCExprNAry node, Arg arg);
    Result VisitEqOp(VCExprNAry node, Arg arg);
    Result VisitNeqOp(VCExprNAry node, Arg arg);
    Result VisitAndOp(VCExprNAry node, Arg arg);
    Result VisitOrOp(VCExprNAry node, Arg arg);
    Result VisitImpliesOp(VCExprNAry node, Arg arg);
    Result VisitDistinctOp(VCExprNAry node, Arg arg);
    Result VisitLabelOp(VCExprNAry node, Arg arg);
    Result VisitSelectOp(VCExprNAry node, Arg arg);
    Result VisitStoreOp(VCExprNAry node, Arg arg);
    Result VisitFloatAddOp(VCExprNAry node, Arg arg);
    Result VisitFloatSubOp(VCExprNAry node, Arg arg);
    Result VisitFloatMulOp(VCExprNAry node, Arg arg);
    Result VisitFloatDivOp(VCExprNAry node, Arg arg);
    Result VisitFloatLeqOp(VCExprNAry node, Arg arg);
    Result VisitFloatLtOp(VCExprNAry node, Arg arg);
    Result VisitFloatGeqOp(VCExprNAry node, Arg arg);
    Result VisitFloatGtOp(VCExprNAry node, Arg arg);
    Result VisitFloatEqOp(VCExprNAry node, Arg arg);
    Result VisitFloatNeqOp(VCExprNAry node, Arg arg);
    Result VisitBvOp(VCExprNAry node, Arg arg);
    Result VisitBvExtractOp(VCExprNAry node, Arg arg);
    Result VisitBvConcatOp(VCExprNAry node, Arg arg);
    Result VisitAddOp(VCExprNAry node, Arg arg);
    Result VisitSubOp(VCExprNAry node, Arg arg);
    Result VisitMulOp(VCExprNAry node, Arg arg);
    Result VisitDivOp(VCExprNAry node, Arg arg);
    Result VisitModOp(VCExprNAry node, Arg arg);
    Result VisitRealDivOp(VCExprNAry node, Arg arg);
    Result VisitPowOp(VCExprNAry node, Arg arg);
    Result VisitLtOp(VCExprNAry node, Arg arg);
    Result VisitLeOp(VCExprNAry node, Arg arg);
    Result VisitGtOp(VCExprNAry node, Arg arg);
    Result VisitGeOp(VCExprNAry node, Arg arg);
    Result VisitSubtypeOp(VCExprNAry node, Arg arg);
    Result VisitSubtype3Op(VCExprNAry node, Arg arg);
    Result VisitToIntOp(VCExprNAry node, Arg arg);
    Result VisitToRealOp(VCExprNAry node, Arg arg);
    Result VisitBoogieFunctionOp(VCExprNAry node, Arg arg);
    Result VisitIfThenElseOp(VCExprNAry node, Arg arg);
    Result VisitCustomOp(VCExprNAry node, Arg arg);
  }
  [ContractClassFor(typeof(IVCExprOpVisitor<,>))]
  public abstract class IVCExprOpVisitorContracts<Result, Arg> : IVCExprOpVisitor<Result, Arg> {
    #region IVCExprOpVisitor<Result,Arg> Members

    public Result VisitNotOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitEqOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitNeqOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitAndOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitOrOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitImpliesOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitDistinctOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitLabelOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitSelectOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitStoreOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatAddOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatSubOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatMulOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatDivOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatLeqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatLtOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatGeqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatGtOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatEqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatNeqOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitBvOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitBvExtractOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitBvConcatOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitAddOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitSubOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitMulOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitDivOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitModOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitRealDivOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitPowOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitLtOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitLeOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitGtOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitGeOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitSubtypeOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitSubtype3Op(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitToIntOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitToRealOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitToFloat(VCExprNAry node, Arg arg) //TODO: modify later
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitBoogieFunctionOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitIfThenElseOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitCustomOp(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    #endregion
  }

  //////////////////////////////////////////////////////////////////////////////
  // Standard implementations that make it easier to create own visitors

  // Simple traversal of VCExprs. The Visit implementations work
  // recursively, apart from the implementation for VCExprNAry that
  // uses a stack when applied to nested nodes with the same
  // operator, e.g., (AND (AND (AND ...) ...) ...). This is necessary
  // to avoid stack overflows


  [ContractClass(typeof(TraversingVCExprVisitorContracts<,>))]
  public abstract class TraversingVCExprVisitor<Result, Arg>
                        : IVCExprVisitor<Result, Arg> {
    protected abstract Result StandardResult(VCExpr/*!*/ node, Arg arg);

    public Result Traverse(VCExpr node, Arg arg) {
      Contract.Requires(node != null);
      return node.Accept(this, arg);
    }

    public virtual Result Visit(VCExprLiteral node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result Visit(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      Result res = StandardResult(node, arg);


      if (node.TypeParamArity == 0 &&
          (node.Op == VCExpressionGenerator.AndOp ||
           node.Op == VCExpressionGenerator.OrOp ||
           node.Op == VCExpressionGenerator.ImpliesOp)) {
        Contract.Assert(node.Op != null);
        VCExprOp op = node.Op;
        HashSet<VCExprOp> ops = new HashSet<VCExprOp>();
        ops.Add(VCExpressionGenerator.AndOp);
        ops.Add(VCExpressionGenerator.OrOp);
        ops.Add(VCExpressionGenerator.ImpliesOp);
        IEnumerator enumerator = new VCExprNAryMultiUniformOpEnumerator(node, ops);
        while (enumerator.MoveNext()) {
          VCExpr expr = cce.NonNull((VCExpr)enumerator.Current);
          VCExprNAry naryExpr = expr as VCExprNAry;
          if (naryExpr == null || !ops.Contains(naryExpr.Op)) {
            expr.Accept(this, arg);
          } else {
            StandardResult(expr, arg);
          }
        }
      } else {
        foreach (VCExpr e in node) {
          Contract.Assert(e != null);
          e.Accept(this, arg);
        }
      }

      return res;
    }

    public virtual Result Visit(VCExprVar node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result Visit(VCExprQuantifier node, Arg arg) {
      //Contract.Requires(node != null);
      Result res = StandardResult(node, arg);
      foreach (VCTrigger/*!*/ trigger in node.Triggers) {
        Contract.Assert(trigger != null);
        foreach (VCExpr/*!*/ expr in trigger.Exprs) {
          Contract.Assert(expr != null);
          expr.Accept(this, arg);
        }
      }
      node.Body.Accept(this, arg);
      return res;
    }
    public virtual Result Visit(VCExprLet node, Arg arg) {
      //Contract.Requires(node != null);
      Result res = StandardResult(node, arg);
      // visit the bound expressions first
      foreach (VCExprLetBinding/*!*/ binding in node) {
        Contract.Assert(binding != null);
        binding.E.Accept(this, arg);
      }
      node.Body.Accept(this, arg);
      return res;
    }
  }
  [ContractClassFor(typeof(TraversingVCExprVisitor<,>))]
  public abstract class TraversingVCExprVisitorContracts<Result, Arg> : TraversingVCExprVisitor<Result, Arg> {
    protected override Result StandardResult(VCExpr node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }
  }
  //////////////////////////////////////////////////////////////////////////////
  // Class to iterate over the nodes of a tree of VCExprNAry. This is
  // used to avoid handling such VCExpr recursively, which can easily
  // lead to stack overflows

  public class VCExprNAryEnumerator : IEnumerator {

    private readonly VCExprNAry/*!*/ CompleteExpr;
    private VCExpr CurrentExpr = null;
    private readonly Stack<VCExpr/*!*/>/*!*/ ExprTodo = new Stack<VCExpr/*!*/>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(CompleteExpr != null);
      Contract.Invariant(cce.NonNullElements(ExprTodo));
    }

    public VCExprNAryEnumerator(VCExprNAry completeExpr) {
      Contract.Requires(completeExpr != null);
      this.CompleteExpr = completeExpr;
      Stack<VCExpr/*!*/>/*!*/ exprTodo = new Stack<VCExpr/*!*/>();
      exprTodo.Push(completeExpr);
      ExprTodo = exprTodo;
    }

    // Method using which a subclass can decide whether the
    // subexpressions of an expression should be enumerated as well
    // The default is to enumerate all nodes
    protected virtual bool Descend(VCExprNAry expr) {
      Contract.Requires(expr != null);
      return true;
    }

    ////////////////////////////////////////////////////////////////////////////

    public bool MoveNext() {
      if (ExprTodo.Count == 0)
        return false;

      CurrentExpr = ExprTodo.Pop();
      VCExprNAry currentNAry = CurrentExpr as VCExprNAry;
      if (currentNAry != null && Descend(currentNAry)) {
        for (int i = currentNAry.Arity - 1; i >= 0; --i)
          ExprTodo.Push(currentNAry[i]);
      }

      return true;
    }

    public object Current {
      get {
        return cce.NonNull(CurrentExpr);
      }
    }

    public void Reset() {
      ExprTodo.Clear();
      CurrentExpr = null;
      ExprTodo.Push(CompleteExpr);
    }
  }


  //////////////////////////////////////////////////////////////////////////////

  public class VCExprNAryUniformOpEnumerator : VCExprNAryEnumerator {
    private readonly VCExprOp/*!*/ Op;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Op != null);
    }

    public VCExprNAryUniformOpEnumerator(VCExprNAry completeExpr)
      : base(completeExpr) {
      Contract.Requires(completeExpr != null);

      this.Op = completeExpr.Op;
    }
    protected override bool Descend(VCExprNAry expr) {
      //Contract.Requires(expr != null);
      return expr.Op.Equals(Op) &&
        // we never skip nodes with type parameters
        // (those are too interesting ...)
             expr.TypeParamArity == 0;
    }
  }

  public class VCExprNAryMultiUniformOpEnumerator : VCExprNAryEnumerator
  {
      private readonly HashSet<VCExprOp> Ops;
      [ContractInvariantMethod]
      void ObjectInvariant()
      {
          Contract.Invariant(Ops != null);
      }

      public VCExprNAryMultiUniformOpEnumerator(VCExprNAry completeExpr, HashSet<VCExprOp> ops)
          : base(completeExpr)
      {
          Contract.Requires(completeExpr != null);

          this.Ops = ops;
      }
      protected override bool Descend(VCExprNAry expr)
      {
          return Ops.Contains(expr.Op) && expr.TypeParamArity == 0;
      }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Visitor that knows about the variables bound at each location in a VCExpr

  public abstract class BoundVarTraversingVCExprVisitor<Result, Arg>
                        : TraversingVCExprVisitor<Result, Arg> {
    // Maps with all variables bound above a certain location in the VCExpression.
    // The value of the map tells how often a particular symbol was bound
    private readonly IDictionary<VCExprVar/*!*/, int>/*!*/ BoundTermVarsDict =
      new Dictionary<VCExprVar/*!*/, int>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundTermVarsDict != null);
      Contract.Invariant(BoundTypeVarsDict != null);
    }

    private readonly IDictionary<TypeVariable/*!*/, int>/*!*/ BoundTypeVarsDict =
      new Dictionary<TypeVariable/*!*/, int>();

    protected ICollection<VCExprVar/*!*/>/*!*/ BoundTermVars {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<ICollection<VCExprVar>>()));
        return BoundTermVarsDict.Keys;
      }
    }
    protected ICollection<TypeVariable/*!*/>/*!*/ BoundTypeVars {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<ICollection<TypeVariable>>()));
        return BoundTypeVarsDict.Keys;
      }
    }

    private void AddBoundVar<T>(IDictionary<T, int> dict, T sym) {
      Contract.Requires(sym != null);
      Contract.Requires(dict != null);
      int n;
      if (dict.TryGetValue(sym, out n))
        dict[sym] = n + 1;
      else
        dict[sym] = 1;
    }

    private void RemoveBoundVar<T>(IDictionary<T/*!*/, int/*!*/>/*!*/ dict, T sym) {
      Contract.Requires(sym != null);
      Contract.Requires(dict != null);
      int n;
      bool b = dict.TryGetValue(sym, out n);
      Contract.Assert(b && n > 0);
      if (n == 1)
        dict.Remove(sym);
      else
        dict[sym] = n - 1;
    }

    public override Result Visit(VCExprQuantifier node, Arg arg) {
      Contract.Requires(node != null);
      // we temporarily add bound (term and type) variables to the
      // corresponding lists
      foreach (VCExprVar/*!*/ v in node.BoundVars) {
        Contract.Assert(v != null);
        AddBoundVar<VCExprVar>(BoundTermVarsDict, v);
      }
      foreach (TypeVariable/*!*/ v in node.TypeParameters) {
        Contract.Assert(v != null);
        AddBoundVar<TypeVariable>(BoundTypeVarsDict, v);
      }

      Result res;
      try {
        res = VisitAfterBinding(node, arg);
      } finally {
        foreach (VCExprVar/*!*/ v in node.BoundVars) {
          Contract.Assert(v != null);
          RemoveBoundVar<VCExprVar>(BoundTermVarsDict, v);
        }
        foreach (TypeVariable/*!*/ v in node.TypeParameters) {
          Contract.Assert(v != null);
          RemoveBoundVar<TypeVariable>(BoundTypeVarsDict, v);
        }
      }
      return res;
    }
    public override Result Visit(VCExprLet node, Arg arg) {
      Contract.Requires(node != null);
      // we temporarily add bound term variables to the
      // corresponding lists
      foreach (VCExprVar/*!*/ v in node.BoundVars) {
        Contract.Assert(v != null);
        AddBoundVar<VCExprVar>(BoundTermVarsDict, v);
      }

      Result res;
      try {
        res = VisitAfterBinding(node, arg);
      } finally {
        foreach (VCExprVar/*!*/ v in node.BoundVars) {
          Contract.Assert(v != null);
          RemoveBoundVar<VCExprVar>(BoundTermVarsDict, v);
        }
      }
      return res;
    }

    ////////////////////////////////////////////////////////////////////////////
    // The possibility is provided to look at a (quantifier or let) node
    // after its bound variables have been registered
    // (when overriding the normal visit-methods, the node will be visited
    // before the binding happens)

    protected virtual Result VisitAfterBinding(VCExprQuantifier node, Arg arg) {
      Contract.Requires(node != null);
      return base.Visit(node, arg);
    }

    protected virtual Result VisitAfterBinding(VCExprLet node, Arg arg) {
      Contract.Requires(node != null);
      return base.Visit(node, arg);
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  // General visitor for recursively collecting information in a VCExpr.
  // As the visitor is not used anywhere for the time being, it maybe should
  // be removed

  [ContractClass(typeof(CollectingVCExprVisitorContracts<,>))]
  public abstract class CollectingVCExprVisitor<Result, Arg>
                        : IVCExprVisitor<Result, Arg> {
    protected abstract Result CombineResults(List<Result>/*!*/ results, Arg arg);

    public Result Collect(VCExpr node, Arg arg) {
      Contract.Requires(node != null);
      return node.Accept(this, arg);
    }

    public virtual Result Visit(VCExprLiteral node, Arg arg) {
      //Contract.Requires(node != null);
      return CombineResults(new List<Result>(), arg);
    }
    public virtual Result Visit(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      List<Result>/*!*/ results = new List<Result>();
      foreach (VCExpr/*!*/ subnode in node) {
        Contract.Assert(subnode != null);
        results.Add(subnode.Accept(this, arg));
      }
      return CombineResults(results, arg);
    }
    public virtual Result Visit(VCExprVar node, Arg arg) {
      //Contract.Requires(node != null);
      return CombineResults(new List<Result>(), arg);
    }
    public virtual Result Visit(VCExprQuantifier node, Arg arg) {
      //Contract.Requires(node != null);
      List<Result>/*!*/ result = new List<Result>();
      result.Add(node.Body.Accept(this, arg));
      foreach (VCTrigger/*!*/ trigger in node.Triggers) {
        Contract.Assert(trigger != null);
        foreach (VCExpr/*!*/ expr in trigger.Exprs) {
          Contract.Assert(expr != null);
          result.Add(expr.Accept(this, arg));
        }
      }
      return CombineResults(result, arg);
    }
    public virtual Result Visit(VCExprLet node, Arg arg) {
      //Contract.Requires(node != null);
      List<Result>/*!*/ results = new List<Result>();
      // visit the bound expressions first
      foreach (VCExprLetBinding/*!*/ binding in node) {
        Contract.Assert(binding != null);
        results.Add(binding.E.Accept(this, arg));
      }
      results.Add(node.Body.Accept(this, arg));
      return CombineResults(results, arg);
    }
  }
  [ContractClassFor(typeof(CollectingVCExprVisitor<,>))]
  public abstract class CollectingVCExprVisitorContracts<Result, Arg> : CollectingVCExprVisitor<Result, Arg> {
    protected override Result CombineResults(List<Result> results, Arg arg) {
      Contract.Requires(results != null);
      throw new NotImplementedException();
    }
  }
  ////////////////////////////////////////////////////////////////////////////

  public class SizeComputingVisitor : TraversingVCExprVisitor<bool, bool> {

    private int Size = 0;

    public static int ComputeSize(VCExpr expr) {
      Contract.Requires(expr != null);
      SizeComputingVisitor/*!*/ visitor = new SizeComputingVisitor();
      visitor.Traverse(expr, true);
      return visitor.Size;
    }

    protected override bool StandardResult(VCExpr node, bool arg) {
      //Contract.Requires(node != null);
      Size = Size + 1;
      return true;
    }
  }

  ////////////////////////////////////////////////////////////////////////////

  // Collect all free term and type variables in a VCExpr. Type variables
  // can occur free either in the types of bound variables, or in the type
  // parameters of VCExprNAry.

  // the result and argument (of type bool) are not used currently
  public class FreeVariableCollector : BoundVarTraversingVCExprVisitor<bool, bool> {
    public readonly Dictionary<VCExprVar/*!*/, object>/*!*/ FreeTermVars = new Dictionary<VCExprVar/*!*/, object>();
    public readonly List<TypeVariable/*!*/>/*!*/ FreeTypeVars = new List<TypeVariable/*!*/>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FreeTermVars != null && Contract.ForAll(FreeTermVars, entry => entry.Key != null));
      Contract.Invariant(cce.NonNullElements(FreeTypeVars));
    }


    // not used
    protected override bool StandardResult(VCExpr node, bool arg) {
      //Contract.Requires(node != null);
      return true;
    }

    public static Dictionary<VCExprVar/*!*/, object>/*!*/ FreeTermVariables(VCExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Dictionary<VCExprVar, object>>() != null);
      Contract.Ensures(Contract.ForAll(Contract.Result<Dictionary<VCExprVar, object>>(), ftv => ftv.Key != null));
      FreeVariableCollector collector = new FreeVariableCollector();
      collector.Traverse(node, true);
      return collector.FreeTermVars;
    }

    public static List<TypeVariable/*!*/>/*!*/ FreeTypeVariables(VCExpr node) {
      Contract.Requires(node != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<TypeVariable>>()));
      FreeVariableCollector collector = new FreeVariableCollector();
      collector.Traverse(node, true);
      return collector.FreeTypeVars;
    }

    public void Reset() {
      FreeTermVars.Clear();
      FreeTypeVars.Clear();
    }

    public void Collect(VCExpr node) {
      Contract.Requires(node != null);
      Traverse(node, true);
    }

    public void Collect(Type type) {
      Contract.Requires(type != null);
      AddTypeVariables(type.FreeVariables.ToList());
    }

    /////////////////////////////////////////////////////////////////////////

    private void CollectTypeVariables(IEnumerable<VCExprVar/*!*/>/*!*/ boundVars) {
      Contract.Requires(cce.NonNullElements(boundVars));
      foreach (VCExprVar/*!*/ var in boundVars) {
        Contract.Assert(var != null);
        Collect(var.Type);
      }
    }

    private void AddTypeVariables(IEnumerable<TypeVariable/*!*/>/*!*/ typeVars) {
      Contract.Requires(cce.NonNullElements(typeVars));
      foreach (TypeVariable/*!*/ tvar in typeVars) {
        Contract.Assert(tvar != null);
        if (!BoundTypeVars.Contains(tvar) && !FreeTypeVars.Contains(tvar))
          FreeTypeVars.Add(tvar);
      }
    }

    public override bool Visit(VCExprVar node, bool arg) {
      Contract.Requires(node != null);
      if (!BoundTermVars.Contains(node) && !FreeTermVars.ContainsKey(node)) {
        FreeTermVars.Add(node, null);
        Collect(node.Type);
      }
      return true;
    }

    public override bool Visit(VCExprNAry node, bool arg) {
      Contract.Requires(node != null);
      foreach (Type/*!*/ t in node.TypeArguments) {
        Contract.Assert(t != null);
        Collect(t);
      }
      return base.Visit(node, arg);
    }

    protected override bool VisitAfterBinding(VCExprQuantifier node, bool arg) {
      //Contract.Requires(node != null);
      CollectTypeVariables(node.BoundVars);
      return base.VisitAfterBinding(node, arg);
    }

    protected override bool VisitAfterBinding(VCExprLet node, bool arg) {
      //Contract.Requires(node != null);
      CollectTypeVariables(node.BoundVars);
      return base.VisitAfterBinding(node, arg);
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  // Framework for mutating VCExprs

  // The Visit implementations in the following visitor work
  // recursively, apart from the implementation for VCExprNAry that
  // uses its own stack when applied to nested nodes with the same
  // operator, e.g., (AND (AND (AND ...) ...) ...). This is necessary
  // to avoid stack overflows (like in TraversingVCExprVisitor)

  public abstract class MutatingVCExprVisitor<Arg>
                        : IVCExprVisitor<VCExpr/*!*/, Arg> {
    protected readonly VCExpressionGenerator/*!*/ Gen;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Gen != null);
    }


    public MutatingVCExprVisitor(VCExpressionGenerator gen) {
      Contract.Requires(gen != null);
      this.Gen = gen;
    }

    public VCExpr Mutate(VCExpr expr, Arg arg) {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return expr.Accept(this, arg);
    }

    public List<VCExpr/*!*/>/*!*/ MutateSeq(IEnumerable<VCExpr/*!*/>/*!*/ exprs, Arg arg) {
      Contract.Requires(cce.NonNullElements(exprs));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExpr>>()));
      List<VCExpr/*!*/>/*!*/ res = new List<VCExpr/*!*/>();
      foreach (VCExpr/*!*/ expr in exprs) {
        Contract.Assert(expr != null);
        res.Add(expr.Accept(this, arg));
      }
      return res;
    }

    private List<VCExpr/*!*/>/*!*/ MutateList(List<VCExpr/*!*/>/*!*/ exprs, Arg arg) {
      Contract.Requires(cce.NonNullElements(exprs));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExpr>>()));
      bool changed = false;
      List<VCExpr/*!*/>/*!*/ res = new List<VCExpr/*!*/>();
      foreach (VCExpr/*!*/ expr in exprs) {
        Contract.Assert(expr != null);
        VCExpr/*!*/ newExpr = expr.Accept(this, arg);
        if (!Object.ReferenceEquals(expr, newExpr))
          changed = true;
        res.Add(newExpr);
      }
      if (!changed)
        return exprs;
      return res;
    }

    public virtual VCExpr Visit(VCExprLiteral node, Arg arg) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return node;
    }

    ////////////////////////////////////////////////////////////////////////////

    // Special element used to mark the positions in the todo-stack where
    // results have to be popped from the result-stack.
    private static readonly VCExpr/*!*/ CombineResultsMarker = new VCExprLiteral(Type.Bool);

    // The todo-stack contains records of the shape
    //
    //     arg0
    //     arg1
    //     arg2
    //     ...
    //     CombineResultsMarker
    //     f(arg0, arg1, arg2, ...)               (the original expression)

    private readonly Stack<VCExpr/*!*/>/*!*/ NAryExprTodoStack = new Stack<VCExpr/*!*/>();
    private readonly Stack<VCExpr/*!*/>/*!*/ NAryExprResultStack = new Stack<VCExpr/*!*/>();
    [ContractInvariantMethod]
    void ObjectInvarianta() {
      Contract.Invariant(cce.NonNullElements(NAryExprResultStack));
      Contract.Invariant(cce.NonNullElements(NAryExprTodoStack));
    }


    private void PushTodo(VCExprNAry exprTodo) {
      Contract.Requires(exprTodo != null);
      NAryExprTodoStack.Push(exprTodo);
      NAryExprTodoStack.Push(CombineResultsMarker);
      for (int i = exprTodo.Arity - 1; i >= 0; --i)
        NAryExprTodoStack.Push(exprTodo[i]);
    }

    public virtual bool AvoidVisit(VCExprNAry node, Arg arg)
    {
        return true;
    }

    public virtual VCExpr Visit(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      int initialStackSize = NAryExprTodoStack.Count;
      int initialResultStackSize = NAryExprResultStack.Count;

      PushTodo(node);

      while (NAryExprTodoStack.Count > initialStackSize) {
        VCExpr/*!*/ subExpr = NAryExprTodoStack.Pop();
        Contract.Assert(subExpr != null);

        if (Object.ReferenceEquals(subExpr, CombineResultsMarker)) {
          // assemble a result
          VCExprNAry/*!*/ originalExpr = (VCExprNAry)NAryExprTodoStack.Pop();
          Contract.Assert(originalExpr != null);
          VCExprOp/*!*/ op = originalExpr.Op;
          bool changed = false;
          List<VCExpr/*!*/>/*!*/ newSubExprs = new List<VCExpr/*!*/>();

          for (int i = op.Arity - 1; i >= 0; --i) {
            VCExpr/*!*/ nextSubExpr = NAryExprResultStack.Pop();
            Contract.Assert(nextSubExpr != null);
            if (!Object.ReferenceEquals(nextSubExpr, originalExpr[i]))
              changed = true;
            newSubExprs.Insert(0, nextSubExpr);
          }

          NAryExprResultStack.Push(UpdateModifiedNode(originalExpr, newSubExprs, changed, arg));
          //
        } else {
          //
            VCExprNAry narySubExpr = subExpr as VCExprNAry;
          if (narySubExpr != null && this.AvoidVisit(narySubExpr, arg) &&
            // as in VCExprNAryUniformOpEnumerator, all expressions with
            // type parameters are allowed to be inspected more closely
              narySubExpr.TypeParamArity == 0) {
            PushTodo(narySubExpr);
          } else {
            NAryExprResultStack.Push(subExpr.Accept(this, arg));
          }
          //
        }
      }

      Contract.Assert(NAryExprTodoStack.Count == initialStackSize && NAryExprResultStack.Count == initialResultStackSize + 1);
      return NAryExprResultStack.Pop();
    }

    protected virtual VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode, List<VCExpr/*!*/>/*!*/ newSubExprs, // has any of the subexpressions changed? 
                                                 bool changed,
                                                 Arg arg) {
      Contract.Requires(cce.NonNullElements(newSubExprs));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      if (changed)
        return Gen.Function(originalNode.Op,
                            newSubExprs, originalNode.TypeArguments);
      else
        return originalNode;
    }

    ////////////////////////////////////////////////////////////////////////////

    public virtual VCExpr Visit(VCExprVar node, Arg arg) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return node;
    }

    protected List<VCTrigger/*!*/>/*!*/ MutateTriggers(List<VCTrigger/*!*/>/*!*/ triggers, Arg arg) {
      Contract.Requires(cce.NonNullElements(triggers));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCTrigger>>()));
      List<VCTrigger/*!*/>/*!*/ newTriggers = new List<VCTrigger/*!*/>();
      bool changed = false;
      foreach (VCTrigger/*!*/ trigger in triggers) {
        Contract.Assert(trigger != null);
        List<VCExpr/*!*/>/*!*/ exprs = trigger.Exprs;
        List<VCExpr/*!*/>/*!*/ newExprs = MutateList(exprs, arg);

        if (Object.ReferenceEquals(exprs, newExprs)) {
          newTriggers.Add(trigger);
        } else {
          newTriggers.Add(Gen.Trigger(trigger.Pos, newExprs));
          changed = true;
        }
      }
      if (!changed)
        return triggers;
      return newTriggers;
    }

    public virtual VCExpr Visit(VCExprQuantifier node, Arg arg) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      bool changed = false;

      VCExpr/*!*/ body = node.Body;
      Contract.Assert(body != null);
      VCExpr/*!*/ newbody = body.Accept(this, arg);
      Contract.Assert(newbody != null);
      if (!Object.ReferenceEquals(body, newbody))
        changed = true;

      // visit the trigger expressions as well
      List<VCTrigger/*!*/>/*!*/ triggers = node.Triggers;
      Contract.Assert(cce.NonNullElements(triggers));
      List<VCTrigger/*!*/>/*!*/ newTriggers = MutateTriggers(triggers, arg);
      Contract.Assert(cce.NonNullElements(newTriggers));
      if (!Object.ReferenceEquals(triggers, newTriggers))
        changed = true;

      if (!changed)
        return node;
      return Gen.Quantify(node.Quan, node.TypeParameters, node.BoundVars,
                          newTriggers, node.Infos, newbody);
    }

    public virtual VCExpr Visit(VCExprLet node, Arg arg) {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      bool changed = false;

      VCExpr/*!*/ body = node.Body;
      VCExpr/*!*/ newbody = body.Accept(this, arg);
      if (!Object.ReferenceEquals(body, newbody))
        changed = true;

      List<VCExprLetBinding/*!*/>/*!*/ newbindings = new List<VCExprLetBinding/*!*/>();
      for (int i = 0; i < node.Length; ++i) {
        VCExprLetBinding/*!*/ binding = node[i];
        Contract.Assert(binding != null);
        VCExpr/*!*/ e = binding.E;
        VCExpr/*!*/ newE = e.Accept(this, arg);
        if (Object.ReferenceEquals(e, newE)) {
          newbindings.Add(binding);
        } else {
          changed = true;
          newbindings.Add(Gen.LetBinding(binding.V, newE));
        }
      }

      if (!changed)
        return node;
      return Gen.Let(newbindings, newbody);
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  // Substitutions and a visitor for applying substitutions. A substitution can
  // substitute both type variables and term variables

  public class VCExprSubstitution {
    private readonly List<IDictionary<VCExprVar/*!*/, VCExpr/*!*/>/*!*/>/*!*/ TermSubsts;
    [ContractInvariantMethod]
    void TermSubstsInvariantMethod() {
      Contract.Invariant(TermSubsts != null && Contract.ForAll(TermSubsts, i => cce.NonNullDictionaryAndValues(i)));
    }
    private readonly List<IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/>/*!*/ TypeSubsts;
    [ContractInvariantMethod]
    void TypeSubstsInvariantMethod() {
      Contract.Invariant(TermSubsts != null && Contract.ForAll(TypeSubsts, i => cce.NonNullDictionaryAndValues(i)));
    }

    public VCExprSubstitution(IDictionary<VCExprVar/*!*/, VCExpr/*!*/>/*!*/ termSubst, IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ typeSubst) {
      Contract.Requires(cce.NonNullDictionaryAndValues(termSubst));
      Contract.Requires(cce.NonNullDictionaryAndValues(typeSubst));
      List<IDictionary<VCExprVar/*!*/, VCExpr/*!*/>/*!*/>/*!*/ termSubsts =
        new List<IDictionary<VCExprVar/*!*/, VCExpr/*!*/>/*!*/>();
      termSubsts.Add(termSubst);
      List<IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/>/*!*/ typeSubsts =
        new List<IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/>();
      typeSubsts.Add(typeSubst);
      this.TermSubsts = termSubsts;
      this.TypeSubsts = typeSubsts;
    }

    public VCExprSubstitution()
      : this(new Dictionary<VCExprVar/*!*/, VCExpr/*!*/>(), new Dictionary<TypeVariable/*!*/, Type/*!*/>()) {

    }

    public void PushScope() {
      TermSubsts.Add(new Dictionary<VCExprVar/*!*/, VCExpr/*!*/>());
      TypeSubsts.Add(new Dictionary<TypeVariable/*!*/, Type/*!*/>());
    }

    public void PopScope() {
      TermSubsts.RemoveAt(TermSubsts.Count - 1);
      TypeSubsts.RemoveAt(TypeSubsts.Count - 1);
    }

    public VCExpr this[VCExprVar/*!*/ var] {
      get {
        Contract.Requires(var != null);
        VCExpr res;
        for (int i = TermSubsts.Count - 1; i >= 0; --i) {
          if (TermSubsts[i].TryGetValue(var, out res))
            return res;
        }
        return null;
      }
      set {
        TermSubsts[TermSubsts.Count - 1][var] = cce.NonNull(value);
      }
    }

    public Type this[TypeVariable/*!*/ var] {
      get {
        Contract.Requires(var != null);
        Type res;
        for (int i = TypeSubsts.Count - 1; i >= 0; --i) {
          if (TypeSubsts[i].TryGetValue(var, out res))
            return res;
        }
        return null;
      }
      set {
        TypeSubsts[TypeSubsts.Count - 1][var] = cce.NonNull(value);
      }
    }

    public bool ContainsKey(VCExprVar var) {
      Contract.Requires(var != null);
      return this[var] != null;
    }

    public bool ContainsKey(TypeVariable var) {
      Contract.Requires(var != null);
      return this[var] != null;
    }

    public bool TermSubstIsEmpty {
      get {
        return TermSubsts.All(dict => !dict.Any());
      }
    }

    public bool TypeSubstIsEmpty {
      get {
        return TypeSubsts.All(dict => !dict.Any());
      }
    }

    public IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ ToTypeSubst {
      get {
        Contract.Ensures(cce.NonNullDictionaryAndValues(Contract.Result<IDictionary<TypeVariable, Type>>()));
        IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ res = new Dictionary<TypeVariable/*!*/, Type/*!*/>();
        foreach (IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ dict in TypeSubsts) {
          foreach (KeyValuePair<TypeVariable/*!*/, Type/*!*/> pair in dict) {
            Contract.Assert(cce.NonNullElements(pair));
            // later ones overwrite earlier ones
            res[pair.Key] = pair.Value;
          }
        }
        return res;
      }
    }

    // the variables that are not mapped to themselves
    public IEnumerable<VCExprVar/*!*/>/*!*/ TermDomain {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<VCExprVar>>()));
        HashSet<VCExprVar/*!*/>/*!*/ domain = new HashSet<VCExprVar/*!*/>();
        foreach (IDictionary<VCExprVar/*!*/, VCExpr/*!*/>/*!*/ dict in TermSubsts) {
          Contract.Assert(dict != null);
          foreach (VCExprVar/*!*/ var in dict.Keys) {
            Contract.Assert(var != null);
            if (!var.Equals(this[var]))
              domain.Add(var);
          }
        }
        return domain;
      }
    }

    // the variables that are not mapped to themselves
    public IEnumerable<TypeVariable/*!*/>/*!*/ TypeDomain {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<TypeVariable>>()));
        HashSet<TypeVariable/*!*/>/*!*/ domain = new HashSet<TypeVariable/*!*/>();
        foreach (IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ dict in TypeSubsts) {
          Contract.Assert(dict != null);
          foreach (TypeVariable/*!*/ var in dict.Keys) {
            Contract.Assert(var != null);
            if (!var.Equals(this[var]))
              domain.Add(var);
          }
        }
        return domain;
      }
    }

    public FreeVariableCollector/*!*/ Codomains {
      get {
        Contract.Ensures(Contract.Result<FreeVariableCollector>() != null);

        FreeVariableCollector/*!*/ coll = new FreeVariableCollector();
        foreach (VCExprVar/*!*/ var in TermDomain)
          coll.Collect(cce.NonNull(this)[var]);
        foreach (TypeVariable/*!*/ var in TypeDomain)
          coll.Collect(cce.NonNull(this)[var]);
        return coll;
      }
    }

    public VCExprSubstitution Clone() {
      Contract.Ensures(Contract.Result<VCExprSubstitution>() != null);
      VCExprSubstitution/*!*/ res = new VCExprSubstitution();
      foreach (IDictionary<VCExprVar/*!*/, VCExpr/*!*/>/*!*/ dict in TermSubsts)
        res.TermSubsts.Add(HelperFuns.Clone(dict));
      foreach (IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ dict in TypeSubsts)
        res.TypeSubsts.Add(HelperFuns.Clone(dict));
      return res;
    }
  }

  /////////////////////////////////////////////////////////////////////////////////

  public class SubstitutingVCExprVisitor
               : MutatingVCExprVisitor<VCExprSubstitution/*!*/> {
    public SubstitutingVCExprVisitor(VCExpressionGenerator gen)
      : base(gen) {
      Contract.Requires(gen != null);

    }

    // when descending across a binder, we have to check that no collisions
    // or variable capture can occur. if this might happen, we replace the
    // term and type variables bound by the binder with fresh variables
    private bool CollisionPossible(IEnumerable<TypeVariable/*!*/>/*!*/ typeParams, IEnumerable<VCExprVar/*!*/>/*!*/ boundVars, VCExprSubstitution/*!*/ substitution) {
      Contract.Requires(cce.NonNullElements(typeParams));
      Contract.Requires(cce.NonNullElements(boundVars));
      Contract.Requires(substitution != null);
      // variables can be shadowed by a binder
      if (typeParams.Any(var => substitution.ContainsKey(var)) ||
          boundVars.Any(var => substitution.ContainsKey(var)))
        return true;
      // compute the codomain of the substitution
      FreeVariableCollector coll = substitution.Codomains;
      Contract.Assert(coll != null);
      // variables could be captured when applying the substitution
      return typeParams.Any(var => coll.FreeTypeVars.Contains(var)) ||
             boundVars.Any(var => coll.FreeTermVars.ContainsKey(var));
    }

    // can be overwritten if names of bound variables are to be changed
    protected virtual string ChooseNewVariableName(string oldName) {
      Contract.Requires(oldName != null);
      Contract.Ensures(Contract.Result<string>() != null);
      return oldName;
    }

    // handle type parameters in VCExprNAry
    protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode, List<VCExpr/*!*/>/*!*/ newSubExprs, bool changed, VCExprSubstitution/*!*/ substitution) {
      //Contract.Requires(originalNode != null);
      //Contract.Requires(cce.NonNullElements(newSubExprs));
      //Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      List<Type/*!*/>/*!*/ typeParams = new List<Type/*!*/>();
      foreach (Type/*!*/ t in originalNode.TypeArguments) {
        Contract.Assert(t != null);
        Type/*!*/ newType = t.Substitute(substitution.ToTypeSubst);
        Contract.Assert(newType != null);
        if (!ReferenceEquals(t, newType))
          changed = true;
        typeParams.Add(newType);
      }
      if (changed)
        return Gen.Function(originalNode.Op, newSubExprs, typeParams);
      else
        return originalNode;
    }

    public override VCExpr/*!*/ Visit(VCExprQuantifier/*!*/ node, VCExprSubstitution/*!*/ substitution) {
      Contract.Requires(node != null);
      Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      // the default is to refresh bound variables only if necessary
      // because of collisions
      return Visit(node, substitution, false);
    }

    public VCExpr/*!*/ Visit(VCExprQuantifier/*!*/ node, VCExprSubstitution/*!*/ substitution, bool refreshBoundVariables) {
      Contract.Requires(node != null);
      Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      substitution.PushScope();
      try {

        List<TypeVariable/*!*/>/*!*/ typeParams = node.TypeParameters;
        Contract.Assert(cce.NonNullElements(typeParams));
        bool refreshAllVariables = refreshBoundVariables ||
                                   CollisionPossible(node.TypeParameters, node.BoundVars, substitution);
        if (refreshAllVariables) {
          // we introduce fresh type variables to ensure that none gets captured
          typeParams = new List<TypeVariable/*!*/>();
          foreach (TypeVariable/*!*/ var in node.TypeParameters) {
            Contract.Assert(var != null);
            TypeVariable/*!*/ freshVar =
              new TypeVariable(Token.NoToken, ChooseNewVariableName(var.Name));
            Contract.Assert(freshVar != null);
            typeParams.Add(freshVar);
            substitution[var] = freshVar;
            // this might overwrite other elements of the substitution, deliberately
          }
        }

        List<VCExprVar/*!*/>/*!*/ boundVars = node.BoundVars;
        Contract.Assert(cce.NonNullElements(boundVars));
        if (refreshAllVariables || !substitution.TypeSubstIsEmpty) {
          // collisions are possible, or we also substitute type variables. in this case
          // the bound term variables have to be replaced with fresh variables with the
          // right types
          boundVars = new List<VCExprVar/*!*/>();
          IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ typeSubst = substitution.ToTypeSubst;
          Contract.Assert(cce.NonNullDictionaryAndValues(typeSubst));
          foreach (VCExprVar/*!*/ var in node.BoundVars) {
            Contract.Assert(var != null);
            VCExprVar/*!*/ freshVar =
              Gen.Variable(ChooseNewVariableName(var.Name),
                           var.Type.Substitute(typeSubst));
            Contract.Assert(freshVar != null);
            boundVars.Add(freshVar);
            substitution[var] = freshVar;
            // this might overwrite other elements of the substitution, deliberately
          }
        }

        List<VCTrigger/*!*/>/*!*/ newTriggers = new List<VCTrigger/*!*/>();
        foreach (VCTrigger/*!*/ trigger in node.Triggers) {
          Contract.Assert(trigger != null);
          newTriggers.Add(Gen.Trigger(trigger.Pos, MutateSeq(trigger.Exprs, substitution)));
        }

        VCExpr/*!*/ newBody = Mutate(node.Body, substitution);
        Contract.Assert(newBody != null);

        return Gen.Quantify(node.Quan, typeParams, boundVars,
                            newTriggers, node.Infos, newBody);

      } finally {
        substitution.PopScope();
      }
    }

    public override VCExpr Visit(VCExprVar node, VCExprSubstitution substitution) {
      Contract.Requires(substitution != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr res = substitution[node];
      if (res != null)
        return res;
      return node;
    }

    public override VCExpr Visit(VCExprLet node, VCExprSubstitution substitution) {
      Contract.Requires(substitution != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      // the default is to refresh bound variables only if necessary
      // because of collisions
      return Visit(node, substitution, false);
    }

    public VCExpr Visit(VCExprLet node, VCExprSubstitution substitution, bool refreshBoundVariables) {
      Contract.Requires(substitution != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      // let-expressions do not have type parameters (fortunately ...)
      substitution.PushScope();
      try {

        bool refreshAllVariables =
          refreshBoundVariables ||
          !substitution.TypeSubstIsEmpty ||
          CollisionPossible(new List<TypeVariable/*!*/>(), node.BoundVars, substitution);

        List<VCExprVar/*!*/>/*!*/ newBoundVars = node.BoundVars;
        Contract.Assert(cce.NonNullElements(newBoundVars));
        if (refreshAllVariables) {
          // collisions are possible, or we also substitute type variables. in this case
          // the bound term variables have to be replaced with fresh variables with the
          // right types
          newBoundVars = new List<VCExprVar/*!*/>();
          IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ typeSubst = substitution.ToTypeSubst;
          Contract.Assert(cce.NonNullDictionaryAndValues(typeSubst));
          foreach (VCExprVar/*!*/ var in node.BoundVars) {
            Contract.Assert(var != null);
            VCExprVar/*!*/ freshVar =
              Gen.Variable(ChooseNewVariableName(var.Name),
                           var.Type.Substitute(typeSubst));
            Contract.Assert(freshVar != null);
            newBoundVars.Add(freshVar);
            substitution[var] = freshVar;
            // this might overwrite other elements of the substitution, deliberately
          }
        }

        List<VCExprLetBinding/*!*/>/*!*/ newbindings = new List<VCExprLetBinding/*!*/>();
        for (int i = 0; i < node.Length; ++i) {
          VCExprLetBinding/*!*/ binding = node[i];
          Contract.Assert(binding != null);
          newbindings.Add(Gen.LetBinding(newBoundVars[i], Mutate(binding.E, substitution)));
        }

        VCExpr/*!*/ newBody = Mutate(node.Body, substitution);
        Contract.Assert(newBody != null);
        return Gen.Let(newbindings, newBody);

      } finally {
        substitution.PopScope();
      }
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  [ContractClassFor(typeof(StandardVCExprOpVisitor<,>))]
  public abstract class StandardVCExprOpVisitorContracts<Result, Arg> : StandardVCExprOpVisitor<Result, Arg> {
    protected override Result StandardResult(VCExprNAry node, Arg arg) {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }
  }


  [ContractClass(typeof(StandardVCExprOpVisitorContracts<,>))]
  public abstract class StandardVCExprOpVisitor<Result, Arg>
                        : IVCExprOpVisitor<Result, Arg> {
    protected abstract Result StandardResult(VCExprNAry/*!*/ node, Arg arg);

    public virtual Result VisitNotOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitEqOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitNeqOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitAndOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitOrOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitImpliesOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitDistinctOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitLabelOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitSelectOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitStoreOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatAddOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatSubOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatMulOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatDivOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatLeqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatLtOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatGeqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatGtOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatEqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitFloatNeqOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitBvOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitBvExtractOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitBvConcatOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitIfThenElseOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitCustomOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitAddOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitSubOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitMulOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitDivOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitModOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitRealDivOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitPowOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitLtOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitLeOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitGtOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitGeOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitSubtypeOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitSubtype3Op(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitToIntOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitToRealOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitToFloatOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    public virtual Result VisitBoogieFunctionOp(VCExprNAry node, Arg arg) {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
  }

}