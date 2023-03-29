using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST;

public abstract class MutatingVCExprVisitor<Arg> : IVCExprVisitor<VCExpr /*!*/, Arg> {
  protected readonly VCExpressionGenerator /*!*/
    Gen;

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
    return expr.Accept(this, arg).Result;
  }

  public async DynamicStack<List<VCExpr /*!*/>> /*!*/ MutateSeq(IEnumerable<VCExpr /*!*/> /*!*/ exprs, Arg arg) {
    Contract.Requires(cce.NonNullElements(exprs));
    Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExpr>>()));
    List<VCExpr /*!*/> /*!*/ res = new List<VCExpr /*!*/>();
    foreach (VCExpr /*!*/ expr in exprs) {
      Contract.Assert(expr != null);
      res.Add(await expr.Accept(this, arg));
    }

    return res;
  }

  private async DynamicStack<List<VCExpr /*!*/>> /*!*/ MutateList(List<VCExpr /*!*/> /*!*/ exprs, Arg arg) {
    Contract.Requires(cce.NonNullElements(exprs));
    Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExpr>>()));
    bool changed = false;
    List<VCExpr /*!*/> /*!*/
      res = new List<VCExpr /*!*/>();
    foreach (VCExpr /*!*/ expr in exprs) {
      Contract.Assert(expr != null);
      var /*!*/ newExpr = await expr.Accept(this, arg);
      if (!ReferenceEquals(expr, newExpr)) {
        changed = true;
      }

      res.Add(newExpr);
    }

    if (!changed) {
      return exprs;
    }

    return res;
  }

  public virtual VCExpr Visit(VCExprLiteral node, Arg arg) {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return node;
  }

  ////////////////////////////////////////////////////////////////////////////

  public virtual async DynamicStack<VCExpr> Visit(VCExprNAry node, Arg arg) {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    bool changed = false;
    var children = new List<VCExpr>();
    for (int i = node.Arity - 1; i >= 0; --i) {
      var child = await node[i].Accept(this, arg);
      if (!Object.ReferenceEquals(child, node[i])) {
        changed = true;
      }
      children.Insert(0, child);
    }

    return UpdateModifiedNode(node, children, changed, arg);
  }

  protected virtual VCExpr /*!*/ UpdateModifiedNode(VCExprNAry /*!*/ originalNode,
    List<VCExpr /*!*/> /*!*/ newSubExprs, // has any of the subexpressions changed? 
    bool changed,
    Arg arg) {
    Contract.Requires(cce.NonNullElements(newSubExprs));
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    if (changed) {
      return Gen.Function(originalNode.Op,
        newSubExprs, originalNode.TypeArguments);
    } else {
      return originalNode;
    }
  }

  ////////////////////////////////////////////////////////////////////////////

  public virtual VCExpr Visit(VCExprVar node, Arg arg) {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return node;
  }

  protected async DynamicStack<List<VCTrigger /*!*/>> /*!*/ MutateTriggers(List<VCTrigger /*!*/> /*!*/ triggers, Arg arg) {
    Contract.Requires(cce.NonNullElements(triggers));
    Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCTrigger>>()));
    List<VCTrigger /*!*/> /*!*/ newTriggers = new List<VCTrigger /*!*/>();
    bool changed = false;
    foreach (VCTrigger /*!*/ trigger in triggers) {
      Contract.Assert(trigger != null);
      List<VCExpr /*!*/> /*!*/ exprs = trigger.Exprs;
      List<VCExpr /*!*/> /*!*/ newExprs = await MutateList(exprs, arg);

      if (Object.ReferenceEquals(exprs, newExprs)) {
        newTriggers.Add(trigger);
      } else {
        newTriggers.Add(Gen.Trigger(trigger.Pos, newExprs));
        changed = true;
      }
    }

    if (!changed) {
      return triggers;
    }

    return newTriggers;
  }

  public virtual async DynamicStack<VCExpr> Visit(VCExprQuantifier node, Arg arg) {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    bool changed = false;

    VCExpr /*!*/ body = node.Body;
    Contract.Assert(body != null);
    VCExpr /*!*/ newbody = await body.Accept(this, arg);
    Contract.Assert(newbody != null);
    if (!ReferenceEquals(body, newbody)) {
      changed = true;
    }

    // visit the trigger expressions as well
    List<VCTrigger /*!*/> /*!*/
      triggers = node.Triggers;
    Contract.Assert(cce.NonNullElements(triggers));
    List<VCTrigger /*!*/> /*!*/ newTriggers = await MutateTriggers(triggers, arg);
    Contract.Assert(cce.NonNullElements(newTriggers));
    if (!ReferenceEquals(triggers, newTriggers)) {
      changed = true;
    }

    if (!changed) {
      return node;
    }

    return Gen.Quantify(node.Quan, node.TypeParameters, node.BoundVars,
      newTriggers, node.Info, newbody);
  }

  public virtual async DynamicStack<VCExpr> Visit(VCExprLet node, Arg arg) {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    bool changed = false;

    VCExpr /*!*/ body = node.Body;
    VCExpr /*!*/ newbody = await body.Accept(this, arg);
    if (!ReferenceEquals(body, newbody)) {
      changed = true;
    }

    List<VCExprLetBinding /*!*/> /*!*/ newbindings = new List<VCExprLetBinding /*!*/>();
    for (int i = 0; i < node.Length; ++i) {
      VCExprLetBinding /*!*/ binding = node[i];
      Contract.Assert(binding != null);
      VCExpr /*!*/ e = binding.E;
      var /*!*/ newE = await e.Accept(this, arg);
      if (ReferenceEquals(e, newE)) {
        newbindings.Add(binding);
      } else {
        changed = true;
        newbindings.Add(Gen.LetBinding(binding.V, newE));
      }
    }

    if (!changed) {
      return node;
    }

    return Gen.Let(newbindings, newbody);
  }
}