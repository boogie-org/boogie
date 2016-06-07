//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Linq;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

// Ensure that no formulas (expressions of type boolean that are not
// just a variable) occur with terms (expressions of some other
// type). This is done by introducing let-binders for boolean
// variables.

namespace Microsoft.Boogie.VCExprAST
{

  public struct FlattenerState {
    public readonly int Polarity;
    public readonly bool InTerm;

    public static FlattenerState INITIAL = new FlattenerState(1, false);

    public FlattenerState(int polarity, bool inTerm) {
      Polarity = polarity;
      InTerm = inTerm;
    }

    public FlattenerState TogglePolarity { get {
      return new FlattenerState(-Polarity, InTerm);
    } }

    public FlattenerState ZeroPolarity { get {
      return new FlattenerState(0, InTerm);
    } }

    public FlattenerState EnterTerm { get {
      return new FlattenerState(Polarity, true);
    } }
  }

  //////////////////////////////////////////////////////////////////////////////

  public class TermFormulaFlattener : MutatingVCExprVisitor<FlattenerState> {

    public TermFormulaFlattener(VCExpressionGenerator gen):base(gen){
Contract.Requires(gen != null);
      
    }

    private readonly IDictionary<VCExpr/*!*/, VCExprVar/*!*/>/*!*/ Bindings =
      new Dictionary<VCExpr/*!*/, VCExprVar/*!*/> ();
    
    private int varNameCounter = 0;

    public VCExpr Flatten(VCExpr expr){
Contract.Requires(expr != null);
Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr/*!*/ res = Mutate(expr, FlattenerState.INITIAL);
      Contract.Assert(res != null);
      while (Bindings.Count > 0) {
        List<VCExprLetBinding/*!*/>/*!*/ letBindings = new List<VCExprLetBinding/*!*/> ();
        foreach (KeyValuePair<VCExpr/*!*/, VCExprVar/*!*/> pair in Bindings){Contract.Assert(cce.NonNullElements(pair));
          letBindings.Add(Gen.LetBinding(pair.Value, pair.Key));}
        Bindings.Clear();
        res = AddBindings(letBindings, res, FlattenerState.INITIAL);
      }
      return res;
    }

    private VCExprVar GetVarFor(VCExpr expr){
Contract.Requires(expr != null);
Contract.Requires((expr.Type.IsBool));
Contract.Ensures(Contract.Result<VCExprVar>() != null);
      VCExprVar res;
      if (!Bindings.TryGetValue(expr, out res)) {
        string name = "flt" + varNameCounter;
        varNameCounter = varNameCounter + 1;
        res = Gen.Variable(name, Type.Bool);
        Bindings.Add(expr, res);
      }
      return cce.NonNull(res);
    }

    // Remove all let-bindings from the field bindings whose rhs
    // contains any of the specified variables
    private List<VCExprLetBinding/*!*/>/*!*/ RemoveBindingsWithVars(List<VCExprVar/*!*/>/*!*/ boundVars, List<TypeVariable/*!*/>/*!*/ boundTypeVars){
Contract.Requires(cce.NonNullElements(boundTypeVars));
Contract.Requires(cce.NonNullElements(boundVars));
Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprLetBinding>>()));      
      List<VCExprLetBinding/*!*/>/*!*/ res = new List<VCExprLetBinding/*!*/> ();
      FreeVariableCollector/*!*/ coll = new FreeVariableCollector ();

      foreach (KeyValuePair<VCExpr, VCExprVar> pair in Bindings) {
        Contract.Assert(cce.NonNullElements(pair));
        coll.Collect(pair.Key);
        if (boundVars.Any(var => coll.FreeTermVars.ContainsKey(var)) ||
            boundTypeVars.Any(var => coll.FreeTypeVars.Contains(var)))
          res.Add(Gen.LetBinding(pair.Value, pair.Key));
        coll.Reset();
      }

      foreach (VCExprLetBinding b in res){Contract.Assert(b != null);
        Bindings.Remove(b.E);}

      return res;
    }
    
    // Add bindings to a formula using an implication or
    // conjunction. The bindings themselves will be flattened as well,
    // which might introduce further bindings
    private VCExpr AddBindings(List<VCExprLetBinding/*!*/>/*!*/ bindings, VCExpr body, FlattenerState state){
Contract.Requires(body != null);
Contract.Requires(cce.NonNullElements(bindings));
Contract.Requires((body.Type.IsBool));
Contract.Ensures(Contract.Result<VCExpr>() != null);

      List<VCExprLetBinding/*!*/>/*!*/ mutatedBindings = FlattenBindings(bindings, state);
      Contract.Assert(mutatedBindings != null);
      VCExpr/*!*/ bindingEquations = Gen.AsEquations(mutatedBindings);
      Contract.Assert(bindingEquations != null);
      switch(state.Polarity) {
      case 1:
        return Gen.Implies(bindingEquations, body);
      case -1:
        return Gen.And(bindingEquations, body);
      case 0:
        // also add explicit quantifiers for the bound variables
        List<VCExprVar/*!*/>/*!*/ vars = new List<VCExprVar/*!*/> ();
        foreach (VCExprLetBinding/*!*/ binding in mutatedBindings){Contract.Assert(binding != null);
          vars.Add(binding.V);}
        return Gen.Forall(vars, new List<VCTrigger/*!*/>(),
                          Gen.Implies(bindingEquations, body));
      }
      Contract.Assert(false); throw new cce.UnreachableException();
    }

    private List<VCExprLetBinding/*!*/>/*!*/ FlattenBindings(List<VCExprLetBinding/*!*/>/*!*/ bindings, FlattenerState state){
Contract.Requires(cce.NonNullElements(bindings));
Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprLetBinding>>()));
      FlattenerState stateInBindings = state.ZeroPolarity;
      List<VCExprLetBinding/*!*/>/*!*/ mutatedBindings = new List<VCExprLetBinding/*!*/> ();
      foreach (VCExprLetBinding/*!*/ b in bindings) {
        Contract.Assert(b != null);
        mutatedBindings.Add(Gen.LetBinding(b.V, Mutate(b.E, stateInBindings)));
      }
      return mutatedBindings;
    }

    ////////////////////////////////////////////////////////////////////////////

    public override bool AvoidVisit(VCExprNAry node, FlattenerState arg)
    {
        return node.Op.Equals(VCExpressionGenerator.AndOp) ||
               node.Op.Equals(VCExpressionGenerator.OrOp);
    }

    public override VCExpr Visit(VCExprNAry node, FlattenerState state){
Contract.Requires(node != null);
Contract.Ensures(Contract.Result<VCExpr>() != null);
      // track the polarity to know whether implications or conjunctions
      // are to be introduced

      if (node.Op.Equals(VCExpressionGenerator.NotOp))
        return Gen.Not(Mutate(node[0], state.TogglePolarity));

      if (node.Op.Equals(VCExpressionGenerator.ImpliesOp)) {
        VCExpr newArg0 = Mutate(node[0], state.TogglePolarity);
        VCExpr newArg1 = Mutate(node[1], state);
        return Gen.Implies(newArg0, newArg1);
      }

      if (!node.Type.IsBool)
        state = state.EnterTerm;

      if (!node.Op.Equals(VCExpressionGenerator.AndOp) &&
          !node.Op.Equals(VCExpressionGenerator.OrOp) &&
          !(node.Op is VCExprLabelOp))
        // standard is to set the polarity to 0 (fits most operators)
        return base.Visit(node, state.ZeroPolarity);

      return base.Visit(node, state);
    }

    public override VCExpr Visit(VCExprQuantifier node, FlattenerState state){
Contract.Requires(node != null);
Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (state.InTerm)
        return GetVarFor(node);

      // we only flatten within the matrix of the quantified formula,
      // not within the triggers (since SMT-solvers do not seem to
      // appreciate triggers with let-binders)
      VCExpr newBody = Mutate(node.Body, state);

      // Check whether any of the extracted terms contain variables
      // bound by this quantifier. In this case, we have to add
      // let-binders and remove the extracted terms
      bool cont = true;
      while (cont) {
        List<VCExprLetBinding/*!*/>/*!*/ localBindings =
          RemoveBindingsWithVars(node.BoundVars, node.TypeParameters);
        Contract.Assert(cce.NonNullElements(localBindings));
        if (localBindings.Count > 0)
          newBody = AddBindings(localBindings, newBody, state);
        else
          cont = false;
      }

      return Gen.Quantify(node.Quan, node.TypeParameters, node.BoundVars, node.Triggers, node.Infos, newBody);
    }

    public override VCExpr Visit(VCExprLet node, FlattenerState state){
Contract.Requires(node != null);
Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (state.InTerm)
        return GetVarFor(node);

      VCExprLet prelimRes = (VCExprLet)cce.NonNull(base.Visit(node, state));

      List<VCExprLetBinding/*!*/>/*!*/ allBindings = new List<VCExprLetBinding/*!*/> ();
      allBindings.AddRange(prelimRes);

      // Check whether any of the extracted terms contain variables
      // bound by this binder. In this case, we have to add
      // let-binders and remove the extracted terms
      bool cont = true;
      while (cont) {
        List<VCExprLetBinding/*!*/>/*!*/ localBindings =
          RemoveBindingsWithVars(prelimRes.BoundVars, new List<TypeVariable/*!*/>());
        if (localBindings.Count > 0)
          allBindings.AddRange(FlattenBindings(localBindings, state));
        else
          cont = false;
      }
      
      return Gen.Let(allBindings, prelimRes.Body);
    }

  }

}