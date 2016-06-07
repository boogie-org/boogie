//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using System.Linq;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

// Class for constructing and collecting the axioms of the partial
// order <:. The class also manages "unique" attributes of constants
// and generated the necessary assumptions for the theorem prover.

// TODO: there should be an interface so that different ways to handle
// ordering relations can be accessed uniformly

namespace Microsoft.Boogie {

  public class OrderingAxiomBuilder {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Gen != null);
      Contract.Invariant(Translator != null);
      Contract.Invariant(cce.NonNullDictionaryAndValues(OneStepFuns));
      Contract.Invariant(cce.NonNullElements(Constants));
      Contract.Invariant(cce.NonNullElements(CompleteConstantsOpen));
      Contract.Invariant(cce.NonNullElements(AllAxioms));
      Contract.Invariant(cce.NonNullElements(IncAxioms));
    }


    private readonly VCExpressionGenerator Gen;
    private readonly Boogie2VCExprTranslator Translator;
    private readonly IDictionary<Type, Function> OneStepFuns;
    private readonly List<Constant> Constants = new List<Constant>();

    // A list to handle constants whose direct children are fully
    // specified (the "complete" keyword). Constants are removed from
    // the list as soon as the corresponding axiom has been generated,
    // which means that from this point on no further children can be
    // added
    private readonly List<Constant> CompleteConstantsOpen = new List<Constant>();

    // list in which all axioms are collected
    private readonly List<VCExpr> AllAxioms = new List<VCExpr>();

    // list in which axioms are incrementally collected
    private readonly List<VCExpr> IncAxioms = new List<VCExpr>();


    public OrderingAxiomBuilder(VCExpressionGenerator gen,
                                Boogie2VCExprTranslator translator) {
      Contract.Requires(gen != null);
      Contract.Requires(translator != null);
      this.Gen = gen;
      this.Translator = translator;
      OneStepFuns = new Dictionary<Type, Function>();
      Constants = new List<Constant>();
      CompleteConstantsOpen = new List<Constant>();
      AllAxioms = new List<VCExpr>();
      IncAxioms = new List<VCExpr>();
    }

    public OrderingAxiomBuilder(VCExpressionGenerator gen,
                                Boogie2VCExprTranslator translator,
                                OrderingAxiomBuilder builder) {
      Contract.Requires(gen != null);
      Contract.Requires(translator != null);
      Contract.Requires(builder != null);
      this.Gen = gen;
      this.Translator = translator;
      OneStepFuns = new Dictionary<Type, Function>(builder.OneStepFuns);
      Constants = new List<Constant>(builder.Constants);
      CompleteConstantsOpen = new List<Constant>(builder.CompleteConstantsOpen);
      AllAxioms = new List<VCExpr>(builder.AllAxioms);
      IncAxioms = new List<VCExpr>(builder.IncAxioms);
    }

    ////////////////////////////////////////////////////////////////////////////

    // Used to axiomatise the disjoint-sub-dag specs that are
    // described by parents with the "unique" flag


    private Function OneStepFunFor(Type t) {
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<Function>() != null);

      Function res;
      if (!OneStepFuns.TryGetValue(t, out res)) {
        List<Variable> args = new List<Variable>();
        args.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "arg0", t), true));
        args.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "arg1", t), true));
        Formal result = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "res", t), false);
        res = new Function(Token.NoToken, "oneStep", new List<TypeVariable>(), args, result);
        OneStepFuns.Add(t, res);
      }
      return cce.NonNull(res);
    }

    ////////////////////////////////////////////////////////////////////////////


    private void AddAxiom(VCExpr axiom) {
      Contract.Requires(axiom != null);
      if (axiom.Equals(VCExpressionGenerator.True))
        return;
      AllAxioms.Add(axiom);
      IncAxioms.Add(axiom);
    }

    // Return all axioms that were added since the last time NewAxioms
    // was called
    public VCExpr GetNewAxioms() {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      CloseChildrenCompleteConstants();
      VCExpr res = Gen.NAry(VCExpressionGenerator.AndOp, IncAxioms);
      IncAxioms.Clear();
      return res;
    }

    // return all axioms
    public VCExpr Axioms {
      get {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        CloseChildrenCompleteConstants();
        return Gen.NAry(VCExpressionGenerator.AndOp, AllAxioms);
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    // Generate the normal axioms for a partial order relation
    public void Setup() {
      TypeVariable alpha = new TypeVariable(Token.NoToken, "alpha");
      Contract.Assert(alpha != null);
      List<TypeVariable> typeParams = new List<TypeVariable>();
      typeParams.Add(alpha);

      List<VCTrigger> triggers = new List<VCTrigger>();

      VCExprVar x = Gen.Variable("x", alpha);
      Contract.Assert(x != null);
      VCExprVar y = Gen.Variable("y", alpha);
      Contract.Assert(y != null);
      VCExprVar z = Gen.Variable("z", alpha);
      Contract.Assert(z != null);

      List<VCExprVar> boundVars = new List<VCExprVar>();

      // reflexivity
      boundVars.Add(x);
      AddAxiom(Gen.Forall(typeParams, boundVars, triggers,
                          new VCQuantifierInfos("bg:subtype-refl", -1, false, null),
                          Gen.AtMost(x, x)));

      // transitivity
      boundVars = new List<VCExprVar>();
      boundVars.Add(x);
      boundVars.Add(y);
      boundVars.Add(z);
      triggers = new List<VCTrigger>();
      triggers.Add(Gen.Trigger(true, Gen.AtMost(x, y), Gen.AtMost(y, z)));
      VCExpr body = Gen.Implies(Gen.And(Gen.AtMost(x, y), Gen.AtMost(y, z)),
                                 Gen.AtMost(x, z));
      Contract.Assert(body != null);
      AddAxiom(Gen.Forall(typeParams, boundVars, triggers,
                          new VCQuantifierInfos("bg:subtype-trans", -1, false, null),
                          body));

      // anti-symmetry
      boundVars = new List<VCExprVar>();
      boundVars.Add(x);
      boundVars.Add(y);
      triggers = new List<VCTrigger>();
      triggers.Add(Gen.Trigger(true, Gen.AtMost(x, y), Gen.AtMost(y, x)));
      body = Gen.Implies(Gen.And(Gen.AtMost(x, y), Gen.AtMost(y, x)),
                         Gen.Eq(x, y));
      AddAxiom(Gen.Forall(typeParams, boundVars, triggers,
                          new VCQuantifierInfos("bg:subtype-antisymm", -1, false, null),
                          body));
    }

    ////////////////////////////////////////////////////////////////////////////

    public void AddConstant(Constant c) {
      Contract.Requires(c != null);
      AddAxiom(GenParentConstraints(c));
      Constants.Add(c);
      if (c.ChildrenComplete)
        CompleteConstantsOpen.Add(c);

      // ensure that no further children are added to closed
      // children-complete constants
      Contract.Assert(!(c.Parents != null && Contract.Exists(c.Parents, p => cce.NonNull((Constant)p.Parent.Decl).ChildrenComplete && !CompleteConstantsOpen.Contains((Constant)p.Parent.Decl))));
    }

    // Generate the constraints telling that parents of a constant are
    // strictly greater than the constant itself, and are the minimal
    // elements with this property
    private VCExpr GenParentConstraints(Constant c) {
      Contract.Requires(c != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      VCExpr res = VCExpressionGenerator.True;

      if (c.Parents == null)
        return res;

      VCExprVar cAsVar = Translator.LookupVariable(c);
      VCExprVar w = Gen.Variable("w", c.TypedIdent.Type);

      // Parents of c are proper ancestors of c
      foreach (ConstantParent p in c.Parents) {
        Contract.Assert(p != null);
        VCExprVar par = Translator.LookupVariable(cce.NonNull(p.Parent.Decl));
        res = Gen.AndSimp(res, Gen.Neq(cAsVar, par));
        res = Gen.AndSimp(res, Gen.AtMost(cAsVar, par));
      }

      // Parents are direct ancestors of c (no other elements are in
      // between c and a parent)
      foreach (ConstantParent p in c.Parents) {
        Contract.Assert(p != null);
        VCExprVar par = Translator.LookupVariable(cce.NonNull(p.Parent.Decl));
        Contract.Assert(par != null);
        VCExpr antecedent1 = Gen.AtMost(cAsVar, w);
        Contract.Assert(antecedent1 != null);
        VCExpr antecedent2 = Gen.AtMost(w, par);
        Contract.Assert(antecedent2 != null);
        VCExpr body = Gen.Implies(Gen.And(antecedent1, antecedent2),
                                   Gen.Or(Gen.Eq(cAsVar, w), Gen.Eq(par, w)));
        Contract.Assert(body != null);
        res = Gen.AndSimp(res,
                          Gen.Forall(w,
                                     Gen.Trigger(true, antecedent1, antecedent2),
                                     body));
      }

      // Ancestors of c are only c itself and the ancestors of the
      // parents of c
      VCExpr minAncestors = Gen.Eq(cAsVar, w);
      Contract.Assert(minAncestors != null);
      foreach (ConstantParent p in c.Parents) {
        Contract.Assert(p != null);
        minAncestors =
          Gen.Or(minAncestors,
                 Gen.AtMost(Translator.LookupVariable(cce.NonNull(p.Parent.Decl)), w));
      }
      VCExpr antecedent = Gen.AtMost(cAsVar, w);
      Contract.Assert(antecedent != null);
      res = Gen.AndSimp(res,
                        Gen.Forall(w,
                                   Gen.Trigger(true, antecedent),
                                   Gen.Implies(antecedent, minAncestors)));

      // Constraints for unique child-parent edges
      foreach (ConstantParent p in c.Parents) {
        Contract.Assert(p != null);
        if (p.Unique)
          res =
            Gen.AndSimp(res,
                        GenUniqueParentConstraint(c, cce.NonNull((Constant)p.Parent.Decl)));
      }

      return res;
    }

    // Generate axioms that state that all direct children of c are
    // specified; this is the dual of the axiom stating that all direct
    // ancestors of a constant are known
    private VCExpr GenCompleteChildrenConstraints(Constant c) {
      Contract.Requires(c != null);
      Contract.Requires(c.ChildrenComplete);
      Contract.Ensures(Contract.Result<VCExpr>() != null);


      VCExprVar cAsVar = Translator.LookupVariable(c);
      VCExprVar w = Gen.Variable("w", c.TypedIdent.Type);

      VCExpr maxDescendants = Gen.Eq(cAsVar, w);
      foreach (Constant d in Constants) {
        Contract.Assert(d != null);
        if (d.Parents != null && d.Parents.Any(p => c.Equals(p.Parent.Decl)))
          maxDescendants = Gen.Or(maxDescendants,
                                  Gen.AtMost(w, Translator.LookupVariable(d)));
      }

      VCExpr antecedent = Gen.AtMost(w, cAsVar);
      Contract.Assert(antecedent != null);
      return Gen.Forall(w,
                        Gen.Trigger(true, antecedent),
                        Gen.Implies(antecedent, maxDescendants));
    }

    private void CloseChildrenCompleteConstants() {
      foreach (Constant c in CompleteConstantsOpen) {
        Contract.Assert(c != null);
        AddAxiom(GenCompleteChildrenConstraints(c));
      }
      CompleteConstantsOpen.Clear();
    }

    // Generate the axiom ensuring that the sub-dags underneath unique
    // child-parent edges are all disjoint
    private VCExpr GenUniqueParentConstraint(Constant child, Constant parent) {
      Contract.Requires(child != null);
      Contract.Requires(parent != null);
      Contract.Requires(child.TypedIdent.Type.Equals(parent.TypedIdent.Type));
      Contract.Ensures(Contract.Result<VCExpr>() != null);



      VCExprVar w = Gen.Variable("w", child.TypedIdent.Type);
      Contract.Assert(w != null);
      VCExpr antecedent =
        Gen.AtMost(w, Translator.LookupVariable(child));
      Contract.Assert(antecedent != null);
      VCExpr succedent =
        Gen.Eq(Gen.Function(OneStepFunFor(child.TypedIdent.Type),
                            Translator.LookupVariable(parent), w),
               Translator.LookupVariable(child));
      Contract.Assert(succedent != null);

      return Gen.Forall(w,
                        Gen.Trigger(true, antecedent),
                        Gen.Implies(antecedent, succedent));
    }

  }

}
