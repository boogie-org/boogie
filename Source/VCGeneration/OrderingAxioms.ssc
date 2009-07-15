//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Microsoft.Contracts;
using Microsoft.Boogie.VCExprAST;

// Class for constructing and collecting the axioms of the partial
// order <:. The class also manages "unique" attributes of constants
// and generated the necessary assumptions for the theorem prover.

// TODO: there should be an interface so that different ways to handle
// ordering relations can be accessed uniformly

namespace Microsoft.Boogie
{

  public class OrderingAxiomBuilder {

    private readonly VCExpressionGenerator! Gen;
    private readonly Boogie2VCExprTranslator! Translator;

    public OrderingAxiomBuilder(VCExpressionGenerator! gen,
                                Boogie2VCExprTranslator! translator) {
      this.Gen = gen;
      this.Translator = translator;
      OneStepFuns = new Dictionary<Type!, Function!> ();
      Constants = new List<Constant!> ();
      CompleteConstantsOpen = new List<Constant!> ();
      AllAxioms = new List<VCExpr!> ();
      IncAxioms = new List<VCExpr!> ();
    }

    public OrderingAxiomBuilder(VCExpressionGenerator! gen,
                                Boogie2VCExprTranslator! translator,
                                OrderingAxiomBuilder! builder) {
      this.Gen = gen;
      this.Translator = translator;
      OneStepFuns = new Dictionary<Type!, Function!> (builder.OneStepFuns);
      Constants = new List<Constant!> (builder.Constants);
      CompleteConstantsOpen = new List<Constant!> (builder.CompleteConstantsOpen);
      AllAxioms = new List<VCExpr!> (builder.AllAxioms);
      IncAxioms = new List<VCExpr!> (builder.IncAxioms);
    }

    ////////////////////////////////////////////////////////////////////////////

    // Used to axiomatise the disjoint-sub-dag specs that are
    // described by parents with the "unique" flag
    private readonly IDictionary<Type!, Function!>! OneStepFuns;

    private Function! OneStepFunFor(Type! t) {
      Function res;
      if (!OneStepFuns.TryGetValue(t, out res)) {
        VariableSeq! args = new VariableSeq ();
        args.Add(new Formal (Token.NoToken,
                             new TypedIdent (Token.NoToken, "arg0", t),
                             true));
        args.Add(new Formal (Token.NoToken,
                             new TypedIdent (Token.NoToken, "arg1", t),
                             true));
        Formal! result = new Formal (Token.NoToken,
                                     new TypedIdent (Token.NoToken, "res", t),
                                     false);
        res = new Function (Token.NoToken, "oneStep",
                            new TypeVariableSeq (), args, result);
        OneStepFuns.Add(t, res);
      }
      return (!)res;
    }

    ////////////////////////////////////////////////////////////////////////////

    private readonly List<Constant!>! Constants = new List<Constant!> ();

    // A list to handle constants whose direct children are fully
    // specified (the "complete" keyword). Constants are removed from
    // the list as soon as the corresponding axiom has been generated,
    // which means that from this point on no further children can be
    // added
    private readonly List<Constant!>! CompleteConstantsOpen = new List<Constant!> ();

    // list in which all axioms are collected
    private readonly List<VCExpr!>! AllAxioms = new List<VCExpr!> ();

    // list in which axioms are incrementally collected
    private readonly List<VCExpr!>! IncAxioms = new List<VCExpr!> ();

    private void AddAxiom(VCExpr! axiom) {
      if (axiom.Equals(VCExpressionGenerator.True))
        return;
      AllAxioms.Add(axiom);
      IncAxioms.Add(axiom);
    }

    // Return all axioms that were added since the last time NewAxioms
    // was called
    public VCExpr! GetNewAxioms() {
      CloseChildrenCompleteConstants();
      VCExpr! res = Gen.NAry(VCExpressionGenerator.AndOp, IncAxioms);
      IncAxioms.Clear();
      return res;
    }

    // return all axioms
    public VCExpr! Axioms { get {
      CloseChildrenCompleteConstants();
      return Gen.NAry(VCExpressionGenerator.AndOp, AllAxioms);
    } }

    ////////////////////////////////////////////////////////////////////////////
    
    // Generate the normal axioms for a partial order relation
    public void Setup() {
      TypeVariable! alpha = new TypeVariable(Token.NoToken, "alpha");
      List<TypeVariable!>! typeParams = new List<TypeVariable!> ();
      typeParams.Add(alpha);

      List<VCTrigger!>! triggers = new List<VCTrigger!> ();

      VCExprVar! x = Gen.Variable("x", alpha);
      VCExprVar! y = Gen.Variable("y", alpha);
      VCExprVar! z = Gen.Variable("z", alpha);
      
      List<VCExprVar!>! boundVars = new List<VCExprVar!> ();

      // reflexivity
      boundVars.Add(x);
      AddAxiom(Gen.Forall(typeParams, boundVars, triggers,
                          new VCQuantifierInfos ("bg:subtype-refl", -1, false, null),
                          Gen.AtMost(x, x)));

      // transitivity
      boundVars = new List<VCExprVar!> ();
      boundVars.Add(x); boundVars.Add(y); boundVars.Add(z);
      triggers = new List<VCTrigger!> ();
      triggers.Add(Gen.Trigger(true, Gen.AtMost(x, y), Gen.AtMost(y, z)));
      VCExpr! body = Gen.Implies(Gen.And(Gen.AtMost(x, y), Gen.AtMost(y, z)),
                                 Gen.AtMost(x, z));
      AddAxiom(Gen.Forall(typeParams, boundVars, triggers,
                          new VCQuantifierInfos ("bg:subtype-trans", -1, false, null),
                          body));

      // anti-symmetry
      boundVars = new List<VCExprVar!> ();
      boundVars.Add(x); boundVars.Add(y);
      triggers = new List<VCTrigger!> ();
      triggers.Add(Gen.Trigger(true, Gen.AtMost(x, y), Gen.AtMost(y, x)));
      body = Gen.Implies(Gen.And(Gen.AtMost(x, y), Gen.AtMost(y, x)),
                         Gen.Eq(x, y));
      AddAxiom(Gen.Forall(typeParams, boundVars, triggers,
                          new VCQuantifierInfos ("bg:subtype-antisymm", -1, false, null),
                          body));
    }
    
    ////////////////////////////////////////////////////////////////////////////

    public void AddConstant(Constant! c) {
      AddAxiom(GenParentConstraints(c));
      Constants.Add(c);
      if (c.ChildrenComplete)
        CompleteConstantsOpen.Add(c);

      // ensure that no further children are added to closed
      // children-complete constants
      assert !(c.Parents != null &&
               exists{ConstantParent! p in c.Parents;
                      ((Constant!)p.Parent.Decl).ChildrenComplete &&
                      !CompleteConstantsOpen.Contains((Constant)p.Parent.Decl)});
    }

    // Generate the constraints telling that parents of a constant are
    // strictly greater than the constant itself, and are the minimal
    // elements with this property
    private VCExpr! GenParentConstraints(Constant! c) {
      VCExpr! res = VCExpressionGenerator.True;

      if (c.Parents == null)
        return res;

      VCExprVar! cAsVar = Translator.LookupVariable(c);
      VCExprVar! w = Gen.Variable("w", c.TypedIdent.Type);

      // Parents of c are proper ancestors of c
      foreach (ConstantParent! p in c.Parents) {
        VCExprVar! par = Translator.LookupVariable((!)p.Parent.Decl);
        res = Gen.AndSimp(res, Gen.Neq(cAsVar, par));
        res = Gen.AndSimp(res, Gen.AtMost(cAsVar, par));
      }      

      // Parents are direct ancestors of c (no other elements are in
      // between c and a parent)
      foreach (ConstantParent! p in c.Parents) {
        VCExprVar! par = Translator.LookupVariable((!)p.Parent.Decl);
        VCExpr! antecedent1 = Gen.AtMost(cAsVar, w);
        VCExpr! antecedent2 = Gen.AtMost(w, par);
        VCExpr! body = Gen.Implies(Gen.And(antecedent1, antecedent2),
                                   Gen.Or(Gen.Eq(cAsVar, w), Gen.Eq(par, w)));
        res = Gen.AndSimp(res,
                          Gen.Forall(w,
                                     Gen.Trigger(true, antecedent1, antecedent2),
                                     body));
      }

      // Ancestors of c are only c itself and the ancestors of the
      // parents of c
      VCExpr! minAncestors = Gen.Eq(cAsVar, w);
      foreach (ConstantParent! p in c.Parents)
        minAncestors =
          Gen.Or(minAncestors,
                 Gen.AtMost(Translator.LookupVariable((!)p.Parent.Decl), w));

      VCExpr! antecedent = Gen.AtMost(cAsVar, w);
      res = Gen.AndSimp(res,
                        Gen.Forall(w,
                                   Gen.Trigger(true, antecedent),
                                   Gen.Implies(antecedent, minAncestors)));

      // Constraints for unique child-parent edges
      foreach (ConstantParent! p in c.Parents) {
        if (p.Unique)
          res =
            Gen.AndSimp(res,
                        GenUniqueParentConstraint(c, (Constant!)p.Parent.Decl));
      }

      return res;
    }

    // Generate axioms that state that all direct children of c are
    // specified; this is the dual of the axiom stating that all direct
    // ancestors of a constant are known
    private VCExpr! GenCompleteChildrenConstraints(Constant! c)
      requires c.ChildrenComplete; {
      
      VCExprVar! cAsVar = Translator.LookupVariable(c);
      VCExprVar! w = Gen.Variable("w", c.TypedIdent.Type);
      
      VCExpr! maxDescendants = Gen.Eq(cAsVar, w);
      foreach (Constant! d in Constants) {
        if (d.Parents != null &&
            exists{ConstantParent! p in d.Parents; c.Equals(p.Parent.Decl)})
          maxDescendants = Gen.Or(maxDescendants,
                                  Gen.AtMost(w, Translator.LookupVariable(d)));
      }

      VCExpr! antecedent = Gen.AtMost(w, cAsVar);
      return Gen.Forall(w,
                        Gen.Trigger(true, antecedent),
                        Gen.Implies(antecedent, maxDescendants));
    }
    
    private void CloseChildrenCompleteConstants() {
      foreach (Constant! c in CompleteConstantsOpen)
        AddAxiom(GenCompleteChildrenConstraints(c));
      CompleteConstantsOpen.Clear();
    }

    // Generate the axiom ensuring that the sub-dags underneath unique
    // child-parent edges are all disjoint
    private VCExpr! GenUniqueParentConstraint(Constant! child, Constant! parent)
      requires child.TypedIdent.Type.Equals(parent.TypedIdent.Type); {

      VCExprVar! w = Gen.Variable("w", child.TypedIdent.Type);

      VCExpr! antecedent =
        Gen.AtMost(w, Translator.LookupVariable(child));
      VCExpr! succedent =
        Gen.Eq(Gen.Function(OneStepFunFor(child.TypedIdent.Type),
                            Translator.LookupVariable(parent), w),
               Translator.LookupVariable(child));

      return Gen.Forall(w,
                        Gen.Trigger(true, antecedent),
                        Gen.Implies(antecedent, succedent));
    }

  }

}
