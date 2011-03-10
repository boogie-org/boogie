//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.Simplify
{
  // Simplify does not understand the LET operator, so we have to replace
  // it with implications (previously, this was done in the VCExprGenerator), or
  // we have to apply the let as a substitution (in the case of terms)

  // This visitor expects that let-bindings are sorted, so that bound
  // variables only occur after their declaration

  public class Let2ImpliesMutator : SubstitutingVCExprVisitor {

    public Let2ImpliesMutator(VCExpressionGenerator gen) :base(gen) {
     Contract.Requires(gen!=null);
     this.keepLetFormula = this.keepLetTerm = false;
    }

    public Let2ImpliesMutator(VCExpressionGenerator gen, bool keepLetTerm, bool keepLetFormula):base(gen) {
      Contract.Requires(gen!=null);
      
      this.keepLetTerm = keepLetTerm;
      this.keepLetFormula = keepLetFormula;
    }
    
    readonly bool keepLetTerm;
    readonly bool keepLetFormula;

    public VCExpr Mutate(VCExpr expr) {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Mutate(expr, new VCExprSubstitution ());
    }

    ////////////////////////////////////////////////////////////////////////////

    private int polarity = 1;  // 1 for positive, -1 for negative, 0 for both

    // we also track which variables occur in positive, negative, or
    // in both positions (to decide whether implications or equations
    // have to be used to define such a variable)
    private enum OccurrenceTypes { None, Pos, Neg, PosNeg };
    private OccurrenceTypes Union(OccurrenceTypes o1, OccurrenceTypes o2) {
      switch(o1) {
      case OccurrenceTypes.None: return o2;
      case OccurrenceTypes.Pos:
        switch(o2) {
        case OccurrenceTypes.None:
        case OccurrenceTypes.Pos:
          return OccurrenceTypes.Pos;
        default:
          return OccurrenceTypes.PosNeg;
        }
      case OccurrenceTypes.Neg:
        switch(o2) {
        case OccurrenceTypes.None:
        case OccurrenceTypes.Neg:
          return OccurrenceTypes.Neg;
        default:
          return OccurrenceTypes.PosNeg;
        }
      default:
        return OccurrenceTypes.PosNeg;
      }
    }

    private IDictionary<VCExprVar/*!*/, OccurrenceTypes>/*!*/ VarOccurrences =
      new Dictionary<VCExprVar/*!*/, OccurrenceTypes>();
    [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(VarOccurrences != null);
}

    ////////////////////////////////////////////////////////////////////////////

    public override VCExpr Visit(VCExprVar node,
                                  VCExprSubstitution substitution) {
      Contract.Requires(node!= null);
      Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      VCExpr res = base.Visit(node, substitution);
      Contract.Assert(res!=null);

      VCExprVar resAsVar = res as VCExprVar;
      if (resAsVar != null) {
        OccurrenceTypes occ;
        if (polarity > 0)
          occ = OccurrenceTypes.Pos;
        else if (polarity < 0)
          occ = OccurrenceTypes.Neg;
        else
          occ = OccurrenceTypes.PosNeg;

        OccurrenceTypes oldOcc;
        if (VarOccurrences.TryGetValue(resAsVar, out oldOcc))
          occ = Union(occ, oldOcc);
        VarOccurrences[resAsVar] = occ;
      }

      return res;
    }

    public override VCExpr Visit(VCExprNAry node,
                                  VCExprSubstitution substitution) {
      Contract.Requires(node != null);
      Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      // track the polarity to ensure that no implications are introduced
      // in negative positions
      // UGLY: the code for tracking polarities should be factored out
      // (similar code is used in the TypeEraser)

      VCExpr res;
      if (node.Op.Equals(VCExpressionGenerator.NotOp)) {
        polarity = -polarity;
        res = base.Visit(node, substitution);
        polarity = -polarity;
      } else if (node.Op.Equals(VCExpressionGenerator.ImpliesOp)) {
        polarity = -polarity;
        VCExpr newArg0 = Mutate(node[0], substitution);
        Contract.Assert(newArg0 != null);
        polarity = -polarity;
        VCExpr newArg1 = Mutate(node[1], substitution);
        Contract.Assert(newArg1 != null);

        res = Gen.Implies(newArg0, newArg1);
      } else if (!node.Op.Equals(VCExpressionGenerator.AndOp) &&
                 !node.Op.Equals(VCExpressionGenerator.OrOp) &&
                 !(node.Op is VCExprLabelOp)) {
        // standard is to set the polarity to 0 (fits most operators)
        int oldPolarity = polarity;
        polarity = 0;
        res = base.Visit(node, substitution);
        polarity = oldPolarity;
      } else {
        res = base.Visit(node, substitution);
      }

      return res;
    }

    public override VCExpr Visit(VCExprLet originalNode,
                                  VCExprSubstitution substitution) {
      Contract.Requires(originalNode != null);
      Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      // first sort the bindings to be able to apply substitutions
      LetBindingSorter letSorter = new LetBindingSorter (Gen);
      Contract.Assert(letSorter != null);
      VCExpr newNode = letSorter.Mutate(originalNode, true);
      Contract.Assert(newNode != null);
      VCExprLet node = newNode as VCExprLet;

      if (node == null)
        // it can happen that the complete let-expressions gets eliminated by the
        // sorter, which also checks whether let-bindings are actually used
        return newNode;

      substitution.PushScope(); try {

      // the bindings that remain and that are later handled using an implication
      List<VCExprLetBinding> bindings = new List<VCExprLetBinding> ();
      List<VCExprLetBinding> keepBindings = new List<VCExprLetBinding> ();

      foreach (VCExprLetBinding binding in node) {
        Contract.Assert(binding != null);
        // in all cases we apply the substitution up to this point
        // to the bound formula
        VCExpr newE = Mutate(binding.E, substitution);
        Contract.Assert(newE != null);
        if (binding.V.Type.IsBool) {
          // a bound formula is handled using an implication; we introduce
          // a fresh variable to avoid clashes
          Contract.Assert( polarity > 0);
          
          if (keepLetFormula) {
            keepBindings.Add(Gen.LetBinding(binding.V, newE));
            
          } else {
            VCExprVar newVar = Gen.Variable(binding.V.Name, Type.Bool);
            Contract.Assert(newVar != null);
            substitution[binding.V] = newVar;

            bindings.Add(Gen.LetBinding(newVar, newE));
          }
        } else {
          if (keepLetTerm) {
            keepBindings.Add(Gen.LetBinding(binding.V, newE));
          } else {
            // a bound term is substituted
            substitution[binding.V] = newE;
          }
        }
      }

      VCExpr newBody = Mutate(node.Body, substitution);
        Contract.Assert(newBody != null);
      if (keepBindings.Count > 0) {
        newBody = Gen.Let(keepBindings, newBody);
      }

      // Depending on the places where the variable occurs, we would
      // have to introduce implications or equations to define the
      // bound variables. For the time being, we just assert that all
      // occurrences are positive
      foreach (VCExprLetBinding b in bindings) {
        Contract.Assert(b != null);
        OccurrenceTypes occ;
        if (VarOccurrences.TryGetValue(b.V, out occ))
          Contract.Assert( occ == OccurrenceTypes.None || occ == OccurrenceTypes.Pos);
      }

      return Gen.ImpliesSimp(Gen.AsImplications(bindings), newBody);

      } finally {
        substitution.PopScope();
      }
    }
  }

}