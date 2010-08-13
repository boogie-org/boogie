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
using Microsoft.Contracts;
using Microsoft.Basetypes;

// Sort the bindings in a let-expression so that terms bound earlier do
// not contain variables bound later

namespace Microsoft.Boogie.VCExprAST
{

  // (argument is not used)
  public class LetBindingSorter : MutatingVCExprVisitor<bool> {

    private readonly FreeVariableCollector! FreeVarCollector =
      new FreeVariableCollector ();

    private List<VCExprVar!>! FreeVarsIn(VCExpr! expr) {
      FreeVarCollector.Collect(expr);
      List<VCExprVar!>! freeVars = new List<VCExprVar!> (FreeVarCollector.FreeTermVars.Keys);
      FreeVarCollector.Reset();
      return freeVars;
    }

    public LetBindingSorter(VCExpressionGenerator! gen) {
      base(gen);
    }

    public override VCExpr! Visit(VCExprLet! node, bool arg) {
      IDictionary<VCExprVar!, Binding!> boundVars =
        new Dictionary<VCExprVar!, Binding!> ();

      // recurse and collect the free variables in bound terms and formulae
      foreach (VCExprLetBinding! binding in node) {
        VCExpr! newE = Mutate(binding.E, arg);
        Binding! b = new Binding (binding.V, newE, FreeVarsIn(newE));
        boundVars.Add(b.V, b);
      }

      // generate the occurrence edges
      foreach (KeyValuePair<VCExprVar!, Binding!> pair in boundVars) {
        Binding! b = pair.Value;
        foreach (VCExprVar! v in b.FreeVars) {
          Binding b2;
          if (boundVars.TryGetValue(v, out b2)) {
            ((!)b2).Occurrences.Add(b);
            b.InvOccurrencesNum = b.InvOccurrencesNum + 1;
          }
        }
      }

      // topological sort
      Stack<Binding!> rootBindings = new Stack<Binding!> ();
      foreach (KeyValuePair<VCExprVar!, Binding!> pair in boundVars)
        if (pair.Value.InvOccurrencesNum == 0)
          rootBindings.Push(pair.Value);

      List<Binding!>! sortedBindings = new List<Binding!> ();
      while (rootBindings.Count > 0) {
        Binding! b = rootBindings.Pop();
        sortedBindings.Add(b);
        foreach (Binding! b2 in b.Occurrences) {
          b2.InvOccurrencesNum = b2.InvOccurrencesNum - 1;
          if (b2.InvOccurrencesNum == 0)
            rootBindings.Push(b2);
        }
      }

      if (exists{KeyValuePair<VCExprVar!, Binding!> pair in boundVars;
                 pair.Value.InvOccurrencesNum > 0})
        System.Diagnostics.Debug.Fail("Cyclic let-bindings");

      assert node.Length == sortedBindings.Count;

      // check which of the bindings can be dropped
      VCExpr! newBody = Mutate(node.Body, arg);

      IDictionary<VCExprVar!, VCExprVar!>! usedVars =
        new Dictionary<VCExprVar!, VCExprVar!> ();
      foreach (VCExprVar! v in FreeVarsIn(newBody))
        if (!usedVars.ContainsKey(v))
          usedVars.Add(v, v);

      for (int i = sortedBindings.Count - 1; i >= 0; --i) {
        if (usedVars.ContainsKey(sortedBindings[i].V)) {
          foreach (VCExprVar! v in sortedBindings[i].FreeVars)
            if (!usedVars.ContainsKey(v))
              usedVars.Add(v, v);
        } else {
          sortedBindings.RemoveAt(i);
        }
      }

      // assemble the resulting let-expression
      List<VCExprLetBinding!>! newBindings = new List<VCExprLetBinding!> ();
      foreach (Binding b in sortedBindings)
        newBindings.Add(Gen.LetBinding(b.V, b.E));

      return Gen.Let(newBindings, newBody);
    }    

    private class Binding {
      public readonly VCExprVar! V;
      public readonly VCExpr! E;
      public readonly List<VCExprVar!>! FreeVars;

      // list of all bound expression in which the variable V occurs
      // (outgoing edges)
      public readonly List<Binding>! Occurrences;

      // number of variables that are bound in this let-expression
      // and that occur in FreeVars
      // (incoming edges)
      public int InvOccurrencesNum;

      public Binding(VCExprVar! v, VCExpr! e, List<VCExprVar!>! freeVars) {
        this.V = v;
        this.E = e;
        this.FreeVars = freeVars;
        this.Occurrences = new List<Binding> ();
        this.InvOccurrencesNum = 0;
      }
    }

  }

}
