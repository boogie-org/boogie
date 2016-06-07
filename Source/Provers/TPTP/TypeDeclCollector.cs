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

namespace Microsoft.Boogie.TPTP
{
  // Visitor for collecting the occurring function symbols in a VCExpr,
  // and for creating the corresponding declarations

  public class TypeDeclCollector : BoundVarTraversingVCExprVisitor<bool, bool> {

    private readonly HashSet<string/*!*/>/*!*/ KnownStoreFunctions = new HashSet<string>();
    private readonly HashSet<string/*!*/>/*!*/ KnownSelectFunctions = new HashSet<string>();

    private readonly UniqueNamer Namer;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Namer != null);
      Contract.Invariant(AllDecls != null);
      Contract.Invariant(IncDecls != null);
      Contract.Invariant(cce.NonNull(KnownFunctions));
      Contract.Invariant(cce.NonNull(KnownVariables));
    }


    public TypeDeclCollector(UniqueNamer namer) {
      Contract.Requires(namer != null);
      this.Namer = namer;
    }

    // not used
    protected override bool StandardResult(VCExpr node, bool arg) {
      //Contract.Requires(node != null);
      return true;
    }

    private readonly List<string/*!>!*/> AllDecls = new List<string/*!*/> ();
    private readonly List<string/*!>!*/> IncDecls = new List<string/*!*/> ();

    private readonly HashSet<Function/*!*/>/*!*/ KnownFunctions = new HashSet<Function/*!*/>();
    private readonly HashSet<VCExprVar/*!*/>/*!*/ KnownVariables = new HashSet<VCExprVar/*!*/>();

    public List<string/*!>!*/> AllDeclarations { get {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<string>>() ));

      List<string>/*!>!*/ res = new List<string/*!*/> ();
      res.AddRange(AllDecls);
      return res;
    } }

    public List<string/*!>!*/> GetNewDeclarations() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<string>>() ));
      List<string>/*!>!*/ res = new List<string/*!*/>();
      res.AddRange(IncDecls);
      IncDecls.Clear();
      return res;
    }

    private void AddDeclaration(string decl) {
      Contract.Requires(decl != null);
      AllDecls.Add(decl);
      IncDecls.Add(decl);
    }

    public void Collect(VCExpr expr) {
      Contract.Requires(expr != null);
      Traverse(expr, true);
    }

    ///////////////////////////////////////////////////////////////////////////

  
    public override bool Visit(VCExprNAry node, bool arg) {
      Contract.Requires(node != null);

      if (node.Op is VCExprStoreOp) {
        string name = TPTPExprLineariser.Lowercase(SimplifyLikeExprLineariser.StoreOpName(node));
        if (!KnownStoreFunctions.Contains(name)) {
          var id = KnownStoreFunctions.Count;

          if (CommandLineOptions.Clo.MonomorphicArrays) {
            var sel = TPTPExprLineariser.Lowercase(SimplifyLikeExprLineariser.SelectOpName(node));

            var eq = "=";
            if (node[node.Arity - 1].Type.IsBool)
              eq = "<=>";

            string xS = "", yS = "";
            string dist = "";

            for (int i = 0; i < node.Arity - 2; i++) {
              if (i != 0) {
                dist += " | ";
                xS += ",";
                yS += ",";
              }
              var x = "X" + i;
              var y = "Y" + i;
              xS += x;
              yS += y;
              dist += string.Format("({0} != {1})", x, y);
            }

            string ax1 = "fof(selectEq" + id + ", axiom, ! [M,V," + xS + "] : (" +
                             string.Format("{0}({1}(M,{2},V),{2}) {3} V", sel, name, xS, eq) + ")).";
            string ax2 = "fof(selectNeq" + id + ", axiom, ! [M,V," + xS + "," + yS + "] : (" +
                             string.Format("( {0} ) => ", dist) +
                             string.Format("{0}({1}(M,{2},V),{3}) {4} {0}(M,{3})", sel, name, xS, yS, eq) + ")).";

            AddDeclaration(ax1);
            AddDeclaration(ax2);
          }

          KnownStoreFunctions.Add(name);
        }
        //
      }

      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprVar node, bool arg) {

      return base.Visit(node, arg);
    }
  }

}