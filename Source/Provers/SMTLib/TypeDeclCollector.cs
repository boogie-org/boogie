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

namespace Microsoft.Boogie.SMTLib
{
  // Visitor for collecting the occurring function symbols in a VCExpr,
  // and for creating the corresponding declarations

  public class TypeDeclCollector : BoundVarTraversingVCExprVisitor<bool, bool> {

    private readonly UniqueNamer Namer;
    [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(Namer!=null);
      Contract.Invariant(AllDecls != null);
      Contract.Invariant(IncDecls != null);
      Contract.Invariant(KnownFunctions != null);
      Contract.Invariant(KnownVariables != null);
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

    private readonly IDictionary<Function/*!*/, bool>/*!*/ KnownFunctions =
      new Dictionary<Function/*!*/, bool> ();
    private readonly IDictionary<VCExprVar/*!*/, bool>/*!*/ KnownVariables =
      new Dictionary<VCExprVar/*!*/, bool> ();

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

    private static string TypeToString(Type t) {
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return SMTLibExprLineariser.TypeToString(t);
    }

    public override bool Visit(VCExprNAry node, bool arg) {
      Contract.Requires(node != null);
      // there are a couple of cases where operators have to be
      // registered by generating appropriate statements

      VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
      if (op != null && !KnownFunctions.ContainsKey(op.Func)) {
        Function f = op.Func;
        Contract.Assert(f!=null);
        string printedName = Namer.GetName(f, SMTLibExprLineariser.MakeIdPrintable(f.Name));
        Contract.Assert(printedName!=null);
        string decl = ":extrafuns ((" + printedName;

        foreach (Variable v in f.InParams) {
          Contract.Assert(v!=null);
          decl += " " + TypeToString(v.TypedIdent.Type);
        }
       Contract.Assert(f.OutParams.Length == 1);
        foreach (Variable v in f.OutParams) {
          Contract.Assert(v!=null);
          decl += " " + TypeToString(v.TypedIdent.Type);
        }

        decl += "))";
        
        AddDeclaration(decl);
        KnownFunctions.Add(f, true);
      }

      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprVar node, bool arg) {
      Contract.Requires(node != null);
      if (!BoundTermVars.Contains(node) && !KnownVariables.ContainsKey(node)) {
        string printedName = Namer.GetName(node, SMTLibExprLineariser.MakeIdPrintable(node.Name));
        Contract.Assert(printedName!=null);
        string decl =
          ":extrafuns ((" + printedName + " " + TypeToString(node.Type) + "))";
        AddDeclaration(decl);
        KnownVariables.Add(node, true);
      }

      return base.Visit(node, arg);
    }
  }

}