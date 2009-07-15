//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.SMTLib
{
  // Visitor for collecting the occurring function symbols in a VCExpr,
  // and for creating the corresponding declarations

  public class TypeDeclCollector : BoundVarTraversingVCExprVisitor<bool, bool> {

    private readonly UniqueNamer! Namer;

    public TypeDeclCollector(UniqueNamer! namer) {
      this.Namer = namer;
    }

    // not used
    protected override bool StandardResult(VCExpr! node, bool arg) {
      return true;
    }

    private readonly List<string!>! AllDecls = new List<string!> ();
    private readonly List<string!>! IncDecls = new List<string!> ();

    private readonly IDictionary<Function!, bool>! KnownFunctions =
      new Dictionary<Function!, bool> ();
    private readonly IDictionary<VCExprVar!, bool>! KnownVariables =
      new Dictionary<VCExprVar!, bool> ();

    public List<string!>! AllDeclarations { get {
      List<string!>! res = new List<string!> ();
      res.AddRange(AllDecls);
      return res;
    } }

    public List<string!>! GetNewDeclarations() {
      List<string!>! res = new List<string!> ();
      res.AddRange(IncDecls);
      IncDecls.Clear();
      return res;
    }

    private void AddDeclaration(string! decl) {
      AllDecls.Add(decl);
      IncDecls.Add(decl);
    }

    public void Collect(VCExpr! expr) {
      Traverse(expr, true);
    }

    ///////////////////////////////////////////////////////////////////////////

    private static string! TypeToString(Type! t) {
      return SMTLibExprLineariser.TypeToString(t);
    }

    public override bool Visit(VCExprNAry! node, bool arg) {
      // there are a couple of cases where operators have to be
      // registered by generating appropriate statements

      VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
      if (op != null && !KnownFunctions.ContainsKey(op.Func)) {
        Function! f = op.Func;
        string! printedName = Namer.GetName(f, SMTLibExprLineariser.MakeIdPrintable(f.Name));
        string! decl = ":extrafuns ((" + printedName;

        foreach (Variable! v in f.InParams) {
          decl += " " + TypeToString(v.TypedIdent.Type);
        }
        assert f.OutParams.Length == 1;
        foreach (Variable! v in f.OutParams) {
          decl += " " + TypeToString(v.TypedIdent.Type);
        }

        decl += "))";
        
        AddDeclaration(decl);
        KnownFunctions.Add(f, true);
      }

      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprVar! node, bool arg) {
      if (!BoundTermVars.Contains(node) && !KnownVariables.ContainsKey(node)) {
        string! printedName = Namer.GetName(node, SMTLibExprLineariser.MakeIdPrintable(node.Name));
        string! decl =
          ":extrafuns ((" + printedName + " " + TypeToString(node.Type) + "))";
        AddDeclaration(decl);
        KnownVariables.Add(node, true);
      }

      return base.Visit(node, arg);
    }
  }

}