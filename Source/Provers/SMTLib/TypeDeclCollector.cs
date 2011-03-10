//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.SMTLib
{
  // Visitor for collecting the occurring function symbols in a VCExpr,
  // and for creating the corresponding declarations

  public class TypeDeclCollector : BoundVarTraversingVCExprVisitor<bool, bool> {

    private readonly UniqueNamer Namer;
    private readonly SMTLibProverOptions Options;

    [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(Namer!=null);
      Contract.Invariant(AllDecls != null);
      Contract.Invariant(IncDecls != null);
      Contract.Invariant(KnownFunctions != null);
      Contract.Invariant(KnownVariables != null);
}


    public TypeDeclCollector(SMTLibProverOptions opts, UniqueNamer namer) {
      Contract.Requires(namer != null);
      this.Namer = namer;
      this.Options = opts;
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

    private readonly HashSet<Type/*!*/>/*!*/ KnownTypes = new HashSet<Type>();
    private readonly HashSet<string/*!*/>/*!*/ KnownStoreFunctions = new HashSet<string>();
    private readonly HashSet<string/*!*/>/*!*/ KnownSelectFunctions = new HashSet<string>();
    private readonly HashSet<string> KnownLBL = new HashSet<string>();


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

    private string TypeToStringReg(Type t)
    {
      RegisterType(t);
      return TypeToString(t);
    }

    public override bool Visit(VCExprNAry node, bool arg) {
      Contract.Requires(node != null);

      if (node.Op is VCExprStoreOp) RegisterStore(node);
      else if (node.Op is VCExprSelectOp) RegisterSelect(node);
      else {
        VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
        if (op != null && !KnownFunctions.Contains(op.Func)) {
          Function f = op.Func;
          Contract.Assert(f != null);
          
          var builtin = SMTLibExprLineariser.ExtractBuiltin(f);
          if (builtin == null) {
            string printedName = Namer.GetQuotedName(f, f.Name);
            Contract.Assert(printedName != null);

            Contract.Assert(f.OutParams.Length == 1);
            var argTypes = f.InParams.Cast<Variable>().MapConcat(p => TypeToStringReg(p.TypedIdent.Type), " ");
            string decl = "(declare-fun " + printedName + " (" + argTypes + ") " + TypeToStringReg(f.OutParams[0].TypedIdent.Type) + ")";
            AddDeclaration(decl);
          }
          KnownFunctions.Add(f);
        } else {
          var lab = node.Op as VCExprLabelOp;
          if (lab != null && !KnownLBL.Contains(lab.label)) {
            KnownLBL.Add(lab.label);
            var name = SMTLibNamer.QuoteId(SMTLibNamer.LabelVar(lab.label));
            AddDeclaration("(declare-fun " + name + " () Bool)");
          }
        }
      }

      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprVar node, bool arg) {
      Contract.Requires(node != null);
      if (!BoundTermVars.Contains(node) && !KnownVariables.Contains(node)) {
        string printedName = Namer.GetQuotedName(node, node.Name);
        Contract.Assert(printedName!=null);
        RegisterType(node.Type);
        string decl =
          "(declare-fun " + printedName + " () " + TypeToString(node.Type) + ")";
        AddDeclaration(decl);
        KnownVariables.Add(node);
      }

      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprQuantifier node, bool arg)
    {
      Contract.Requires(node != null);
      foreach (VCExprVar v in node.BoundVars) {
        Contract.Assert(v != null);
        RegisterType(v.Type);
      }

      return base.Visit(node, arg);
    } 

    private void RegisterType(Type type)
    {
      Contract.Requires(type != null);
      if (KnownTypes.Contains(type)) return;

      if (type.IsMap && CommandLineOptions.Clo.MonomorphicArrays) {
        KnownTypes.Add(type);
        MapType mapType = type.AsMap;
        Contract.Assert(mapType != null);

        foreach (Type t in mapType.Arguments) {
          Contract.Assert(t != null);
          RegisterType(t);
        }
        RegisterType(mapType.Result);

        if (!CommandLineOptions.Clo.UseArrayTheory)
          AddDeclaration("(declare-sort " + TypeToString(type) + " 0)");

        return;
      }

      if (type.IsBool || type.IsInt || type.IsBv)
        return;

      if (CommandLineOptions.Clo.TypeEncodingMethod == CommandLineOptions.TypeEncoding.Monomorphic) {
        AddDeclaration("(declare-sort " + TypeToString(type) + " 0)");
        KnownTypes.Add(type);
        return;
      }
    }

    private void RegisterSelect(VCExprNAry node)
    {
      RegisterType(node[0].Type);

      if (CommandLineOptions.Clo.UseArrayTheory)
        return;

      string name = SimplifyLikeExprLineariser.SelectOpName(node);
      name = Namer.GetQuotedName(name, name);

      if (!KnownSelectFunctions.Contains(name)) {
        string decl = "(declare-fun " + name + " (" + node.MapConcat(n => TypeToString(n.Type), " ") + ") " + TypeToString(node.Type) + ")";
        AddDeclaration(decl);
        KnownSelectFunctions.Add(name);
      }
    }

    private void RegisterStore(VCExprNAry node)
    {
      RegisterType(node.Type);        // this is the map type, registering it should register also the index and value types

      if (CommandLineOptions.Clo.UseArrayTheory)
        return;

      string name = SimplifyLikeExprLineariser.StoreOpName(node);
      name = Namer.GetQuotedName(name, name);

      if (!KnownStoreFunctions.Contains(name)) {
        string decl = "(declare-fun " + name + " (" + node.MapConcat(n => TypeToString(n.Type), " ") + ") " + TypeToString(node.Type) + ")";
        AddDeclaration(decl);

        if (CommandLineOptions.Clo.MonomorphicArrays) {
          var sel = SimplifyLikeExprLineariser.SelectOpName(node);
          sel = Namer.GetQuotedName(sel, sel);
          
          if (!KnownSelectFunctions.Contains(sel)) {
            // need to declare it before reference
            var args = node.SkipEnd(1);
            var ret = node.Last();
            string seldecl = "(declare-fun " + sel + " (" + args.MapConcat(n => TypeToString(n.Type), " ") + ") " + TypeToString(ret.Type) + ")";
            AddDeclaration(seldecl);
            KnownSelectFunctions.Add(sel);
          }

          string ax1 = "(assert (forall (";
          string ax2 = "(assert (forall (";

          string argX = "", argY = "";
          string dist = "";
          for (int i = 0; i < node.Arity; i++) {
            var t = " " + TypeToString(node[i].Type);
            var x = " ?x" + i;
            var y = " ?y" + i;
            ax1 += " (" + x + t + ")";
            ax2 += " (" + x + t + ")";
            if (i != 0 && i != node.Arity - 1) {
              argX += x;
              argY += y;
              ax2 += " (" + y + t + ")";
              dist += " (not (=" + x + y + "))";
            }
          }
          string v = " ?x" + (node.Arity - 1);
          ax1 += ") (= (" + sel + " (" + name + " ?x0" + argX + v + ")" + argX + ") " + v + ")";
          ax1 += "))";

          if (node.Arity > 3)
            dist = "(or " + dist + ")";
          ax2 += ") (=> " + dist + " (= (" + sel + " (" + name + " ?x0" + argX + v + ")" + argY + ") (" + sel + " ?x0" + argY + ")))";
          ax2 += "))";

          AddDeclaration(ax1);
          AddDeclaration(ax2);
        }

        KnownStoreFunctions.Add(name);
      }
      //
    }

  }

}