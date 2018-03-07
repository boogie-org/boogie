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

    private UniqueNamer Namer;
    private readonly SMTLibProverOptions Options;
    private HashSet<Function/*!*/>/*!*/ RegisteredRelations = new HashSet<Function>();

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
      InitializeKnownDecls();
    }

    // not used
    protected override bool StandardResult(VCExpr node, bool arg) {
      //Contract.Requires(node != null);
      return true;
    }

    private readonly List<string/*!>!*/> AllDecls = new List<string/*!*/> ();
    private readonly List<string/*!>!*/> IncDecls = new List<string/*!*/> ();

    // In order to support push/pop interface of the theorem prover, the "known" declarations
    // must be kept in a stack

    private HashSet<Function/*!*/>/*!*/ KnownFunctions
    {
        get { return _KnownFunctions.Peek(); }
    }

    private HashSet<VCExprVar/*!*/>/*!*/ KnownVariables
    {
        get { return _KnownVariables.Peek(); }
    }

    private HashSet<Type/*!*/>/*!*/ KnownTypes
    {
        get { return _KnownTypes.Peek(); }
    }

    private HashSet<string/*!*/>/*!*/ KnownStoreFunctions
    {
        get { return _KnownStoreFunctions.Peek(); }
    }

    private HashSet<string/*!*/>/*!*/ KnownSelectFunctions
    {
        get { return _KnownSelectFunctions.Peek(); }
    }

    private HashSet<string> KnownLBL
    {
        get { return _KnownLBL.Peek(); }
    }

    // ------
    private readonly Stack<HashSet<Function/*!*/>/*!*/> _KnownFunctions = new Stack<HashSet<Function/*!*/>>();
    private readonly Stack<HashSet<VCExprVar/*!*/>/*!*/> _KnownVariables = new Stack<HashSet<VCExprVar/*!*/>>();

    private readonly Stack<HashSet<Type/*!*/>/*!*/> _KnownTypes = new Stack<HashSet<Type>>();
    private readonly Stack<HashSet<string/*!*/>/*!*/> _KnownStoreFunctions = new Stack<HashSet<string>>();
    private readonly Stack<HashSet<string/*!*/>/*!*/> _KnownSelectFunctions = new Stack<HashSet<string>>();
    private readonly Stack<HashSet<string>> _KnownLBL = new Stack<HashSet<string>>();
		
	// lets RPFP checker capture decls	
	public abstract class DeclHandler {
		public abstract void VarDecl(VCExprVar v);
		public abstract void FuncDecl(Function f);
	}
		
	private DeclHandler declHandler = null;

	public void SetDeclHandler(DeclHandler _d){
		declHandler = _d;
	}
		
    private void InitializeKnownDecls()
    {
        _KnownFunctions.Push(new HashSet<Function>());
        _KnownVariables.Push(new HashSet<VCExprVar>());
        _KnownTypes.Push(new HashSet<Type>());
        _KnownStoreFunctions.Push(new HashSet<string>());
        _KnownSelectFunctions.Push(new HashSet<string>());
        _KnownLBL.Push(new HashSet<string>());
    }

    public void Reset()
    {
      _KnownFunctions.Clear();
      _KnownVariables.Clear();
      _KnownTypes.Clear();
      _KnownStoreFunctions.Clear();
      _KnownSelectFunctions.Clear();
      _KnownLBL.Clear();
      AllDecls.Clear();
      IncDecls.Clear();
      InitializeKnownDecls();
    }

    public void Push()
    {
        Contract.Assert(_KnownFunctions.Count > 0);
        _KnownFunctions.Push(new HashSet<Function>(_KnownFunctions.Peek()));
        _KnownVariables.Push(new HashSet<VCExprVar>(_KnownVariables.Peek()));
        _KnownTypes.Push(new HashSet<Type>(_KnownTypes.Peek()));
        _KnownStoreFunctions.Push(new HashSet<string>(_KnownStoreFunctions.Peek()));
        _KnownSelectFunctions.Push(new HashSet<string>(_KnownSelectFunctions.Peek()));
        _KnownLBL.Push(new HashSet<string>(_KnownLBL.Peek()));
    }

    public void Pop()
    {
        Contract.Assert(_KnownFunctions.Count > 1);
        _KnownFunctions.Pop();
        _KnownVariables.Pop();
        _KnownTypes.Pop();
        _KnownStoreFunctions.Pop();
        _KnownSelectFunctions.Pop();
        _KnownLBL.Pop();
    }

    public void SetNamer(UniqueNamer namer)
    {
      Namer = namer;
    }

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

    public string TypeToStringReg(Type t)
    {
      RegisterType(t);
      return TypeToString(t);
    }

    public void AddFunction(Function func) {
      if (KnownFunctions.Contains(func))
        return;
      KnownFunctions.Add(func);
	  if(declHandler != null)
		declHandler.FuncDecl(func);
    }

    public void RegisterRelation(Function func)
    {
      if (RegisteredRelations.Contains(func))
        return;
      RegisteredRelations.Add(func);
    }

    public override bool Visit(VCExprNAry node, bool arg) {
      Contract.Requires(node != null);

      if (node.Op is VCExprStoreOp) RegisterStore(node);
      else if (node.Op is VCExprSelectOp) RegisterSelect(node);
      else if (node.Op is VCExprSoftOp) {
        var exprVar = node[0] as VCExprVar;
        AddDeclaration(string.Format("(declare-fun {0} () Bool)", exprVar.Name));
        AddDeclaration(string.Format("(assert-soft {0} :weight {1})", exprVar.Name, ((VCExprSoftOp)node.Op).Weight));
      } else if (node.Op.Equals(VCExpressionGenerator.NamedAssumeOp)) {
        var exprVar = node[0] as VCExprVar;
        AddDeclaration(string.Format("(declare-fun {0} () Bool)", exprVar.Name));
        if (CommandLineOptions.Clo.PrintNecessaryAssumes)
        {
          AddDeclaration(string.Format("(assert (! {0} :named {1}))", exprVar.Name, "aux$$" + exprVar.Name));
        }
      } else {
        VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
        if (op != null && 
          !(op.Func is DatatypeConstructor) && !(op.Func is DatatypeMembership) && !(op.Func is DatatypeSelector) && 
          !KnownFunctions.Contains(op.Func)) {
          Function f = op.Func;
          Contract.Assert(f != null);
          
          var builtin = SMTLibExprLineariser.ExtractBuiltin(f);
          if (builtin == null) {
            string printedName = Namer.GetQuotedName(f, f.Name);
            Contract.Assert(printedName != null);

            Contract.Assert(f.OutParams.Count == 1);
            var argTypes = f.InParams.Cast<Variable>().MapConcat(p => TypeToStringReg(p.TypedIdent.Type), " ");
            string decl;
            if(RegisteredRelations.Contains(op.Func))
                decl = "(declare-rel " + printedName + " (" + argTypes + ") " + ")";
            else
                decl = "(declare-fun " + printedName + " (" + argTypes + ") " + TypeToStringReg(f.OutParams[0].TypedIdent.Type) + ")";
            AddDeclaration(decl);
            if (declHandler != null) declHandler.FuncDecl(f);
          }
          KnownFunctions.Add(f);
        } else {
          var lab = node.Op as VCExprLabelOp;
          if (lab != null && !KnownLBL.Contains(lab.label)) {
            KnownLBL.Add(lab.label);
            var name = SMTLibNamer.QuoteId(Namer.LabelVar(lab.label));
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
        if (!(printedName.StartsWith("assume$$") || printedName.StartsWith("soft$$") || printedName.StartsWith("try$$")))
        {
          AddDeclaration(decl);
        }
        KnownVariables.Add(node);
		if(declHandler != null)
			declHandler.VarDecl(node);
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

      if (type.IsBool || type.IsInt || type.IsReal || type.IsBv || type.IsFloat || type.IsRMode)
        return;

      CtorType ctorType = type as CtorType;
      if (ctorType != null && ctorType.IsDatatype())
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