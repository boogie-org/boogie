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

namespace Microsoft.Boogie.Z3
{
  // Visitor for collecting the occurring function symbols in a VCExpr,
  // and for creating the corresponding declarations that can be fed into
  // Z3

  // (should this be rather done by Context.DeclareFunction? right now,
  // the TypeErasure visitor introduces new function symbols that are
  // not passed to this method)

  public class TypeDeclCollector : BoundVarTraversingVCExprVisitor<bool, bool> {

    private readonly UniqueNamer! Namer;

    private readonly bool NativeBv;

    public TypeDeclCollector(UniqueNamer! namer, bool nativeBv) {
      this.Namer = namer;
      this.NativeBv = nativeBv;
      AllDecls = new List<string!> ();
      IncDecls = new List<string!> ();
      KnownFunctions = new Dictionary<Function!, bool> ();
      KnownVariables = new Dictionary<VCExprVar!, bool> ();
      KnownTypes = new Dictionary<Type!, bool> ();
      KnownBvOps = new Dictionary<string!, bool> ();
      
      KnownStoreFunctions = new Dictionary<string!, bool> ();
      KnownSelectFunctions = new Dictionary<string!, bool> ();
    }

    internal TypeDeclCollector(UniqueNamer! namer, TypeDeclCollector! coll) {
      this.Namer = namer;
      this.NativeBv = coll.NativeBv;
      AllDecls = new List<string!> (coll.AllDecls);
      IncDecls = new List<string!> (coll.IncDecls);
      KnownFunctions = new Dictionary<Function!, bool> (coll.KnownFunctions);
      KnownVariables = new Dictionary<VCExprVar!, bool> (coll.KnownVariables);
      KnownTypes = new Dictionary<Type!, bool> (coll.KnownTypes);
      KnownBvOps = new Dictionary<string!, bool> (coll.KnownBvOps);
      
      KnownStoreFunctions = new Dictionary<string!, bool> (coll.KnownStoreFunctions);
      KnownSelectFunctions = new Dictionary<string!, bool> (coll.KnownSelectFunctions);
    }

    // not used
    protected override bool StandardResult(VCExpr! node, bool arg) {
      return true;
    }

    private readonly List<string!>! AllDecls;
    private readonly List<string!>! IncDecls;

    private readonly IDictionary<Function!, bool>! KnownFunctions;
    private readonly IDictionary<VCExprVar!, bool>! KnownVariables;

    // bitvector types have to be registered as well
    private readonly IDictionary<Type!, bool>! KnownTypes;

    // the names of registered BvConcatOps and BvExtractOps
    private readonly IDictionary<string!, bool>! KnownBvOps;

    private readonly IDictionary<string!, bool>! KnownStoreFunctions;
    private readonly IDictionary<string!, bool>! KnownSelectFunctions;

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
      return SimplifyLikeExprLineariser.TypeToString(t);
    }

    private void RegisterType(Type! type)
    {
      if (KnownTypes.ContainsKey(type)) return;
      
      if (type.IsMap && CommandLineOptions.Clo.UseArrayTheory) {
        KnownTypes.Add(type, true);
        string declString = "";
        MapType! mapType = type.AsMap;
        
        declString += "(DEFTYPE " +  TypeToString(type) + " :BUILTIN Array ";
		foreach (Type! t in mapType.Arguments) {
		  RegisterType(t);
		  declString += TypeToString(t);
		  declString += " ";
		}
		RegisterType(mapType.Result);
		declString += TypeToString(mapType.Result);
		declString += ")";
		AddDeclaration(declString);		
		return;
      }
      
      if (type.IsBv && NativeBv) {
        int bits = type.BvBits;
        string name = TypeToString(type);

        AddDeclaration("(DEFTYPE " + name + " :BUILTIN BitVec " + bits + ")");
        // If we add the BUILTIN then the conversion axiom does not work
        AddDeclaration("(DEFOP " + name + "_to_int " + name + " $int)"); // :BUILTIN bv2int $int)");
        AddDeclaration("(DEFOP $make_bv" + bits + " $int " + name + " :BUILTIN int2bv " + bits + ")");
        string! expr = "($make_bv" + bits + " (" + name + "_to_int  x))";
        AddDeclaration("(BG_PUSH (FORALL (x :TYPE " + name + ") (PATS "
                       + expr + ") (QID bvconv" + bits + ") (EQ " + expr + " x)))");

        KnownTypes.Add(type, true);
      }
    }

    public override bool Visit(VCExprNAry! node, bool arg) {
      // there are a couple cases where operators have to be
      // registered by generating appropriate Z3 statements

      if (node.Op is VCExprBvConcatOp) {
        //
        if (NativeBv) {
          RegisterType(node[0].Type);
          RegisterType(node[1].Type);
          RegisterType(node.Type);

          string name = SimplifyLikeExprLineariser.BvConcatOpName(node);
          if (!KnownBvOps.ContainsKey(name)) {
            AddDeclaration("(DEFOP " + name +
                           " " + TypeToString(node[0].Type) +
                           " " + TypeToString(node[1].Type) +
                           " " + TypeToString(node.Type) +
                           " :BUILTIN concat)");
            KnownBvOps.Add(name, true);
          }
        }
        //
      } else if (node.Op is VCExprBvExtractOp) {
        //
        if (NativeBv) {
          RegisterType(node[0].Type);
          RegisterType(node.Type);

          VCExprBvExtractOp! op = (VCExprBvExtractOp)node.Op;
          string name = SimplifyLikeExprLineariser.BvExtractOpName(node);
          if (!KnownBvOps.ContainsKey(name)) {
            AddDeclaration("(DEFOP " + name +
                           " " + TypeToString(node[0].Type) +
                           " " + TypeToString(node.Type) + 
                           " :BUILTIN extract " +
                           (op.End - 1) + " " + op.Start + ")");
            KnownBvOps.Add(name, true);
          }
        }
        //
      } else if (node.Op is VCExprStoreOp) {
        //
        RegisterType(node[0].Type);
        RegisterType(node[1].Type);
        RegisterType(node[2].Type);
        RegisterType(node.Type);
        string name = SimplifyLikeExprLineariser.StoreOpName(node);
        if (!KnownStoreFunctions.ContainsKey(name)) {
          AddDeclaration("(DEFOP " + name + 
                         " " + TypeToString(node[0].Type) + 
                         " " + TypeToString(node[1].Type) +
                         " " + TypeToString(node[2].Type) + 
                         " " + TypeToString(node.Type) + 
                         " :BUILTIN store)");
          KnownStoreFunctions.Add(name, true);
        }
        //
      } else if (node.Op is VCExprSelectOp) {
        //
        RegisterType(node[0].Type);
        RegisterType(node[1].Type);
        RegisterType(node.Type);
        string name = SimplifyLikeExprLineariser.SelectOpName(node);
        if (!KnownSelectFunctions.ContainsKey(name)) {
          AddDeclaration("(DEFOP " + name + 
                         " " + TypeToString(node[0].Type) + 
                         " " + TypeToString(node[1].Type) +
                         " " + TypeToString(node.Type) + 
                         " :BUILTIN select)");
          KnownSelectFunctions.Add(name, true);
        }
        //
      } else {
        //
        VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
        if (op != null && !KnownFunctions.ContainsKey(op.Func)) {
          Function! f = op.Func;
          string! printedName = Namer.GetName(f, f.Name);
          string! decl = "(DEFOP " + SimplifyLikeExprLineariser.MakeIdPrintable(printedName);

          foreach (Variable! v in f.InParams) {
            decl += " " + TypeToString(v.TypedIdent.Type);
            RegisterType(v.TypedIdent.Type);
          }
          assert f.OutParams.Length == 1;
          foreach (Variable! v in f.OutParams) {
            decl += " " + TypeToString(v.TypedIdent.Type);
            RegisterType(v.TypedIdent.Type);
          }

          string? builtin = ExtractBuiltin(f);
          if (builtin != null)
            decl += " :BUILTIN " + builtin;

          decl += ")";
        
          AddDeclaration(decl);
          KnownFunctions.Add(f, true);
        }
        //
      }

      return base.Visit(node, arg);
    }

    private string? ExtractBuiltin(Function! f) {
      string? retVal = null; 
      if (NativeBv) {
        retVal = f.FindStringAttribute("bvbuiltin");
      } 
      if (retVal == null) {
        retVal = f.FindStringAttribute("builtin");
      }
      return retVal;
    }

    public override bool Visit(VCExprVar! node, bool arg) {
      if (!BoundTermVars.Contains(node) && !KnownVariables.ContainsKey(node)) {
        RegisterType(node.Type);
        string! printedName = Namer.GetName(node, node.Name);
        string! decl =
          "(DEFOP " + SimplifyLikeExprLineariser.MakeIdPrintable(printedName)
          + " " + TypeToString(node.Type) + ")";
        AddDeclaration(decl);
        KnownVariables.Add(node, true);
      }

      return base.Visit(node, arg);
    }
    
    public override bool Visit(VCExprQuantifier! node, bool arg) {
      foreach (VCExprVar! v in node.BoundVars)
        RegisterType(v.Type);
        
      return base.Visit(node, arg);
    } 
  }
}