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

namespace Microsoft.Boogie.Z3
{
  // Visitor for collecting the occurring function symbols in a VCExpr,
  // and for creating the corresponding declarations that can be fed into
  // Z3

  // (should this be rather done by Context.DeclareFunction? right now,
  // the TypeErasure visitor introduces new function symbols that are
  // not passed to this method)

  public class TypeDeclCollector : BoundVarTraversingVCExprVisitor<bool, bool> {

    private readonly UniqueNamer Namer;
    [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(Namer!=null);
      Contract.Invariant(AllDecls != null);
      Contract.Invariant(IncDecls != null);
      Contract.Invariant(cce.NonNullElements(KnownFunctions));
      Contract.Invariant(cce.NonNullElements(KnownVariables));
      Contract.Invariant(cce.NonNullElements(KnownTypes));
      Contract.Invariant(cce.NonNullElements(KnownBvOps));
      Contract.Invariant(cce.NonNullElements(KnownSelectFunctions));
      Contract.Invariant(cce.NonNullElements(KnownStoreFunctions));
}


    private readonly bool NativeBv;

    public TypeDeclCollector(UniqueNamer namer, bool nativeBv) {
      Contract.Requires(namer != null);
      this.Namer = namer;
      this.NativeBv = nativeBv;
      AllDecls = new List<string/*!*/> ();
      IncDecls = new List<string/*!*/> ();
      KnownFunctions = new Dictionary<Function/*!*/, bool> ();
      KnownVariables = new Dictionary<VCExprVar/*!*/, bool> ();
      KnownTypes = new Dictionary<Type/*!*/, bool> ();
      KnownBvOps = new Dictionary<string/*!*/, bool> ();
      
      KnownStoreFunctions = new Dictionary<string/*!*/, bool>();
      KnownSelectFunctions = new Dictionary<string/*!*/, bool>();
    }

    internal TypeDeclCollector(UniqueNamer namer, TypeDeclCollector coll) {
      Contract.Requires(namer!=null);
      Contract.Requires(coll!=null);
      this.Namer = namer;
      this.NativeBv = coll.NativeBv;
      AllDecls = new List<string/*!*/> (coll.AllDecls);
      IncDecls = new List<string/*!*/> (coll.IncDecls);
      KnownFunctions = new Dictionary<Function/*!*/, bool> (coll.KnownFunctions);
      KnownVariables = new Dictionary<VCExprVar/*!*/, bool> (coll.KnownVariables);
      KnownTypes = new Dictionary<Type/*!*/, bool> (coll.KnownTypes);
      KnownBvOps = new Dictionary<string/*!*/, bool> (coll.KnownBvOps);
      
      KnownStoreFunctions = new Dictionary<string/*!*/, bool> (coll.KnownStoreFunctions);
      KnownSelectFunctions = new Dictionary<string/*!*/, bool> (coll.KnownSelectFunctions);
    }

    // not used
    protected override bool StandardResult(VCExpr node, bool arg) {
      Contract.Requires(node != null);
      return true;
    }

    private readonly List<string/*!>!*/> AllDecls;
    private readonly List<string/*!>!*/> IncDecls;

    private readonly IDictionary<Function/*!*/, bool>/*!*/ KnownFunctions;
    private readonly IDictionary<VCExprVar/*!*/, bool>/*!*/ KnownVariables;

    // bitvector types have to be registered as well
    private readonly IDictionary<Type/*!*/, bool>/*!*/ KnownTypes;

    // the names of registered BvConcatOps and BvExtractOps
    private readonly IDictionary<string/*!*/, bool>/*!*/ KnownBvOps;

    private readonly IDictionary<string/*!*/, bool>/*!*/ KnownStoreFunctions;
    private readonly IDictionary<string/*!*/, bool>/*!*/ KnownSelectFunctions;

    public List<string/*!>!*/> AllDeclarations { get {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<string>>()));

      List<string/*!>!*/> res = new List<string/*!*/> ();
      res.AddRange(AllDecls);
      return res;
    } }

    public List<string/*!>!*/> GetNewDeclarations() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<string>>()));
      List<string/*!>!*/> res = new List<string/*!*/> ();
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
      Contract.Requires(t!= null);
      Contract.Ensures(Contract.Result<string>() != null);

      return SimplifyLikeExprLineariser.TypeToString(t);
    }

    private void RegisterType(Type type)
    {
      Contract.Requires(type != null);
      if (KnownTypes.ContainsKey(type)) return;

      if (type.IsMap && CommandLineOptions.Clo.MonomorphicArrays) {
        KnownTypes.Add(type, true);
        string declString = "";
        MapType mapType = type.AsMap;
        Contract.Assert(mapType != null);

        foreach (Type t in mapType.Arguments) {
          Contract.Assert(t != null);
          RegisterType(t);
        }
        RegisterType(mapType.Result);

        declString += "(DEFTYPE " + TypeToString(type);

        if (CommandLineOptions.Clo.UseArrayTheory) {
          declString += " :BUILTIN Array ";
          foreach (Type t in mapType.Arguments) {
            declString += TypeToString(t);
            declString += " ";
          }
          declString += TypeToString(mapType.Result);
        }

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
        string expr = "($make_bv" + bits + " (" + name + "_to_int  x))";
        AddDeclaration("(BG_PUSH (FORALL (x :TYPE " + name + ") (PATS "
                       + expr + ") (QID bvconv" + bits + ") (EQ " + expr + " x)))");

        KnownTypes.Add(type, true);
        return;
      }

      if (type.IsBool || type.IsInt)
        return;

      if (CommandLineOptions.Clo.TypeEncodingMethod == CommandLineOptions.TypeEncoding.Monomorphic) {
        AddDeclaration("(DEFTYPE " + TypeToString(type) + ")");
        KnownTypes.Add(type, true);
        return;
      }

    }

    public override bool Visit(VCExprNAry node, bool arg) {
      Contract.Requires(node != null);
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

          VCExprBvExtractOp op = (VCExprBvExtractOp)node.Op;
          Contract.Assert(op!=null);
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
        RegisterType(node.Type);        // this is the map type, registering it should register also the index and value types
        string name = SimplifyLikeExprLineariser.StoreOpName(node);
        if (!KnownStoreFunctions.ContainsKey(name)) {
          string decl = "(DEFOP " + name;

          foreach (VCExpr ch in node) {
            decl += " " + TypeToString(ch.Type);
          }
          decl += " " + TypeToString(node.Type);

          if (CommandLineOptions.Clo.UseArrayTheory)
            decl += " :BUILTIN store";
          decl += ")";
          AddDeclaration(decl);

          if (CommandLineOptions.Clo.MonomorphicArrays && !CommandLineOptions.Clo.UseArrayTheory) {
            var sel = SimplifyLikeExprLineariser.SelectOpName(node);

            if (!KnownSelectFunctions.ContainsKey(name)) {
              // need to declare it before reference
              string seldecl = "(DEFOP " + sel;
              foreach (VCExpr ch in node) {
                seldecl += " " + TypeToString(ch.Type);
              }
              AddDeclaration(seldecl + ")");
              KnownSelectFunctions.Add(name, true);
            }

            var eq = "EQ";
            if (node[node.Arity - 1].Type.IsBool)
              eq = "IFF";

            string ax1 = "(BG_PUSH (FORALL (";
            string ax2 = "(BG_PUSH (FORALL (";
            string argX = "", argY = "";
            string dist = "";
            for (int i = 0; i < node.Arity; i++) {
              var t = " :TYPE " + TypeToString(node[i].Type);
              var x = " x" + i;
              var y = " y" + i;
              ax1 += x + t;
              ax2 += x + t;
              if (i != 0 && i != node.Arity - 1) {
                argX += x;
                argY += y;
                ax2 += y + t;
                dist += " (NEQ" + x + y + ")";
              }
            }
            string v = " x" + (node.Arity - 1);
            ax1 += ") ";
            ax1 += "(" + eq + " (" + sel + " (" + name + " x0" + argX + v + ")" + argX + ") " + v + ")";
            ax1 += "))";

            ax2 += ") ";
            ax2 += "(IMPLIES (OR " + dist + ") (" + eq + " (" + sel + " (" + name + " x0" + argX + v + ")" + argY + ") (" + sel + " x0" + argY + ")))";
            ax2 += "))";

            AddDeclaration(ax1);
            AddDeclaration(ax2);
          }
          
          KnownStoreFunctions.Add(name, true);
        }
        //
      } else if (node.Op is VCExprSelectOp) {
        //
        RegisterType(node[0].Type);
        string name = SimplifyLikeExprLineariser.SelectOpName(node);
        if (!KnownSelectFunctions.ContainsKey(name)) {
          string decl = "(DEFOP " + name;

          foreach (VCExpr ch in node) {
            decl += " " + TypeToString(ch.Type);
          }
          decl += " " + TypeToString(node.Type);

          if (CommandLineOptions.Clo.UseArrayTheory)
            decl += " :BUILTIN select";
          decl += ")";
          AddDeclaration(decl);
          KnownSelectFunctions.Add(name, true);
        }
        //
      } else {
        //
        VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
        if (op != null && !KnownFunctions.ContainsKey(op.Func)) {
          Function f = op.Func;
          Contract.Assert(f!=null);
          string printedName = Namer.GetName(f, f.Name);
          Contract.Assert(printedName!=null);
          string decl = "(DEFOP " + SimplifyLikeExprLineariser.MakeIdPrintable(printedName);

          foreach (Variable v in f.InParams) {
            Contract.Assert(v!=null);
            decl += " " + TypeToString(v.TypedIdent.Type);
            RegisterType(v.TypedIdent.Type);
          }
         Contract.Assert(f.OutParams.Length == 1);
          foreach (Variable v in f.OutParams) {
            Contract.Assert(v!=null);
            decl += " " + TypeToString(v.TypedIdent.Type);
            RegisterType(v.TypedIdent.Type);
          }

          string builtin = ExtractBuiltin(f);
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

    private string ExtractBuiltin(Function f) {
      Contract.Requires(f != null);
      string retVal = null;
      if (NativeBv) {
        retVal = f.FindStringAttribute("bvbuiltin");
      } 
      if (retVal == null) {
        retVal = f.FindStringAttribute("builtin");
      }
      return retVal;
    }

    public override bool Visit(VCExprVar node, bool arg) {
      Contract.Requires(node != null);
      if (!BoundTermVars.Contains(node) && !KnownVariables.ContainsKey(node)) {
        RegisterType(node.Type);
        string printedName = Namer.GetName(node, node.Name);
        Contract.Assert(printedName!=null);
        string decl =
          "(DEFOP " + SimplifyLikeExprLineariser.MakeIdPrintable(printedName)
          + " " + TypeToString(node.Type) + ")";
        AddDeclaration(decl);
        KnownVariables.Add(node, true);
      }

      return base.Visit(node, arg);
    }
    
    public override bool Visit(VCExprQuantifier node, bool arg) {
      Contract.Requires(node != null);
      foreach (VCExprVar v in node.BoundVars) {
        Contract.Assert(v != null);
        RegisterType(v.Type);
      }
        
      return base.Visit(node, arg);
    } 
  }
}