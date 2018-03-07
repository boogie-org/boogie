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
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;

// Prover-independent syntax trees for representing verification conditions
// The language can be seen as a simple polymorphically typed first-order logic,
// very similar to the expression language of Boogie

namespace Microsoft.Boogie {
  using Microsoft.Boogie.VCExprAST;

  public class VCExpressionGenerator {
    public static readonly VCExpr False = new VCExprLiteral(Type.Bool);
    public static readonly VCExpr True = new VCExprLiteral(Type.Bool);

    private Function ControlFlowFunction = null;
    public VCExpr ControlFlowFunctionApplication(VCExpr e1, VCExpr e2) {
      Contract.Requires(e1 != null);
      Contract.Requires(e2 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      if (ControlFlowFunction == null) {
        Formal/*!*/ first = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Int), true);
        Formal/*!*/ second = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Int), true);
        List<Variable> inputs = new List<Variable>();
        inputs.Add(first);
        inputs.Add(second);
        Formal/*!*/ returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Int), false);
        ControlFlowFunction = new Function(Token.NoToken, "ControlFlow", inputs, returnVar);
      }
      List<VCExpr/*!*/> args = new List<VCExpr/*!*/>();
      args.Add(e1);
      args.Add(e2);
      return Function(BoogieFunctionOp(ControlFlowFunction), args);
    }

    public VCExpr/*!*/ Integer(BigNum x) {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprIntLit(x);
    }

    public VCExpr/*!*/ Real(BigDec x) {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprRealLit(x);
    }

    public VCExpr/*!*/ Float(BigFloat x)
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprFloatLit(x);
    }

    public VCExpr/*!*/ RMode(RoundingMode x)
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprRModeLit(x);
    }

    public VCExpr/*!*/ Function(VCExprOp/*!*/ op,
                            List<VCExpr/*!*/>/*!*/ arguments,
                            List<Type/*!*/>/*!*/ typeArguments) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(cce.NonNullElements(typeArguments));
      if (typeArguments.Count > 0)
        return new VCExprMultiAry(op, arguments, typeArguments);

      switch (arguments.Count) {
        case 0:
          return new VCExprNullary(op);
        case 1:
          return new VCExprUnary(op, arguments);
        case 2:
          return new VCExprBinary(op, arguments);
        default:
          return new VCExprMultiAry(op, arguments);
      }
    }

    public VCExpr/*!*/ Function(VCExprOp/*!*/ op, List<VCExpr/*!*/>/*!*/ arguments) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(op, arguments, VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr/*!*/ Function(VCExprOp/*!*/ op, params VCExpr[]/*!*/ arguments) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(arguments));

      return Function(op,
                      HelperFuns.ToNonNullList(arguments),
                      VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr/*!*/ Function(VCExprOp/*!*/ op, VCExpr[]/*!*/ arguments, Type[]/*!*/ typeArguments) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(cce.NonNullElements(typeArguments));
      Contract.Ensures(Contract.Result<VCExpr>() != null);


      return Function(op,
                      HelperFuns.ToNonNullList(arguments),
                      HelperFuns.ToNonNullList(typeArguments));
    }

    public VCExpr/*!*/ Function(Function/*!*/ op, List<VCExpr/*!*/>/*!*/ arguments) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(BoogieFunctionOp(op), arguments, VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr/*!*/ Function(Function/*!*/ op, params VCExpr[]/*!*/ arguments) {
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(op != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(BoogieFunctionOp(op), arguments);
    }


    // The following method should really be called "ReduceLeft". It must
    // only be used for the binary operators "and" and "or"
    public VCExpr/*!*/ NAry(VCExprOp/*!*/ op, List<VCExpr/*!*/>/*!*/ args) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return NAry(op, args.ToArray());
    }

    public VCExpr/*!*/ NAry(VCExprOp/*!*/ op, params VCExpr[]/*!*/ args) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Requires(op == AndOp || op == OrOp);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      bool and = (op == AndOp);

      VCExpr/*!*/ e = and ? True : False;
      foreach (VCExpr a in args) {
        e = and ? AndSimp(e, cce.NonNull(a)) : OrSimp(e, cce.NonNull(a));
      }
      return e;
    }

    ////////////////////////////////////////////////////////////////////////////////

    public static readonly VCExprOp NotOp = new VCExprNAryOp(1, Type.Bool);
    public static readonly VCExprOp EqOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp NeqOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp AndOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp OrOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp ImpliesOp = new VCExprNAryOp(2, Type.Bool);

    public VCExprDistinctOp DistinctOp(int arity) {
      Contract.Ensures(Contract.Result<VCExprDistinctOp>() != null);

      return new VCExprDistinctOp(arity);
    }

    public VCExpr/*!*/ Not(List<VCExpr/*!*/>/*!*/ args) {
      Contract.Requires(args != null);
      Contract.Requires(args.Count == 1);
      Contract.Requires(args[0] != null);
      return Function(NotOp, args);
    }

    public VCExpr/*!*/ Not(VCExpr/*!*/ e0) {
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(NotOp, e0);
    }
    public VCExpr/*!*/ Eq(VCExpr/*!*/ e0, VCExpr/*!*/ e1) {
      return Function(EqOp, e0, e1);
    }
    public VCExpr/*!*/ Neq(VCExpr/*!*/ e0, VCExpr/*!*/ e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(NeqOp, e0, e1);
    }
    public VCExpr/*!*/ And(VCExpr/*!*/ e0, VCExpr/*!*/ e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(AndOp, e0, e1);
    }
    public VCExpr/*!*/ Gt(VCExpr/*!*/ e0, VCExpr/*!*/ e1)
    {
        Contract.Requires(e0 != null);
        Contract.Requires(e1 != null);
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        return Function(GtOp, e0, e1);
    }
    public VCExpr/*!*/ Add(VCExpr/*!*/ e0, VCExpr/*!*/ e1)
    {
        Contract.Requires(e0 != null);
        Contract.Requires(e1 != null);
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        VCExprOp op = cce.NonNull(cce.NonNull(e0).Type).IsInt ? AddIOp : AddROp;
        return Function(op, e0, e1);
    }
    public VCExpr/*!*/ Or(VCExpr/*!*/ e0, VCExpr/*!*/ e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(OrOp, e0, e1);
    }
    public VCExpr/*!*/ Implies(VCExpr/*!*/ e0, VCExpr/*!*/ e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(ImpliesOp, e0, e1);
    }
    public VCExpr/*!*/ Distinct(List<VCExpr/*!*/>/*!*/ args) {
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      if (args.Count <= 1)
        // trivial case
        return True;
      return Function(DistinctOp(args.Count), args);
    }

    ///////////////////////////////////////////////////////////////////////////
    // Versions of the propositional operators that automatically simplify in
    // certain cases (for example, if one of the operators is True or False)

    public VCExpr NotSimp(VCExpr e0) {
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e0.Equals(True))
        return False;
      if (e0.Equals(False))
        return True;
      return Not(e0);
    }
    public VCExpr AndSimp(VCExpr e0, VCExpr e1) {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e0.Equals(True))
        return e1;
      if (e1.Equals(True))
        return e0;
      if (e0.Equals(False) || e1.Equals(False))
        return False;
      return And(e0, e1);
    }
    public VCExpr OrSimp(VCExpr e0, VCExpr e1) {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e0.Equals(False))
        return e1;
      if (e1.Equals(False))
        return e0;
      if (e0.Equals(True) || e1.Equals(True))
        return True;
      return Or(e0, e1);
    }
    public VCExpr ImpliesSimp(VCExpr e0, VCExpr e1, bool aggressive = true) {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e0.Equals(True))
        return e1;
      if (e1.Equals(False))
        return NotSimp(e0);
      if (e0.Equals(False) || e1.Equals(True))
        return True;
      // attempt to save on the depth of expressions (to reduce chances of stack overflows)
      while (aggressive && e1 is VCExprBinary) {
        VCExprBinary n = (VCExprBinary)e1;
        if (n.Op == ImpliesOp) {
          if (AndSize(n[0]) <= AndSize(e0)) {
            // combine the antecedents
            e0 = And(e0, n[0]);
            e1 = n[1];
            continue;
          }
        }
        break;
      }
      return Implies(e0, e1);
    }

    ///<summary>
    /// Returns some measure of the number of conjuncts in e.  This could be the total number of conjuncts in all
    /// top-most layers of the expression, or it can simply be the length of the left-prong of this and-tree.  The
    /// important thing is that: AndSize(e0) >= AndSize(31) ==> AndSize(And(e0,e1)) > AndSize(e0).
    ///</summary>
    int AndSize(VCExpr e) {
      Contract.Requires(e != null);
      int n = 1;
      while (true) {
        VCExprNAry nary = e as VCExprNAry;
        if (nary != null && nary.Op == AndOp && 2 <= nary.Arity) {
          e = nary[0];
          n++;
        } else {
          return n;
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Further operators

    public static readonly VCExprOp AddIOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp AddROp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp SubIOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp SubROp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp MulIOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp MulROp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp DivIOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp DivROp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp ModOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp PowOp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp LtOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp LeOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp GtOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp GeOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp SubtypeOp = new VCExprNAryOp(2, Type.Bool);
    // ternary version of the subtype operator, the first argument of which gives
    // the type of the compared terms
    public static readonly VCExprOp Subtype3Op = new VCExprNAryOp(3, Type.Bool);
    public static readonly VCExprOp IfThenElseOp = new VCExprIfThenElseOp();
    public static readonly VCExprOp ToIntOp = new VCExprNAryOp(1, Type.Int);
    public static readonly VCExprOp ToRealOp = new VCExprNAryOp(1, Type.Real);

    public static readonly VCExprOp TickleBoolOp = new VCExprCustomOp("tickleBool", 1, Type.Bool);

    public static readonly VCExprOp TimeoutDiagnosticsOp = new VCExprCustomOp("timeoutDiagnostics", 1, Type.Bool);

    public static readonly VCExprOp MinimizeOp = new VCExprCustomOp("minimize##dummy", 2, Type.Bool);
    public static readonly VCExprOp MaximizeOp = new VCExprCustomOp("maximize##dummy", 2, Type.Bool);
    public static readonly VCExprOp NamedAssumeOp = new VCExprCustomOp("named_assume##dummy", 2, Type.Bool);

    public VCExprOp BoogieFunctionOp(Function func) {
      Contract.Requires(func != null);
      Contract.Ensures(Contract.Result<VCExprOp>() != null);
      return new VCExprBoogieFunctionOp(func);
    }

    // Float nodes

    public VCExprOp BinaryFloatOp(int sig, int exp, string op)
    {
      Contract.Requires(exp > 0);
      Contract.Requires(sig > 0);
      Contract.Requires(op != null);
      Contract.Ensures(Contract.Result<VCExprOp>() != null);
      return new VCExprBinaryFloatOp(sig, exp, op);
    }
        
    // Bitvector nodes

    public VCExpr Bitvector(BvConst bv) {
      Contract.Requires(bv != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprBvOp(bv.Bits), Integer(bv.Value));
    }

    public VCExpr BvExtract(VCExpr bv, int bits, int start, int end) {
      Contract.Requires(bv != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprBvExtractOp(start, end, bits), bv);
    }

    public VCExpr BvConcat(VCExpr bv1, VCExpr bv2) {
      Contract.Requires(bv2 != null);
      Contract.Requires(bv1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprBvConcatOp(bv1.Type.BvBits, bv2.Type.BvBits), bv1, bv2);
    }

    public VCExpr AtMost(VCExpr smaller, VCExpr greater) {
      Contract.Requires(greater != null);
      Contract.Requires(smaller != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(SubtypeOp, smaller, greater);
    }


    ////////////////////////////////////////////////////////////////////////////////
    // Dispatcher for the visitor

    // the declared singleton operators
    internal enum SingletonOp {
      NotOp,
      EqOp,
      NeqOp,
      AndOp,
      OrOp,
      ImpliesOp,
      AddOp,
      SubOp,
      MulOp,
      DivOp,
      ModOp,
      RealDivOp,
      PowOp,
      LtOp,
      LeOp,
      GtOp,
      GeOp,
      SubtypeOp,
      Subtype3Op,
      BvConcatOp,
      ToIntOp,
      ToRealOp,
      ToFloatOp
    };
    internal static Dictionary<VCExprOp/*!*/, SingletonOp>/*!*/ SingletonOpDict;
    [ContractInvariantMethod]
    void MiscInvariant() {
      Contract.Invariant(SingletonOpDict != null);
    }


    static VCExpressionGenerator() {
      SingletonOpDict = new Dictionary<VCExprOp/*!*/, SingletonOp>();
      SingletonOpDict.Add(NotOp, SingletonOp.NotOp);
      SingletonOpDict.Add(EqOp, SingletonOp.EqOp);
      SingletonOpDict.Add(NeqOp, SingletonOp.NeqOp);
      SingletonOpDict.Add(AndOp, SingletonOp.AndOp);
      SingletonOpDict.Add(OrOp, SingletonOp.OrOp);
      SingletonOpDict.Add(ImpliesOp, SingletonOp.ImpliesOp);
      SingletonOpDict.Add(AddIOp, SingletonOp.AddOp);
      SingletonOpDict.Add(AddROp, SingletonOp.AddOp);
      SingletonOpDict.Add(SubIOp, SingletonOp.SubOp);
      SingletonOpDict.Add(SubROp, SingletonOp.SubOp);
      SingletonOpDict.Add(MulIOp, SingletonOp.MulOp);
      SingletonOpDict.Add(MulROp, SingletonOp.MulOp);
      SingletonOpDict.Add(DivIOp, SingletonOp.DivOp);
      SingletonOpDict.Add(DivROp, SingletonOp.RealDivOp);
      SingletonOpDict.Add(ModOp, SingletonOp.ModOp);
      SingletonOpDict.Add(PowOp, SingletonOp.PowOp);
      SingletonOpDict.Add(LtOp, SingletonOp.LtOp);
      SingletonOpDict.Add(LeOp, SingletonOp.LeOp);
      SingletonOpDict.Add(GtOp, SingletonOp.GtOp);
      SingletonOpDict.Add(GeOp, SingletonOp.GeOp);
      SingletonOpDict.Add(SubtypeOp, SingletonOp.SubtypeOp);
      SingletonOpDict.Add(Subtype3Op, SingletonOp.Subtype3Op);
      SingletonOpDict.Add(ToIntOp, SingletonOp.ToIntOp);
      SingletonOpDict.Add(ToRealOp, SingletonOp.ToRealOp);
    }

    ////////////////////////////////////////////////////////////////////////////////


    // Let-bindings

    public VCExprLetBinding LetBinding(VCExprVar v, VCExpr e) {
      Contract.Requires(e != null);
      Contract.Requires(v != null);
      Contract.Ensures(Contract.Result<VCExprLetBinding>() != null);
      return new VCExprLetBinding(v, e);
    }

    // A "real" let expression. All let-bindings happen simultaneously, i.e.,
    // at this level the order of the bindings does not matter. It is possible to
    // create expressions like   "let x = y, y = 5 in ...". All bound variables are
    // bound in all bound terms/formulas and can occur there, but the dependencies
    // have to be acyclic
    public VCExpr Let(List<VCExprLetBinding> bindings, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(cce.NonNullElements(bindings));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (bindings.Count == 0)
        // no empty let-bindings
        return body;
      return new VCExprLet(bindings, body);
    }

    public VCExpr Let(VCExpr body, params VCExprLetBinding[] bindings) {
      Contract.Requires(body != null);
      Contract.Requires((cce.NonNullElements(bindings)));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Let(HelperFuns.ToNonNullList(bindings), body);
    }


    /// <summary>
    /// In contrast to the previous method, the following methods are not a general LET.
    ///  Instead, it
    /// is a boolean "LET b = P in Q", where P and Q are predicates, that is allowed to be
    /// encoded as "(b == P) ==> Q" or even as "(P ==> b) ==> Q"
    /// (or "(P ==> b) and Q" in negative positions).
    /// The method assumes that the variables in the bindings are unique in the entire formula
    /// to be produced, which allows the implementation to ignore scope issues in the event that
    /// it needs to generate an alternate expression for LET.
    /// </summary>


    // Turn let-bindings let v = E in ... into implications E ==> v
    public VCExpr AsImplications(List<VCExprLetBinding> bindings) {
      Contract.Requires(cce.NonNullElements(bindings));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr/*!*/ antecedents = True;
      foreach (VCExprLetBinding b in bindings)
        // turn "LET_binding v = E" into "v <== E"
        antecedents = AndSimp(antecedents, Implies(b.E, b.V));
      return antecedents;
    }

    // Turn let-bindings let v = E in ... into equations v == E
    public VCExpr AsEquations(List<VCExprLetBinding> bindings) {
      Contract.Requires(cce.NonNullElements(bindings));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr/*!*/ antecedents = True;
      foreach (VCExprLetBinding b in bindings)
        // turn "LET_binding v = E" into "v <== E"
        antecedents = AndSimp(antecedents, Eq(b.E, b.V));
      return antecedents;
    }



    // Maps

    public VCExpr Select(params VCExpr[] allArgs) {
      Contract.Requires(allArgs != null);
      Contract.Requires((cce.NonNullElements(allArgs)));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprSelectOp(allArgs.Length - 1, 0),
                      HelperFuns.ToNonNullList(allArgs),
                      VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr Select(VCExpr[] allArgs, Type[] typeArgs) {
      Contract.Requires(1 <= allArgs.Length);
      Contract.Requires(cce.NonNullElements(allArgs));
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprSelectOp(allArgs.Length - 1, typeArgs.Length),
                      allArgs, typeArgs);
    }

    public VCExpr Select(List<VCExpr> allArgs, List<Type> typeArgs) {
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(allArgs));
      Contract.Requires((1 <= allArgs.Count));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprSelectOp(allArgs.Count - 1, typeArgs.Count),
                      allArgs, typeArgs);
    }

    public VCExpr Store(params VCExpr[] allArgs) {
      Contract.Requires(allArgs != null);
      Contract.Requires(cce.NonNullElements(allArgs));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprStoreOp(allArgs.Length - 2, 0),
                      HelperFuns.ToNonNullList(allArgs),
                      VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr Store(VCExpr[] allArgs, Type[] typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(allArgs != null);
      Contract.Requires((2 <= allArgs.Length));
      Contract.Requires(cce.NonNullElements(allArgs));
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprStoreOp(allArgs.Length - 2, typeArgs.Length),
                      allArgs, typeArgs);
    }

    public VCExpr Store(List<VCExpr> allArgs, List<Type/*!*/>/*!*/ typeArgs) {
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(allArgs));
      Contract.Requires((2 <= allArgs.Count));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprStoreOp(allArgs.Count - 2, typeArgs.Count),
                      allArgs, typeArgs);
    }


    // Labels

    public VCExprLabelOp LabelOp(bool pos, string l) {
      Contract.Requires(l != null);
      Contract.Ensures(Contract.Result<VCExprLabelOp>() != null);
      return new VCExprLabelOp(pos, l);
    }

    public VCExpr LabelNeg(string label, VCExpr e) {
      Contract.Requires(e != null);
      Contract.Requires(label != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e.Equals(True)) {
        return e;  // don't bother putting negative labels around True (which will expose the True to further peephole optimizations)
      }
      return Function(LabelOp(false, label), e);
    }
    public VCExpr LabelPos(string label, VCExpr e) {
      Contract.Requires(e != null);
      Contract.Requires(label != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(LabelOp(true, label), e);
    }

    // Quantifiers

    public VCExpr Quantify(Quantifier quan, List<TypeVariable/*!*/>/*!*/ typeParams, List<VCExprVar/*!*/>/*!*/ vars, List<VCTrigger/*!*/>/*!*/ triggers, VCQuantifierInfos infos, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(infos != null);
      Contract.Requires(cce.NonNullElements(triggers));
      Contract.Requires(cce.NonNullElements(vars));
      Contract.Requires(cce.NonNullElements(typeParams));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return new VCExprQuantifier(quan, typeParams, vars, triggers, infos, body);
    }

    public VCExpr Forall(List<TypeVariable/*!*/>/*!*/ typeParams, List<VCExprVar/*!*/>/*!*/ vars, List<VCTrigger/*!*/>/*!*/ triggers, VCQuantifierInfos infos, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(infos != null);
      Contract.Requires(cce.NonNullElements(triggers));
      Contract.Requires(cce.NonNullElements(vars));
      Contract.Requires(cce.NonNullElements(typeParams));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.ALL, typeParams, vars, triggers, infos, body);
    }
    public VCExpr Forall(List<VCExprVar/*!*/>/*!*/ vars, List<VCTrigger/*!*/>/*!*/ triggers, string qid, int weight, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(qid != null);
      Contract.Requires(cce.NonNullElements(triggers));
      Contract.Requires(cce.NonNullElements(vars));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      QKeyValue kv = null;
      if (0 <= weight) {
        kv = new QKeyValue(Token.NoToken, "weight", new List<object>() { new LiteralExpr(Token.NoToken, BigNum.FromInt(0)) }, null);
      }
      return Quantify(Quantifier.ALL, new List<TypeVariable/*!*/>(), vars,
                            triggers, new VCQuantifierInfos(qid, -1, false, kv), body);
    }
    public VCExpr Forall(List<VCExprVar/*!*/>/*!*/ vars, List<VCTrigger/*!*/>/*!*/ triggers, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(cce.NonNullElements(triggers));
      Contract.Requires(cce.NonNullElements(vars));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.ALL, new List<TypeVariable/*!*/>(), vars,
                            triggers, new VCQuantifierInfos(null, -1, false, null), body);
    }
    public VCExpr Forall(VCExprVar var, VCTrigger trigger, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(trigger != null);
      Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Forall(HelperFuns.ToNonNullList(var), HelperFuns.ToNonNullList(trigger), body);
    }
    public VCExpr Exists(List<TypeVariable/*!*/>/*!*/ typeParams, List<VCExprVar/*!*/>/*!*/ vars, List<VCTrigger/*!*/>/*!*/ triggers, VCQuantifierInfos infos, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(infos != null);
      Contract.Requires(cce.NonNullElements(triggers));
      Contract.Requires(cce.NonNullElements(vars));
      Contract.Requires(cce.NonNullElements(typeParams));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.EX, typeParams, vars, triggers, infos, body);
    }
    public VCExpr Exists(List<VCExprVar/*!*/>/*!*/ vars, List<VCTrigger/*!*/>/*!*/ triggers, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(cce.NonNullElements(triggers));
      Contract.Requires(cce.NonNullElements(vars));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.EX, new List<TypeVariable/*!*/>(), vars,
                      triggers, new VCQuantifierInfos(null, -1, false, null), body);
    }
    public VCExpr Exists(VCExprVar var, VCTrigger trigger, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(trigger != null);
      Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Exists(HelperFuns.ToNonNullList(var), HelperFuns.ToNonNullList(trigger), body);
    }

    public VCTrigger Trigger(bool pos, List<VCExpr> exprs) {
      Contract.Requires(cce.NonNullElements(exprs));
      Contract.Ensures(Contract.Result<VCTrigger>() != null);
      return new VCTrigger(pos, exprs);
    }

    public VCTrigger Trigger(bool pos, params VCExpr[] exprs) {
      Contract.Requires(exprs != null);
      Contract.Requires((Contract.ForAll(0, exprs.Length, i => exprs[i] != null)));
      Contract.Ensures(Contract.Result<VCTrigger>() != null);
      return Trigger(pos, HelperFuns.ToNonNullList(exprs));
    }

    // Reference to a bound or free variable

    public VCExprVar Variable(string name, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<VCExprVar>() != null);
      return new VCExprVar(name, type);
    }
  }
}

namespace Microsoft.Boogie.VCExprAST {

  public class HelperFuns {
    public static bool SameElements(IEnumerable a, IEnumerable b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      IEnumerator ia = a.GetEnumerator();
      IEnumerator ib = b.GetEnumerator();
      while (true) {
        if (ia.MoveNext()) {
          if (ib.MoveNext()) {
            if (!cce.NonNull(ia.Current).Equals(ib.Current))
              return false;
          } else {
            return false;
          }
        } else {
          return !ib.MoveNext();
        }
      }
    }

    public static int PolyHash(int init, int factor, IEnumerable a) {
      Contract.Requires(a != null);
      int res = init;
      foreach (object x in a)
        res = res * factor + (cce.NonNull(x)).GetHashCode();
      return res;
    }

    public static List<T> ToList<T>(IEnumerable<T> l) {
      Contract.Requires(l != null);
      Contract.Ensures(Contract.Result<List<T>>() != null);
      List<T>/*!*/ res = new List<T>();
      foreach (T x in l)
        res.Add(x);
      return res;
    }

    public static List<Type> ToTypeSeq(VCExpr[] exprs, int startIndex) {
      Contract.Requires(exprs != null);
      Contract.Requires((Contract.ForAll(0, exprs.Length, i => exprs[i] != null)));
      Contract.Ensures(Contract.Result<List<Type>>() != null);
      List<Type>/*!*/ res = new List<Type>();
      for (int i = startIndex; i < exprs.Length; ++i)
        res.Add(cce.NonNull(exprs[i]).Type);
      return res;
    }

    public static List<T/*!*/>/*!*/ ToNonNullList<T>(params T[] args) where T : class {
      Contract.Requires(args != null);
      List<T/*!*/>/*!*/ res = new List<T>(args.Length);
      foreach (T t in args)
        res.Add(cce.NonNull(t));
      return res;
    }

    public static IDictionary<A, B> Clone<A, B>(IDictionary<A, B> dict) {
      Contract.Requires(dict != null);
      Contract.Ensures(Contract.Result<IDictionary<A, B>>() != null);
      IDictionary<A, B> res = new Dictionary<A, B>(dict.Count);
      foreach (KeyValuePair<A, B> pair in dict)
        res.Add(pair);
      return res;
    }
  }

  [ContractClassFor(typeof(VCExpr))]
  public abstract class VCExprContracts : VCExpr {
    public override Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();
      }

    }
    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg) {
      Contract.Requires(visitor != null);
      throw new NotImplementedException();
    }
  }

  [ContractClass(typeof(VCExprContracts))]
  public abstract class VCExpr {
    public abstract Type Type {
      get;
    }

    public abstract Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg);

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      StringWriter sw = new StringWriter();
      VCExprPrinter printer = new VCExprPrinter();
      printer.Print(this, sw);
      return cce.NonNull(sw.ToString());
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Literal expressions

  public class VCExprLiteral : VCExpr {
    private readonly Type LitType;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(LitType != null);
    }

    public override Type Type {
      get {
        return LitType;
      }
    }
    internal VCExprLiteral(Type type) {
      Contract.Requires(type != null);
      this.LitType = type;
    }
    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
  }

  public class VCExprIntLit : VCExprLiteral {
    public readonly BigNum Val;
    internal VCExprIntLit(BigNum val)
      : base(Type.Int) {
      this.Val = val;
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprIntLit)
        return Val == ((VCExprIntLit)that).Val;
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Val.GetHashCode() * 72321;
    }
  }

  public class VCExprRealLit : VCExprLiteral {
    public readonly BigDec Val;
    internal VCExprRealLit(BigDec val)
      : base(Type.Real) {
      this.Val = val;
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprRealLit)
        return Val == ((VCExprRealLit)that).Val;
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Val.GetHashCode() * 72321;
    }
  }

  public class VCExprFloatLit : VCExprLiteral
  {
    public readonly BigFloat Val;
    internal VCExprFloatLit(BigFloat val)
      : base(Type.GetFloatType(val.SignificandSize, val.ExponentSize))
    {
      this.Val = val;
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprFloatLit)
        return Val == ((VCExprFloatLit)that).Val;
      return false;
    }
    [Pure]
    public override int GetHashCode()
    {
      return Val.GetHashCode() * 72321;
    }
  }

  public class VCExprRModeLit : VCExprLiteral
  {
    public readonly RoundingMode Val;
    internal VCExprRModeLit(RoundingMode val)
      : base(Type.RMode)
    {
      this.Val = val;
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprRModeLit)
        return Val == ((VCExprRModeLit)that).Val;
      return false;
    }
    [Pure]
    public override int GetHashCode()
    {
      return Val.GetHashCode() * 72321;
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Operator expressions with fixed arity
  [ContractClassFor(typeof(VCExprNAry))]
  public abstract class VCExprNAryContracts : VCExprNAry {
    public VCExprNAryContracts()
      : base(null) {
    }
    public override VCExpr this[int index] {
      get {
        Contract.Ensures(Contract.Result<VCExpr>() != null);
        throw new NotImplementedException();
      }
    }
  }

  [ContractClass(typeof(VCExprNAryContracts))]
  public abstract class VCExprNAry : VCExpr, IEnumerable<VCExpr/*!*/> {
    public readonly VCExprOp Op;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Op != null);
      Contract.Invariant(cce.NonNullElements(EMPTY_TYPE_LIST));
      Contract.Invariant(cce.NonNullElements(EMPTY_VCEXPR_LIST));
    }

    public int Arity {
      get {
        return Op.Arity;
      }
    }
    public int TypeParamArity {
      get {
        return Op.TypeParamArity;
      }
    }
    public int Length {
      get {
        return Arity;
      }
    }
    // the sub-expressions of the expression
    public abstract VCExpr/*!*/ this[int index] {
      get;
    }

    // the type arguments
    public abstract List<Type/*!*/>/*!*/ TypeArguments {
      get;
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    public IEnumerator<VCExpr/*!*/>/*!*/ GetEnumerator() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerator<VCExpr>>()));
      for (int i = 0; i < Arity; ++i)
        yield return this[i];
    }
    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IEnumerator System.Collections.IEnumerable.GetEnumerator() {
      Contract.Ensures(Contract.Result<IEnumerator>() != null);
      for (int i = 0; i < Arity; ++i)
        yield return this[i];
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprNAry) {
        // we compare the subterms iteratively (not recursively)
        // to avoid stack overflows

        VCExprNAryEnumerator enum0 = new VCExprNAryEnumerator(this);
        VCExprNAryEnumerator enum1 = new VCExprNAryEnumerator((VCExprNAry)that);

        while (true) {
          bool next0 = enum0.MoveNext();
          bool next1 = enum1.MoveNext();
          if (next0 != next1)
            return false;
          if (!next0)
            return true;

          VCExprNAry nextExprNAry0 = enum0.Current as VCExprNAry;
          VCExprNAry nextExprNAry1 = enum1.Current as VCExprNAry;

          if ((nextExprNAry0 == null) != (nextExprNAry1 == null))
            return false;
          if (nextExprNAry0 != null && nextExprNAry1 != null) {
            if (!nextExprNAry0.Op.Equals(nextExprNAry1.Op))
              return false;
          } else {
            if (!cce.NonNull(enum0.Current).Equals(enum1.Current))
              return false;
          }
        }
      }
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return HelperFuns.PolyHash(Op.GetHashCode() * 123 + Arity * 61521,
                                 3, this);
    }

    internal VCExprNAry(VCExprOp op) {
      Contract.Requires(op != null);
      this.Op = op;
    }
    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
    public Result Accept<Result, Arg>(IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      Contract.Requires(visitor != null);
      return Op.Accept(this, visitor, arg);
    }

    internal static readonly List<Type/*!*/>/*!*/ EMPTY_TYPE_LIST = new List<Type/*!*/>();
    internal static readonly List<VCExpr/*!*/>/*!*/ EMPTY_VCEXPR_LIST = new List<VCExpr/*!*/>();

    public IEnumerable<VCExpr> UniformArguments
    {
      get
      {
        var enumerator = new VCExprNAryUniformOpEnumerator(this);
        while (enumerator.MoveNext()) {
          VCExprNAry naryExpr = enumerator.Current as VCExprNAry;
          if (naryExpr == null || !naryExpr.Op.Equals(this.Op)) {
            yield return (VCExpr)enumerator.Current;
          }
        }
      }
    }
  }

  // We give specialised implementations for nullary, unary and binary expressions

  internal class VCExprNullary : VCExprNAry {
    private readonly Type ExprType;
    [ContractInvariantMethod]
    void loneinvariant() {
      Contract.Invariant(ExprType != null);
    }

    public override Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return ExprType;
      }
    }
    public override VCExpr this[int index] {
      get {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        Contract.Assert(false);
        throw new cce.UnreachableException(); // no arguments
      }
    }

    // the type arguments
    public override List<Type/*!*/>/*!*/ TypeArguments {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Type>>()));
        return EMPTY_TYPE_LIST;
      }
    }

    internal VCExprNullary(VCExprOp op)
      : base(op) {
      Contract.Requires(op != null);
      Contract.Requires(op.Arity == 0 && op.TypeParamArity == 0);
      this.ExprType = op.InferType(EMPTY_VCEXPR_LIST, EMPTY_TYPE_LIST);
    }
  }

  internal class VCExprUnary : VCExprNAry {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Argument != null);
      Contract.Invariant(ExprType != null);

    }

    private readonly VCExpr/*!*/ Argument;
    private readonly Type/*!*/ ExprType;
    public override Type/*!*/ Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return ExprType;
      }
    }
    public override VCExpr/*!*/ this[int index] {
      get {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        Contract.Assume(index == 0);
        return Argument;
      }
    }

    // the type arguments
    public override List<Type/*!*/>/*!*/ TypeArguments {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Type>>()));
        return EMPTY_TYPE_LIST;
      }
    }

    internal VCExprUnary(VCExprOp op, List<VCExpr> arguments)
      : base(op) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(op.Arity == 1 && op.TypeParamArity == 0 && arguments.Count == 1);

      this.Argument = arguments[0];
      this.ExprType =
        op.InferType(arguments, EMPTY_TYPE_LIST);
    }

    internal VCExprUnary(VCExprOp op, VCExpr argument)
      : base(op) {
      Contract.Requires(argument != null);
      Contract.Requires(op != null);
      Contract.Requires(op.Arity == 1 && op.TypeParamArity == 0);

      this.Argument = argument;
      // PR: could be optimised so that the argument does
      // not have to be boxed in an array each time
      this.ExprType =
        op.InferType(HelperFuns.ToNonNullList(argument), EMPTY_TYPE_LIST);
    }
  }

  internal class VCExprBinary : VCExprNAry {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Argument0 != null);
      Contract.Invariant(Argument1 != null);
      Contract.Invariant(ExprType != null);
    }

    private readonly VCExpr Argument0;
    private readonly VCExpr Argument1;
    private readonly Type ExprType;
    public override Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return ExprType;
      }
    }
    public override VCExpr this[int index] {
      get {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        switch (index) {
          case 0:
            return Argument0;
          case 1:
            return Argument1;
          default: {
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }
        }
      }
    }

    // the type arguments
    public override List<Type/*!*/>/*!*/ TypeArguments {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Type>>()));
        return EMPTY_TYPE_LIST;
      }
    }

    internal VCExprBinary(VCExprOp op, List<VCExpr> arguments)
      : base(op) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(op.Arity == 2 && op.TypeParamArity == 0 && arguments.Count == 2);

      this.Argument0 = arguments[0];
      this.Argument1 = arguments[1];
      this.ExprType = op.InferType(arguments, EMPTY_TYPE_LIST);
    }

    internal VCExprBinary(VCExprOp op, VCExpr argument0, VCExpr argument1)
      : base(op) {
      Contract.Requires(argument1 != null);
      Contract.Requires(argument0 != null);
      Contract.Requires(op != null);
      Contract.Requires(op.Arity == 2 && op.TypeParamArity == 0);
      this.Argument0 = argument0;
      this.Argument1 = argument1;
      // PR: could be optimised so that the arguments do
      // not have to be boxed in an array each time
      this.ExprType =
        op.InferType(HelperFuns.ToNonNullList(argument0, argument1),
                     EMPTY_TYPE_LIST);
    }
  }

  internal class VCExprMultiAry : VCExprNAry {
    private readonly List<VCExpr/*!*/>/*!*/ Arguments;
    private readonly List<Type/*!*/>/*!*/ TypeArgumentsAttr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Arguments));
      Contract.Invariant(cce.NonNullElements(TypeArgumentsAttr));
      Contract.Invariant(ExprType != null);
    }


    private readonly Type/*!*/ ExprType;
    public override Type/*!*/ Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return ExprType;
      }
    }
    public override VCExpr/*!*/ this[int index] {
      get {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        Contract.Assume(index >= 0 && index < Arity);
        return cce.NonNull(Arguments)[index];
      }
    }

    // the type arguments
    public override List<Type/*!*/>/*!*/ TypeArguments {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Type>>()));
        return TypeArgumentsAttr;
      }
    }

    internal VCExprMultiAry(VCExprOp op, List<VCExpr> arguments)
      : base(op) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(arguments));
      this.Arguments = arguments;
      this.TypeArgumentsAttr = EMPTY_TYPE_LIST;
      this.ExprType = op.InferType(arguments, TypeArgumentsAttr);
    }
    internal VCExprMultiAry(VCExprOp op, List<VCExpr> arguments, List<Type/*!*/>/*!*/ typeArguments)
      : base(op) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(typeArguments));
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(arguments.Count > 2 || typeArguments.Count > 0);
      Contract.Requires(op.Arity == arguments.Count);
      Contract.Requires(op.TypeParamArity == typeArguments.Count);
      this.Arguments = arguments;
      this.TypeArgumentsAttr = typeArguments;
      this.ExprType = op.InferType(arguments, typeArguments);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // The various operators available
  [ContractClass(typeof(VCExprOpContracts))]
  public abstract class VCExprOp {
    // the number of value parameters
    public abstract int Arity {
      get;
    }
    // the number of type parameters
    public abstract int TypeParamArity {
      get;
    }

    public abstract Type/*!*/ InferType(List<VCExpr/*!*/>/*!*/ args, List<Type/*!*/>/*!*/ typeArgs);

    public virtual Result Accept<Result, Arg>(VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      Contract.Requires(visitor != null);
      Contract.Requires(expr != null);
      VCExpressionGenerator.SingletonOp op;
      if (VCExpressionGenerator.SingletonOpDict.TryGetValue(this, out op)) {
        switch (op) {
          case VCExpressionGenerator.SingletonOp.NotOp:
            return visitor.VisitNotOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.EqOp:
            return visitor.VisitEqOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.NeqOp:
            return visitor.VisitNeqOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.AndOp:
            return visitor.VisitAndOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.OrOp:
            return visitor.VisitOrOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.ImpliesOp:
            return visitor.VisitImpliesOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.AddOp:
            return visitor.VisitAddOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.SubOp:
            return visitor.VisitSubOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.MulOp:
            return visitor.VisitMulOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.DivOp:
            return visitor.VisitDivOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.ModOp:
            return visitor.VisitModOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.RealDivOp:
            return visitor.VisitRealDivOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.PowOp:
            return visitor.VisitPowOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.LtOp:
            return visitor.VisitLtOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.LeOp:
            return visitor.VisitLeOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.GtOp:
            return visitor.VisitGtOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.GeOp:
            return visitor.VisitGeOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.SubtypeOp:
            return visitor.VisitSubtypeOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.Subtype3Op:
            return visitor.VisitSubtype3Op(expr, arg);
          case VCExpressionGenerator.SingletonOp.BvConcatOp:
            return visitor.VisitBvConcatOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.ToIntOp:
            return visitor.VisitToIntOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.ToRealOp:
            return visitor.VisitToRealOp(expr, arg);
          default:
            Contract.Assert(false);
            throw new cce.UnreachableException();
        }
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }
  }
  [ContractClassFor(typeof(VCExprOp))]
  abstract class VCExprOpContracts : VCExprOp {
    public override Type InferType(List<VCExpr> args, List<Type> typeArgs) {
      Contract.Requires(cce.NonNullElements(args));
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }
  }

  public class VCExprNAryOp : VCExprOp {
    private readonly Type OpType;
    private readonly int OpArity;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(OpType != null);
    }

    public override int Arity {
      get {
        return OpArity;
      }
    }
    public override int TypeParamArity {
      get {
        return 0;
      }
    }
    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return OpType;
    }

    internal VCExprNAryOp(int arity, Type type) {
      Contract.Requires(type != null);
      this.OpArity = arity;
      this.OpType = type;
    }
  }

  public class VCExprDistinctOp : VCExprNAryOp {
    internal VCExprDistinctOp(int arity)
      : base(arity, Type.Bool) {
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprDistinctOp)
        return Arity == ((VCExprDistinctOp)that).Arity;
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Arity * 917632481;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitDistinctOp(expr, arg);
    }
  }

  public class VCExprLabelOp : VCExprOp {
    public override int Arity {
      get {
        return 1;
      }
    }
    public override int TypeParamArity {
      get {
        return 0;
      }
    }
    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return args[0].Type;
    }

    public readonly bool pos;
    public readonly string label;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(label != null);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprLabelOp) {
        VCExprLabelOp/*!*/ thatOp = (VCExprLabelOp)that;
        return this.pos == thatOp.pos && this.label.Equals(thatOp.label);
      }
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return (pos ? 9817231 : 7198639) + label.GetHashCode();
    }

    internal VCExprLabelOp(bool pos, string l) {
      Contract.Requires(l != null);
      this.pos = pos;
      this.label = pos ? "+" + l : "@" + l;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitLabelOp(expr, arg);
    }
  }

  public class VCExprSelectOp : VCExprOp {
    private readonly int MapArity;
    private readonly int MapTypeParamArity;
    public override int Arity {
      get {
        return MapArity + 1;
      }
    }
    public override int TypeParamArity {
      get {
        return MapTypeParamArity;
      }
    }

    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      MapType/*!*/ mapType = args[0].Type.AsMap;
      Contract.Assert(TypeParamArity == mapType.TypeParameters.Count);
      IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ subst = new Dictionary<TypeVariable/*!*/, Type/*!*/>();
      for (int i = 0; i < TypeParamArity; ++i)
        subst.Add(mapType.TypeParameters[i], typeArgs[i]);
      return mapType.Result.Substitute(subst);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprSelectOp)
        return Arity == ((VCExprSelectOp)that).Arity &&
          TypeParamArity == ((VCExprSelectOp)that).TypeParamArity;
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Arity * 1212481 + TypeParamArity * 298741;
    }

    internal VCExprSelectOp(int arity, int typeParamArity) {
      Contract.Requires(0 <= arity && 0 <= typeParamArity);
      this.MapArity = arity;
      this.MapTypeParamArity = typeParamArity;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitSelectOp(expr, arg);
    }
  }

  public class VCExprStoreOp : VCExprOp {
    private readonly int MapArity;
    private readonly int MapTypeParamArity;
    public override int Arity {
      get {
        return MapArity + 2;
      }
    }
    // stores never need explicit type parameters, because also the
    // rhs is a value argument
    public override int TypeParamArity {
      get {
        return MapTypeParamArity;
      }
    }

    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return args[0].Type;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprStoreOp)
        return Arity == ((VCExprStoreOp)that).Arity;
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Arity * 91361821;
    }

    internal VCExprStoreOp(int arity, int typeParamArity) {
      Contract.Requires(0 <= arity && 0 <= typeParamArity);
      this.MapArity = arity;
      this.MapTypeParamArity = typeParamArity;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitStoreOp(expr, arg);
    }
  }

  public class VCExprIfThenElseOp : VCExprOp {
    public override int Arity {
      get {
        return 3;
      }
    }
    public override int TypeParamArity {
      get {
        return 0;
      }
    }
    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return args[1].Type;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprIfThenElseOp)
        return true;
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return 1;
    }

    internal VCExprIfThenElseOp() {
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitIfThenElseOp(expr, arg);
    }
  }

  public class VCExprSoftOp : VCExprCustomOp
  {
    public readonly int Weight;

    public VCExprSoftOp(int weight) : base("soft##dummy", 2, Microsoft.Boogie.Type.Bool)
    {
      Weight = weight;
    }
  }

  public class VCExprCustomOp : VCExprOp {
    public readonly string/*!*/ Name;
    int arity;
    public readonly Type/*!*/ Type;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(Type != null);
    }

    public VCExprCustomOp(string/*!*/ name, int arity, Type/*!*/ type) {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.Name = name;
      this.arity = arity;
      this.Type = type;
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      VCExprCustomOp t = that as VCExprCustomOp;
      if (t == null)
        return false;
      return this.Name == t.Name && this.arity == t.arity && this.Type == t.Type;
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override int GetHashCode() {
      int h = Name.GetHashCode();
      h = 7823 * h + arity;
      h = 7823 * h + Type.GetHashCode();
      return h;
    }
    public override int Arity {
      get {
        return arity;
      }
    }
    public override int TypeParamArity {
      get {
        return 0;
      }
    }
    public override Type/*!*/ InferType(List<VCExpr/*!*/>/*!*/ args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires((cce.NonNullElements(args)));
      //Contract.Requires((cce.NonNullElements(typeArgs)));
      Contract.Ensures(Contract.Result<Type>() != null);
      return Type;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry/*!*/ expr, IVCExprOpVisitor<Result, Arg>/*!*/ visitor, Arg arg) {
      //Contract.Requires(expr != null);
      //Contract.Requires(visitor != null);
      return visitor.VisitCustomOp(expr, arg);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Float operators

  public class VCExprBinaryFloatOp : VCExprOp {
    public readonly int Significand;
    public readonly int Exponent;
    private string op;

    public override int Arity {
      get {
        return 2;
      }
    }
    public override int TypeParamArity {
      get {
        return 2;
      }
    }
    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      switch (op)
      {
        case ("+"):
        case ("-"):
        case ("*"):
        case ("/"):
          return Type.GetFloatType(Significand, Exponent);
        case ("<="):
        case ("<"):
        case (">="):
        case (">"):
        case ("=="):
        case ("!="):
          return Type.Bool;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprBinaryFloatOp)
        return this.Exponent == ((VCExprBinaryFloatOp)that).Exponent && this.Significand == ((VCExprBinaryFloatOp)that).Significand;
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Exponent * 81748912 + Significand * 67867979;
    }

    internal VCExprBinaryFloatOp(int sig, int exp, string op) {
      this.Exponent = exp;
      this.Significand = sig;
      this.op = op;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      switch (op) { 
      case ("+"):
        return visitor.VisitFloatAddOp(expr, arg);
      case ("-"):
        return visitor.VisitFloatSubOp(expr, arg);
      case ("*"):
        return visitor.VisitFloatMulOp(expr, arg);
      case ("/"):
        return visitor.VisitFloatDivOp(expr, arg);
      case ("<="):
        return visitor.VisitFloatLeqOp(expr, arg);
      case ("<"):
        return visitor.VisitFloatLtOp(expr, arg);
      case (">="):
        return visitor.VisitFloatGeqOp(expr, arg);
      case (">"):
        return visitor.VisitFloatGtOp(expr, arg);
      case ("=="):
        return visitor.VisitEqOp(expr, arg);
      case ("!="):
        return visitor.VisitNeqOp(expr, arg);
      default:
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Bitvector operators

  public class VCExprBvOp : VCExprOp {
    public readonly int Bits;

    public override int Arity {
      get {
        return 1;
      }
    }
    public override int TypeParamArity {
      get {
        return 0;
      }
    }
    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return Type.GetBvType(Bits);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprBvOp)
        return this.Bits == ((VCExprBvOp)that).Bits;
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Bits * 81748912;
    }

    internal VCExprBvOp(int bits) {
      this.Bits = bits;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitBvOp(expr, arg);
    }
  }

  public class VCExprBvExtractOp : VCExprOp {
    public readonly int Start;
    public readonly int End;
    public readonly int Total;  // the number of bits from which the End-Start bits are extracted

    public override int Arity {
      get {
        return 1;
      }
    }
    public override int TypeParamArity {
      get {
        return 0;
      }
    }
    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return Type.GetBvType(End - Start);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprBvExtractOp) {
        VCExprBvExtractOp/*!*/ thatExtract = (VCExprBvExtractOp)that;
        return this.Start == thatExtract.Start && this.End == thatExtract.End && this.Total == thatExtract.Total;
      }
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Start * 81912 + End * 978132 + Total * 571289;
    }

    internal VCExprBvExtractOp(int start, int end, int total) {
      Contract.Requires(0 <= start && start <= end && end <= total);
      this.Start = start;
      this.End = end;
      this.Total = total;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitBvExtractOp(expr, arg);
    }
  }

  public class VCExprBvConcatOp : VCExprOp {
    public readonly int LeftSize;
    public readonly int RightSize;

    public override int Arity {
      get {
        return 2;
      }
    }
    public override int TypeParamArity {
      get {
        return 0;
      }
    }
    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return Type.GetBvType(args[0].Type.BvBits + args[1].Type.BvBits);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprBvConcatOp) {
        VCExprBvConcatOp thatConcat = (VCExprBvConcatOp)that;
        return this.LeftSize == thatConcat.LeftSize && this.RightSize == thatConcat.RightSize;
      }
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return LeftSize * 81912 + RightSize * 978132;
    }

    internal VCExprBvConcatOp(int leftSize, int rightSize) {
      Contract.Requires(0 <= leftSize && 0 <= rightSize);
      this.LeftSize = leftSize;
      this.RightSize = rightSize;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitBvConcatOp(expr, arg);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // References to user-defined Boogie functions

  public class VCExprBoogieFunctionOp : VCExprOp {
    public readonly Function Func;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Func != null);
    }


    public override int Arity {
      get {
        return Func.InParams.Count;
      }
    }
    public override int TypeParamArity {
      get {
        return Func.TypeParameters.Count;
      }
    }
    public override Type InferType(List<VCExpr> args, List<Type/*!*/>/*!*/ typeArgs) {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Assert(TypeParamArity == Func.TypeParameters.Count);
      if (TypeParamArity == 0)
        return cce.NonNull(Func.OutParams[0]).TypedIdent.Type;
      IDictionary<TypeVariable/*!*/, Type/*!*/>/*!*/ subst = new Dictionary<TypeVariable/*!*/, Type/*!*/>(TypeParamArity);
      for (int i = 0; i < TypeParamArity; ++i)
        subst.Add(Func.TypeParameters[i], typeArgs[i]);
      return cce.NonNull(Func.OutParams[0]).TypedIdent.Type.Substitute(subst);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprBoogieFunctionOp)
        return this.Func.Equals(((VCExprBoogieFunctionOp)that).Func);
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Func.GetHashCode() + 18731;
    }

    // we require that the result type of the expression is specified, because we
    // do not want to perform full type inference at this point
    internal VCExprBoogieFunctionOp(Function func) {
      Contract.Requires(func != null);
      this.Func = func;
    }
    public override Result Accept<Result, Arg>
           (VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitBoogieFunctionOp(expr, arg);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Binders (quantifiers and let-expressions). We introduce our own class for
  // term variables, but use the Boogie-AST class for type variables

  public class VCExprVar : VCExpr {
    // the name of the variable. Note that the name is not used for comparison,
    // i.e., there can be two distinct variables with the same name
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(VarType != null);
    }

    public readonly string/*!*/ Name;
    private readonly Type/*!*/ VarType;
    public override Type/*!*/ Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return VarType;
      }
    }

    internal VCExprVar(string name, Type type) {
      Contract.Requires(type != null);
      Contract.Requires(name != null);
      this.Name = name;
      this.VarType = type;
    }
    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
  }

  public class VCExprConstant : VCExprVar
  {
      internal VCExprConstant(string name, Type type) : base(name,type) {
      Contract.Requires(type != null);
      Contract.Requires(name != null);
    }
  }

  public abstract class VCExprBinder : VCExpr {
    public readonly VCExpr/*!*/ Body;
    public readonly List<TypeVariable/*!*/>/*!*/ TypeParameters;
    public readonly List<VCExprVar/*!*/>/*!*/ BoundVars;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Body != null);
      Contract.Invariant(cce.NonNullElements(TypeParameters));
      Contract.Invariant(cce.NonNullElements(BoundVars));
    }


    public override Type/*!*/ Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Body.Type;
      }
    }

    internal VCExprBinder(List<TypeVariable/*!*/>/*!*/ typeParams, List<VCExprVar/*!*/>/*!*/ boundVars, VCExpr body) {
      Contract.Requires(body != null);
      Contract.Requires(cce.NonNullElements(boundVars));
      Contract.Requires(cce.NonNullElements(typeParams));
      Contract.Requires(boundVars.Count + typeParams.Count > 0);     // only nontrivial binders ...
      this.TypeParameters = typeParams;
      this.BoundVars = boundVars;
      this.Body = body;
    }
  }

  public class VCTrigger {
    public readonly bool Pos;
    public readonly List<VCExpr/*!*/>/*!*/ Exprs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Exprs != null);
    }


    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCTrigger) {
        VCTrigger/*!*/ thatTrigger = (VCTrigger)that;
        return this.Pos == thatTrigger.Pos &&
          HelperFuns.SameElements(this.Exprs, thatTrigger.Exprs);
      }
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return (Pos ? 913821 : 871334) +
             HelperFuns.PolyHash(123, 7, this.Exprs);
    }

    public VCTrigger(bool pos, List<VCExpr> exprs) {
      Contract.Requires(cce.NonNullElements(exprs));
      this.Pos = pos;
      this.Exprs = exprs;
    }
  }

  public class VCQuantifierInfos {
    public readonly string qid;
    public readonly int uniqueId;
    public readonly bool bvZ3Native;
    public QKeyValue attributes;

    public VCQuantifierInfos(string qid, int uniqueId, bool bvZ3Native, QKeyValue attributes) {
      this.qid = qid;
      this.uniqueId = uniqueId;
      this.bvZ3Native = bvZ3Native;
      this.attributes = attributes;
    }
  }

  public enum Quantifier {
    ALL,
    EX
  };

  public class VCExprQuantifier : VCExprBinder {
    public readonly Quantifier Quan;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Infos != null);
      Contract.Invariant(cce.NonNullElements(Triggers));
    }


    public readonly List<VCTrigger/*!*/>/*!*/ Triggers;
    public readonly VCQuantifierInfos Infos;

    // Equality is /not/ modulo bound renaming at this point
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprQuantifier) {
        VCExprQuantifier/*!*/ thatQuan = (VCExprQuantifier)that;
        return this.Quan == thatQuan.Quan &&
               HelperFuns.SameElements(this.Triggers, thatQuan.Triggers) &&
               HelperFuns.SameElements(this.TypeParameters, thatQuan.TypeParameters) &&
               HelperFuns.SameElements(this.BoundVars, thatQuan.BoundVars) &&
               this.Body.Equals(thatQuan.Body);
      }
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return Quan.GetHashCode() +
        HelperFuns.PolyHash(973219, 7, TypeParameters) +
        HelperFuns.PolyHash(998431, 9, BoundVars) +
        HelperFuns.PolyHash(123, 11, Triggers);
    }

    internal VCExprQuantifier(Quantifier kind, List<TypeVariable/*!*/>/*!*/ typeParams, List<VCExprVar/*!*/>/*!*/ boundVars, List<VCTrigger/*!*/>/*!*/ triggers, VCQuantifierInfos infos, VCExpr body)
      : base(typeParams, boundVars, body) {
      Contract.Requires(body != null);
      Contract.Requires(infos != null);
      Contract.Requires(cce.NonNullElements(triggers));
      Contract.Requires(cce.NonNullElements(boundVars));
      Contract.Requires(cce.NonNullElements(typeParams));

      this.Quan = kind;
      this.Triggers = triggers;
      this.Infos = infos;
    }
    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Let-Bindings

  public class VCExprLetBinding {
    public readonly VCExprVar V;
    public readonly VCExpr E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(V != null);
      Contract.Invariant(E != null);
    }


    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprLetBinding) {
        VCExprLetBinding/*!*/ thatB = (VCExprLetBinding)that;
        return this.V.Equals(thatB.V) && this.E.Equals(thatB.E);
      }
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return V.GetHashCode() * 71261 + E.GetHashCode();
    }

    internal VCExprLetBinding(VCExprVar v, VCExpr e) {
      Contract.Requires(e != null);
      Contract.Requires(v != null);
      this.V = v;
      this.E = e;
      Contract.Assert(v.Type.Equals(e.Type));
    }
  }

  public class VCExprLet : VCExprBinder, IEnumerable<VCExprLetBinding/*!*/> {
    private readonly List<VCExprLetBinding/*!*/>/*!*/ Bindings;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Bindings));

    }


    public int Length {
      get {
        return Bindings.Count;
      }
    }
    public VCExprLetBinding this[int index] {
      get {
        Contract.Ensures(Contract.Result<VCExprLetBinding>() != null);
        return Bindings[index];
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      if (Object.ReferenceEquals(this, that))
        return true;
      if (that is VCExprLet) {
        VCExprLet/*!*/ thatLet = (VCExprLet)that;
        return this.Body.Equals(thatLet.Body) &&
               HelperFuns.SameElements(this, (VCExprLet)that);
      }
      return false;
    }
    [Pure]
    public override int GetHashCode() {
      return HelperFuns.PolyHash(Body.GetHashCode(), 9, Bindings);
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    public IEnumerator<VCExprLetBinding/*!*/>/*!*/ GetEnumerator() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerator<VCExprLetBinding>>()));
      return Bindings.GetEnumerator();
    }
    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IEnumerator System.Collections.IEnumerable.GetEnumerator() {
      Contract.Ensures(Contract.Result<IEnumerator>() != null);
      return Bindings.GetEnumerator();
    }

    private static List<VCExprVar/*!*/>/*!*/ toSeq(List<VCExprLetBinding/*!*/>/*!*/ bindings) {
      Contract.Requires(cce.NonNullElements(bindings));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
      List<VCExprVar> res = new List<VCExprVar>();
      foreach (VCExprLetBinding/*!*/ b in bindings)
        res.Add(b.V);
      return res;
    }

    internal VCExprLet(List<VCExprLetBinding/*!*/>/*!*/ bindings, VCExpr/*!*/ body)
      : base(new List<TypeVariable/*!*/>(), toSeq(bindings), body) {
      Contract.Requires(cce.NonNullElements(bindings));
      Contract.Requires(body != null);
      this.Bindings = bindings;
    }
    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg) {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
  }
}
