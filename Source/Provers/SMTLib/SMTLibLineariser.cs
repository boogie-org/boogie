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
using System.Linq;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

// Method to turn VCExprs into strings that can be fed into SMT
// solvers. This is currently quite similar to the
// SimplifyLikeLineariser (but the code is independent)

namespace Microsoft.Boogie.SMTLib
{

  // Options for the linearisation
  public class LineariserOptions
  {
    public static LineariserOptions Default = new LineariserOptions();
    public bool LabelsBelowQuantifiers = false;
  }


  ////////////////////////////////////////////////////////////////////////////////////////

  // Lineariser for expressions. The result (bool) is currently not used for anything
  public class SMTLibExprLineariser : IVCExprVisitor<bool, LineariserOptions/*!*/>
  {

    public static string ToString(VCExpr e, UniqueNamer namer, SMTLibProverOptions opts, ISet<VCExprVar> namedAssumes = null, IList<string> optReqs = null, ISet<VCExprVar> tryAssumes = null)
    {
      Contract.Requires(e != null);
      Contract.Requires(namer != null);
      Contract.Ensures(Contract.Result<string>() != null);

      StringWriter sw = new StringWriter();
      SMTLibExprLineariser lin = new SMTLibExprLineariser(sw, namer, opts, namedAssumes, optReqs);
      Contract.Assert(lin != null);
      lin.Linearise(e, LineariserOptions.Default);
      return cce.NonNull(sw.ToString());
    }

    ////////////////////////////////////////////////////////////////////////////////////////

    private readonly TextWriter wr;
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(wr != null);
      Contract.Invariant(Namer != null);
    }

    private SMTLibOpLineariser OpLinObject = null;
    private IVCExprOpVisitor<bool, LineariserOptions>/*!>!*/ OpLineariser
    {
      get
      {
        Contract.Ensures(Contract.Result<IVCExprOpVisitor<bool, LineariserOptions>>() != null);

        if (OpLinObject == null)
          OpLinObject = new SMTLibOpLineariser(this, wr);
        return OpLinObject;
      }
    }

    internal readonly UniqueNamer Namer;
    internal int UnderQuantifier = 0;
    internal readonly SMTLibProverOptions ProverOptions;

    readonly IList<string> OptimizationRequests;
    readonly ISet<VCExprVar> NamedAssumes;

    public SMTLibExprLineariser(TextWriter wr, UniqueNamer namer, SMTLibProverOptions opts, ISet<VCExprVar> namedAssumes = null, IList<string> optReqs = null)
    {
      Contract.Requires(wr != null); Contract.Requires(namer != null);
      this.wr = wr;
      this.Namer = namer;
      this.ProverOptions = opts;
      this.OptimizationRequests = optReqs;
      this.NamedAssumes = namedAssumes;
    }

    public void Linearise(VCExpr expr, LineariserOptions options)
    {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      expr.Accept<bool, LineariserOptions>(this, options);
    }

    /////////////////////////////////////////////////////////////////////////////////////

    private static void TypeToStringHelper(Type t, StringBuilder sb)
    {
      Contract.Requires(t != null);

      TypeSynonymAnnotation syn = t as TypeSynonymAnnotation;
      if (syn != null) {
        TypeToStringHelper(syn.ExpandedType, sb);
      } else {
        if (t.IsMap && CommandLineOptions.Clo.UseArrayTheory) {
          MapType m = t.AsMap;
          // Contract.Assert(m.MapArity == 1);
          sb.Append("(Array ");
          foreach (Type tp in m.Arguments)
            sb.Append(TypeToString(tp)).Append(" ");
          sb.Append(TypeToString(m.Result)).Append(")");
        } else if (t.IsMap) {
          MapType m = t.AsMap;
          sb.Append('[');
          for (int i = 0; i < m.MapArity; ++i) {
            if (i != 0)
              sb.Append(',');
            TypeToStringHelper(m.Arguments[i], sb);
          }
          sb.Append(']');
          TypeToStringHelper(m.Result, sb);
        } else if (t.IsBool || t.IsInt || t.IsReal || t.IsFloat || t.IsBv || t.IsRMode) {
          sb.Append(TypeToString(t));
        } else {
          System.IO.StringWriter buffer = new System.IO.StringWriter();
          using (TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, /*setTokens=*/false, /*pretty=*/false)) {
            t.Emit(stream);
          }
          sb.Append(buffer.ToString());
        }
      }

    }

    public static string TypeToString(Type t)
    {
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<string>() != null);

      if (t.IsBool)
        return "Bool";
      else if (t.IsInt)
        return "Int";
      else if (t.IsReal)
        return "Real";
      else if (t.IsFloat)
        return "(_ FloatingPoint " + t.FloatExponent + " " + t.FloatSignificand + ")";
      else if (t.IsBv)
        return "(_ BitVec " + t.BvBits + ")";
      else if (t.IsRMode) {
        return "RoundingMode";
      } else {
        StringBuilder sb = new StringBuilder();        
        TypeToStringHelper(t, sb);
        var s = sb.ToString();
        if (s[0] == '(')
          return s;
        else
          return SMTLibNamer.QuoteId("T@" + s);
      }
    }

    public static string ExtractBuiltin(Function f)
    {
      Contract.Requires(f != null);
      string retVal = null;
      retVal = f.FindStringAttribute("bvbuiltin");
      
      // It used to be "sign_extend 12" in Simplify, and is "(_ sign_extend 12)" with SMT
      if (retVal != null && (retVal.StartsWith("sign_extend ") || retVal.StartsWith("zero_extend ")))
        return "(_ " + retVal + ")";

      if (retVal == null) {
        retVal = f.FindStringAttribute("builtin");
      }

      if (retVal != null && !CommandLineOptions.Clo.UseArrayTheory && SMTLibOpLineariser.ArrayOps.Contains(retVal))
      {
          retVal = null;
      }

      return retVal;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLiteral node, LineariserOptions options)
    {
      if (node == VCExpressionGenerator.True)
        wr.Write("true");
      else if (node == VCExpressionGenerator.False)
        wr.Write("false");
      else if (node is VCExprIntLit) {
        BigNum lit = ((VCExprIntLit)node).Val;
        if (lit.IsNegative)
          // In SMT2 "-42" is an identifier (SMT2, Sect. 3.2 "Symbols")
          wr.Write("(- 0 {0})", lit.Abs);
        else
          wr.Write(lit);
      } 
      else if (node is VCExprRealLit) {
        BigDec lit = ((VCExprRealLit)node).Val;
        if (lit.IsNegative)
          // In SMT2 "-42" is an identifier (SMT2, Sect. 3.2 "Symbols")
          wr.Write("(- 0.0 {0})", lit.Abs.ToDecimalString());
        else
          wr.Write(lit.ToDecimalString());
      }
      else if (node is VCExprFloatLit)
      {
        BigFloat lit = ((VCExprFloatLit)node).Val;
        wr.Write("(" + lit.ToBVString() + ")");
      }
      else if (node is VCExprRModeLit)
      {
        RoundingMode lit = ((VCExprRModeLit)node).Val;
        wr.Write(lit.ToString());
      }
      else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }

      return true;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprNAry node, LineariserOptions options)
    {
        VCExprOp op = node.Op;
        Contract.Assert(op != null);

        var booleanOps = new HashSet<VCExprOp>();
        booleanOps.Add(VCExpressionGenerator.NotOp);
        booleanOps.Add(VCExpressionGenerator.ImpliesOp);
        booleanOps.Add(VCExpressionGenerator.AndOp);
        booleanOps.Add(VCExpressionGenerator.OrOp);
        if (booleanOps.Contains(op))
        {
            Stack<VCExpr> exprs = new Stack<VCExpr>();
            exprs.Push(node);
            while (exprs.Count > 0)
            {
                VCExpr expr = exprs.Pop();
                if (expr == null)
                {
                    wr.Write(")");
                    continue;
                }
                wr.Write(" ");
                VCExprNAry naryExpr = expr as VCExprNAry;
                if (naryExpr == null || !booleanOps.Contains(naryExpr.Op))
                {
                    Linearise(expr, options);
                    continue;
                }
                else if (naryExpr.Op.Equals(VCExpressionGenerator.NotOp))
                {
                    wr.Write("(not");
                }
                else if (naryExpr.Op.Equals(VCExpressionGenerator.ImpliesOp))
                {
                    wr.Write("(=>");
                }
                else if (naryExpr.Op.Equals(VCExpressionGenerator.AndOp))
                {
                    wr.Write("(and");
                }
                else 
                {
                    System.Diagnostics.Debug.Assert(naryExpr.Op.Equals(VCExpressionGenerator.OrOp));
                    wr.Write("(or");
                }
                exprs.Push(null);
                for (int i = naryExpr.Arity - 1; i >= 0; i--)
                {
                    exprs.Push(naryExpr[i]);
                }
            }
            return true;
        }
        if (OptimizationRequests != null
            && (node.Op.Equals(VCExpressionGenerator.MinimizeOp) || node.Op.Equals(VCExpressionGenerator.MaximizeOp)))
        {
          string optOp = node.Op.Equals(VCExpressionGenerator.MinimizeOp) ? "minimize" : "maximize";
          OptimizationRequests.Add(string.Format("({0} {1})", optOp, ToString(node[0], Namer, ProverOptions, NamedAssumes)));
          Linearise(node[1], options);
          return true;
        }
        if (node.Op is VCExprSoftOp)
        {
          Linearise(node[1], options);
          return true;
        }
        if (node.Op.Equals(VCExpressionGenerator.NamedAssumeOp))
        {
          var exprVar = node[0] as VCExprVar;
          NamedAssumes.Add(exprVar);
          Linearise(node[1], options);
          return true;
        }
        return node.Accept<bool, LineariserOptions/*!*/>(OpLineariser, options);
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprVar node, LineariserOptions options)
    {
      wr.Write(Namer.GetQuotedName(node, node.Name));
      return true;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprQuantifier node, LineariserOptions options)
    {
      Contract.Assert(node.TypeParameters.Count == 0);

      UnderQuantifier++;
      Namer.PushScope(); try {

        string kind = node.Quan == Quantifier.ALL ? "forall" : "exists";
        wr.Write("({0} (", kind);

        for (int i = 0; i < node.BoundVars.Count; i++) {
          VCExprVar var = node.BoundVars[i];
          Contract.Assert(var != null);
          string printedName = Namer.GetQuotedLocalName(var, var.Name);
          Contract.Assert(printedName != null);
          wr.Write("({0} {1}) ", printedName, TypeToString(var.Type));
        }

        wr.Write(") ");

        VCQuantifierInfos infos = node.Infos;
        var weight = QKeyValue.FindIntAttribute(infos.attributes, "weight", 1);
        if (!ProverOptions.UseWeights)
          weight = 1;
        var hasAttrs = node.Triggers.Count > 0 || infos.qid != null || weight != 1 || infos.uniqueId != -1;

        if (hasAttrs)
          wr.Write("(! ");

        Linearise(node.Body, options);

        if (hasAttrs) {
          wr.Write("\n");
          if (infos.qid != null)
            wr.Write(" :qid {0}\n", SMTLibNamer.QuoteId(infos.qid));
          if (weight != 1)
            wr.Write(" :weight {0}\n", weight);
          if (infos.uniqueId != -1)
            wr.Write(" :skolemid |{0}|\n", infos.uniqueId);
          WriteTriggers(node.Triggers, options);
          
          wr.Write(")");
        }
        
        wr.Write(")");

        return true;

      } finally {
        UnderQuantifier--;
        Namer.PopScope();
      }
    }

    private void WriteTriggers(List<VCTrigger/*!>!*/> triggers, LineariserOptions options)
    {
      Contract.Requires(options != null);
      Contract.Requires(triggers != null);
      // first, count how many neg/pos triggers there are
      int negTriggers = 0;
      int posTriggers = 0;
      foreach (VCTrigger vcTrig in triggers) {
        Contract.Assert(vcTrig != null);
        if (vcTrig.Pos) {
          posTriggers++;
        } else {
          negTriggers++;
        }
      }

      if (posTriggers > 0) {
        foreach (VCTrigger vcTrig in triggers) {
          Contract.Assert(vcTrig != null);
          if (vcTrig.Pos) {
            wr.Write(" :pattern (");
            foreach (VCExpr e in vcTrig.Exprs) {
              Contract.Assert(e != null);
              wr.Write(" ");
              var subPat = e;
              var nary = e as VCExprNAry;
              if (nary != null && (nary.Op == VCExpressionGenerator.NeqOp || nary.Op == VCExpressionGenerator.EqOp)) {
                if (nary[0] is VCExprLiteral)
                  subPat = nary[1];
                else if (nary[1] is VCExprLiteral)
                  subPat = nary[0];
              }
              Linearise(subPat, options);
            }
            wr.Write(")\n");
          }
        }
      } else if (negTriggers > 0) {
        // if also positive triggers are given, the SMT solver (at least Z3)
        // will ignore the negative patterns and output a warning. Therefore
        // we never specify both negative and positive triggers
        foreach (VCTrigger vcTrig in triggers) {
          Contract.Assert(vcTrig != null);
          if (!vcTrig.Pos) {
            wr.Write(" :no-pattern ");
            Contract.Assert(vcTrig.Exprs.Count == 1);
            Linearise(vcTrig.Exprs[0], options);
            wr.Write("\n");
          }
        }
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLet node, LineariserOptions options)
    {
      Namer.PushScope();
      try {
        
        foreach (VCExprLetBinding b in node) {
          wr.Write("(let (");
          Contract.Assert(b != null);
          wr.Write("({0} ", Namer.GetQuotedName(b.V, b.V.Name));
          Linearise(b.E, options);
          wr.Write("))\n");
        }        
        Linearise(node.Body, options);
        foreach (VCExprLetBinding b in node)
          wr.Write(")");
        return true;
      } finally {
        Namer.PopScope();
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////

    // Lineariser for operator terms. The result (bool) is currently not used for anything
    internal class SMTLibOpLineariser : IVCExprOpVisitor<bool, LineariserOptions/*!*/>
    {
      private readonly SMTLibExprLineariser ExprLineariser;
      private readonly TextWriter wr;
      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(wr != null);
        Contract.Invariant(ExprLineariser != null);
      }


      public SMTLibOpLineariser(SMTLibExprLineariser ExprLineariser, TextWriter wr)
      {
        Contract.Requires(ExprLineariser != null);
        Contract.Requires(wr != null);
        this.ExprLineariser = ExprLineariser;
        this.wr = wr;
      }

      ///////////////////////////////////////////////////////////////////////////////////
      private void WriteApplication(string opName, IEnumerable<VCExpr>/*!>!*/ args, LineariserOptions options)
      {
        Contract.Requires(cce.NonNullElements(args));
        Contract.Requires(options != null);
        Contract.Assert(opName != null);

        bool hasArgs = false;
        foreach (VCExpr e in args) {
          Contract.Assert(e != null);
          if (!hasArgs)
            wr.Write("({0}", opName);
          wr.Write(" ");
          ExprLineariser.Linearise(e, options);
          hasArgs = true;
        }

        if (hasArgs)
          wr.Write(")");
        else
          wr.Write("{0}", opName);
      }

      ///////////////////////////////////////////////////////////////////////////////////

      public bool VisitNotOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("not", node, options);      // arguments can be both terms and formulas
        return true;
      }

      private bool PrintEq(VCExprNAry node, LineariserOptions options)
      {
        Contract.Requires(node != null);
        Contract.Requires(options != null);

        WriteApplication("=", node, options);

        return true;
      }

      public bool VisitEqOp(VCExprNAry node, LineariserOptions options)
      {
        return PrintEq(node, options);
      }

      public bool VisitNeqOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
        wr.Write("(not ");
        PrintEq(node, options);
        wr.Write(")");
        return true;
      }

      public bool VisitAndOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("and", node, options);
        return true;
      }

      public bool VisitOrOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("or", node, options);
        return true;
      }

      public bool VisitImpliesOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("=>", node, options);
        return true;
      }

      public bool VisitIfThenElseOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("ite", node, options);
        return true;
      }

      public bool VisitCustomOp(VCExprNAry node, LineariserOptions options)
      {
        VCExprCustomOp op = (VCExprCustomOp)node.Op;
        if (!ExprLineariser.ProverOptions.UseTickleBool && op.Name == "tickleBool")
          ExprLineariser.Linearise(VCExpressionGenerator.True, options);
        else
          WriteApplication(op.Name, node, options);
        return true;
      }

      public bool VisitDistinctOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);

        if (node.Length < 2) {
          ExprLineariser.Linearise(VCExpressionGenerator.True, options);
        } else {
          var groupings = node.GroupBy(e => e.Type).Where(g => g.Count() > 1).ToArray();
          if (groupings.Length == 0) {
            ExprLineariser.Linearise(VCExpressionGenerator.True, options);
          } else {
            if (groupings.Length > 1)
              wr.Write("(and ");

            foreach (var g in groupings) {
              wr.Write("(distinct");
              foreach (VCExpr e in g) {
                Contract.Assert(e != null);
                wr.Write(" ");
                ExprLineariser.Linearise(e, options);
              }
              wr.Write(")");
            }

            if (groupings.Length > 1)
              wr.Write(")");

            wr.Write("\n");
          }
        }

        return true;
      }

      public bool VisitLabelOp(VCExprNAry node, LineariserOptions options)
      {
        if (ExprLineariser.UnderQuantifier > 0 && !options.LabelsBelowQuantifiers) {
          ExprLineariser.Linearise(node[0], options);
          return true;
        }

        var op = (VCExprLabelOp)node.Op;

        if (CommandLineOptions.Clo.UseLabels)
        {
            // Z3 extension
            //wr.Write("({0} {1} ", op.pos ? "lblpos" : "lblneg", SMTLibNamer.QuoteId(op.label));
            wr.Write("(! ");
        }

        if(!options.LabelsBelowQuantifiers)
            wr.Write("({0} {1} ", op.pos ? "and" : "or", SMTLibNamer.QuoteId(ExprLineariser.Namer.LabelVar(op.label)));

        ExprLineariser.Linearise(node[0], options);


        if (!options.LabelsBelowQuantifiers) 
            wr.Write(")");

        if (CommandLineOptions.Clo.UseLabels)
          wr.Write(" :{0} {1})", op.pos ? "lblpos" : "lblneg", SMTLibNamer.QuoteId(ExprLineariser.Namer.LabelName(op.label)));

        return true;
      }

      public bool VisitSelectOp(VCExprNAry node, LineariserOptions options)
      {        
        var name = SimplifyLikeExprLineariser.SelectOpName(node);
        name = ExprLineariser.Namer.GetQuotedName(name, name);
        if (CommandLineOptions.Clo.UseArrayTheory)
          name = "select";
        WriteApplication(name, node, options);
        return true;
      }

      public bool VisitStoreOp(VCExprNAry node, LineariserOptions options)
      {
        var name = SimplifyLikeExprLineariser.StoreOpName(node);
        name = ExprLineariser.Namer.GetQuotedName(name, name);
        if (CommandLineOptions.Clo.UseArrayTheory)
          name = "store";
        WriteApplication(name, node, options);
        return true;
      }

      public bool VisitFloatAddOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.add RNE", node, options);
        return true;
      }

      public bool VisitFloatSubOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.sub RNE", node, options);
        return true;
      }

      public bool VisitFloatMulOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.mul RNE", node, options);
        return true;
      }

      public bool VisitFloatDivOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.div RNE", node, options);
        return true;
      }

      public bool VisitFloatLeqOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.leq", node, options);
        return true;
      }

      public bool VisitFloatLtOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.lt", node, options);
        return true;
      }

      public bool VisitFloatGeqOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.geq", node, options);
        return true;
      }

      public bool VisitFloatGtOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.gt", node, options);
        return true;
      }

      public bool VisitFloatEqOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("fp.eq", node, options);
        return true;
      }

      public bool VisitFloatNeqOp(VCExprNAry node, LineariserOptions options)
      {
        wr.Write("(not ");
        VisitFloatEqOp(node, options);
        wr.Write(")");
        return true;
      }

      static char[] hex = { '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' };
      public bool VisitBvOp(VCExprNAry node, LineariserOptions options)
      {
        var lit = (VCExprIntLit)node[0];
        var bytes = lit.Val.ToByteArray();
        if (node.Type.BvBits % 8 == 0) {
          wr.Write("#x");
          for (var pos = node.Type.BvBits / 8 - 1; pos >= 0; pos--) {
            var k = pos < bytes.Length ? bytes[pos] : (byte)0;
            wr.Write(hex[k >> 4]);
            wr.Write(hex[k & 0xf]);
          }
        } else {
          wr.Write("#b");
          for (var pos = node.Type.BvBits - 1; pos >= 0; pos--) {
            var i = pos >> 3;
            var k = i < bytes.Length ? bytes[i] : (byte)0;
            wr.Write((k & (1 << (pos & 7))) == 0 ? '0' : '1');
          }
        }
        return true;
      }

      public bool VisitBvExtractOp(VCExprNAry node, LineariserOptions options)
      {
        var op = (VCExprBvExtractOp)node.Op;
        wr.Write("((_ extract {0} {1}) ", op.End - 1, op.Start);
        ExprLineariser.Linearise(node[0], options);
        wr.Write(")");
        return true;
      }

      public bool VisitBvConcatOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("concat", node, options);
        return true;
      }

      public bool VisitAddOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("+", node, options);
        return true;
      }

      public bool VisitSubOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("-", node, options);
        return true;
      }

      public bool VisitMulOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("*", node, options);
        return true;
      }

      public bool VisitDivOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("div", node, options);
        return true;
      }

      public bool VisitModOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("mod", node, options);
        return true;
      }

      public bool VisitRealDivOp(VCExprNAry node, LineariserOptions options) {
        WriteApplication("/", node, options);
        return true;
      }

      public bool VisitPowOp(VCExprNAry node, LineariserOptions options) {
        WriteApplication("real_pow", node, options);
        return true;
      }

      public bool VisitLtOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("<", node, options);
        return true;
      }

      public bool VisitLeOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("<=", node, options);
        return true;
      }

      public bool VisitGtOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication(">", node, options);
        return true;
      }

      public bool VisitGeOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication(">=", node, options);
        return true;
      }

      public bool VisitSubtypeOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("UOrdering2", node, options);
        return true;
      }

      public bool VisitSubtype3Op(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("UOrdering3", node, options);
        return true;
      }

      public bool VisitToIntOp(VCExprNAry node, LineariserOptions options) {
        WriteApplication("to_int", node, options);
        return true;
      }

      public bool VisitToRealOp(VCExprNAry node, LineariserOptions options) {
        WriteApplication("to_real", node, options);
        return true;
      }

      private string ExtractDatatype(Function func) {
        if (func is DatatypeSelector) {
          DatatypeSelector selector = (DatatypeSelector) func;
          Variable v = selector.constructor.InParams[selector.index];
          return ExprLineariser.Namer.GetQuotedName(v, v.Name + "#" + selector.constructor.Name);
        }
        else if (func is DatatypeMembership) {
          DatatypeMembership membership = (DatatypeMembership)func;
          return ExprLineariser.Namer.GetQuotedName(membership, "is-" + membership.constructor.Name);
        }
        else {
          return null;
        }
      }

      public bool VisitBoogieFunctionOp(VCExprNAry node, LineariserOptions options) {
        VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp)node.Op;
        Contract.Assert(op != null);
        string printedName;

        var builtin = ExtractBuiltin(op.Func);
        var datatype = ExtractDatatype(op.Func);
        if (builtin != null)
        {
            printedName = CheckMapApply(builtin, node);
        }
        else if (datatype != null)
        {
            printedName = datatype;
        }
        else
        { 
            printedName = ExprLineariser.Namer.GetQuotedName(op.Func, op.Func.Name); 
        }
        Contract.Assert(printedName != null);

        WriteApplication(printedName, node, options);

        return true;
      }

      private static Type ResultType(Type type) {
        MapType mapType = type as MapType;
        if (mapType != null) {
          return ResultType(mapType.Result);
        }
        else {
          return type;
        }
      }

      public static HashSet<string> ArrayOps = new HashSet<string>(new string[] { 
          "MapConst", "MapAdd", "MapSub", "MapMul", "MapDiv", "MapMod", "MapEq", "MapIff", "MapGt", "MapGe", "MapLt", "MapLe", "MapOr", "MapAnd", "MapNot", "MapImp", "MapIte" });

      private static string CheckMapApply(string name, VCExprNAry node) {
        if (name == "MapConst") {
          Type type = node.Type;
          string s = TypeToString(type);
          return "(as const " + s + ")";
        } 
        else if (name == "MapAdd") {
          return "(_ map (+ (Int Int) Int))";
        }
        else if (name == "MapSub") {
          return "(_ map (- (Int Int) Int))";
        }
        else if (name == "MapMul") {
          return "(_ map (* (Int Int) Int))";
        }
        else if (name == "MapDiv") {
          return "(_ map (div (Int Int) Int))";
        }
        else if (name == "MapMod") {
          return "(_ map (mod (Int Int) Int))";
        }
        else if (name == "MapEq") {
          Type type = ResultType(node[0].Type);
          string s = TypeToString(type);
          return "(_ map (= (" + s + " " + s + ") Bool))";
        }
        else if (name == "MapIff") {
          return "(_ map (= (Bool Bool) Bool))";
        }
        else if (name == "MapGt") {
          return "(_ map (> (Int Int) Int))";
        }
        else if (name == "MapGe") {
          return "(_ map (>= (Int Int) Int))";
        }
        else if (name == "MapLt") {
          return "(_ map (< (Int Int) Int))";
        }
        else if (name == "MapLe") {
          return "(_ map (<= (Int Int) Int))";
        }
        else if (name == "MapOr") {
          return "(_ map or)";
        }
        else if (name == "MapAnd") {
          return "(_ map and)";
        }
        else if (name == "MapNot") {
          return "(_ map not)";
        }
        else if (name == "MapImp") {
          return "(_ map =>)";
        }
        else if (name == "MapIte") {
          Type type = ResultType(node.Type);
          string s = TypeToString(type);
          return "(_ map (ite (Bool " + s + " " + s + ") " + s + "))";
        }
        else {
          return name;
        }
      }
    }
  }

}
