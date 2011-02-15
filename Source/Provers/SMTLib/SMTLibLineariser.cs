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
    public static readonly LineariserOptions Default = new LineariserOptions();
  }


  ////////////////////////////////////////////////////////////////////////////////////////

  // Lineariser for expressions. The result (bool) is currently not used for anything
  public class SMTLibExprLineariser : IVCExprVisitor<bool, LineariserOptions/*!*/>
  {

    public static string ToString(VCExpr e, UniqueNamer namer, SMTLibProverOptions opts)
    {
      Contract.Requires(e != null);
      Contract.Requires(namer != null);
      Contract.Ensures(Contract.Result<string>() != null);

      StringWriter sw = new StringWriter();
      SMTLibExprLineariser lin = new SMTLibExprLineariser(sw, namer, opts);
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
    internal readonly SMTLibProverOptions ProverOptions;

    public SMTLibExprLineariser(TextWriter wr, UniqueNamer namer, SMTLibProverOptions opts)
    {
      Contract.Requires(wr != null); Contract.Requires(namer != null);
      this.wr = wr;
      this.Namer = namer;
      this.ProverOptions = opts;
    }

    public void Linearise(VCExpr expr, LineariserOptions options)
    {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      expr.Accept<bool, LineariserOptions>(this, options);
    }

    /////////////////////////////////////////////////////////////////////////////////////

    internal static string TypeToString(Type t)
    {
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<string>() != null);

      if (t.IsBool)
        return "Bool";
      else if (t.IsInt)
        return "Int";
      else if (t.IsBv) {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      } // bitvectors are currently not handled for SMT-Lib solvers
      else {
        // at this point, only the types U, T should be left (except when /typeEncoding:m is used)
        System.IO.StringWriter buffer = new System.IO.StringWriter();
        using (TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, false)) {
          t.Emit(stream);
        }
        return SMTLibNamer.QuoteId("T@" + buffer.ToString());
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLiteral node, LineariserOptions options)
    {
      if (node == VCExpressionGenerator.True)
        wr.Write("true");
      else if (node == VCExpressionGenerator.False)
        wr.Write("false");
      else if (node is VCExprIntLit) {
        // some SMT-solvers do not understand negative literals
        // (e.g., yices)
        BigNum lit = ((VCExprIntLit)node).Val;
        if (lit.IsNegative)
          wr.Write("(- 0 {0})", lit.Abs);
        else
          wr.Write(lit);
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }

      return true;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprNAry node, LineariserOptions options)
    {
      //Contract.Requires(node != null);
      //Contract.Requires(options != null);

      VCExprOp op = node.Op;
      Contract.Assert(op != null);

      if (op.Equals(VCExpressionGenerator.AndOp) ||
           op.Equals(VCExpressionGenerator.OrOp)) {
        // handle these operators without recursion

        wr.Write("({0}",
          op.Equals(VCExpressionGenerator.AndOp) ? "and" : "or");
        foreach (var ch in node.UniformArguments) {
          wr.Write("\n");
          Linearise(ch, options);
        }
        wr.Write(")");

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

      Namer.PushScope(); try {

        string kind = node.Quan == Quantifier.ALL ? "forall" : "exists";
        wr.Write("({0} (", kind);

        for (int i = 0; i < node.BoundVars.Count; i++) {
          VCExprVar var = node.BoundVars[i];
          Contract.Assert(var != null);
          string printedName = Namer.GetLocalName(var, var.Name);
          Contract.Assert(printedName != null);
          wr.Write("({0} {1}) ", printedName, TypeToString(var.Type));
        }

        wr.Write(")");

        VCQuantifierInfos infos = node.Infos;
        var weight = QKeyValue.FindIntAttribute(infos.attributes, "weight", 1);
        if (!ProverOptions.UseWeights)
          weight = 1;
        var hasAttrs = node.Triggers.Count > 0 || infos.qid != null || weight != 1;

        if (hasAttrs)
          wr.Write("(! ");

        Linearise(node.Body, options);

        if (hasAttrs) {
          wr.Write("\n");
          if (infos.qid != null)
            wr.Write(" :named {0}\n", SMTLibNamer.QuoteId(infos.qid));
          if (weight != 1)
            wr.Write(" :weight {0}\n", weight);
          WriteTriggers(node.Triggers, options);
          
          wr.Write(")");
        }
        
        wr.Write(")");

        return true;

      } finally {
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
              Linearise(e, options);
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
            wr.Write(" :no-pattern (");
            Contract.Assert(vcTrig.Exprs.Count == 1);
            Linearise(vcTrig.Exprs[0], options);
            wr.Write(")\n");
          }
        }
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLet node, LineariserOptions options)
    {
      Namer.PushScope();
      try {
        wr.Write("(let (");
        foreach (VCExprLetBinding b in node) {
          Contract.Assert(b != null);
          wr.Write("({0} ", Namer.GetQuotedName(b.V, b.V.Name));
          Linearise(b.E, options);
          wr.Write(")\n");
        }
        wr.Write(") ");
        Linearise(node.Body, options);
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

        // not sure if this is needed
        if (node[0].Type.IsBool) {
          Contract.Assert(node[1].Type.IsBool);
          // use equivalence
          WriteApplication("iff", node, options);
        } else {
          WriteApplication("=", node, options);
        }

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

        return true;
      }

      public bool VisitLabelOp(VCExprNAry node, LineariserOptions options)
      {
        var op = (VCExprLabelOp)node.Op;
        if (ExprLineariser.ProverOptions.UseLabels) {
          // Z3 extension
          wr.Write("({0} {1} ", op.pos ? "lblpos" : "lblneg", SMTLibNamer.QuoteId(op.label));
          ExprLineariser.Linearise(node[0], options);
          wr.Write(")");
        } else {
          ExprLineariser.Linearise(node[0], options);
        }
        return true;
      }

      public bool VisitSelectOp(VCExprNAry node, LineariserOptions options)
      {
        var name = SimplifyLikeExprLineariser.SelectOpName(node);
        name = ExprLineariser.Namer.GetQuotedName(name, name);
        WriteApplication(name, node, options);
        return true;
      }

      public bool VisitStoreOp(VCExprNAry node, LineariserOptions options)
      {
        var name = SimplifyLikeExprLineariser.StoreOpName(node);
        name = ExprLineariser.Namer.GetQuotedName(name, name);
        WriteApplication(name, node, options);
        return true;
      }

      public bool VisitBvOp(VCExprNAry node, LineariserOptions options)
      {
       { Contract.Assert(false); throw new NotImplementedException(); }       // TODO
      }

      public bool VisitBvExtractOp(VCExprNAry node, LineariserOptions options)
      {
       { Contract.Assert(false); throw new NotImplementedException(); }       // TODO
      }

      public bool VisitBvConcatOp(VCExprNAry node, LineariserOptions options)
      {
       { Contract.Assert(false); throw new NotImplementedException(); }       // TODO
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
        WriteApplication("int_div", node, options);
        return true;
      }

      public bool VisitModOp(VCExprNAry node, LineariserOptions options)
      {
        WriteApplication("int_mod", node, options);
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

      public bool VisitBoogieFunctionOp(VCExprNAry node, LineariserOptions options)
      {
        VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp)node.Op;
        Contract.Assert(op != null);
        string printedName = ExprLineariser.Namer.GetQuotedName(op.Func, op.Func.Name);
        Contract.Assert(printedName != null);

        WriteApplication(printedName, node, options);

        return true;
      }

    }
  }

}
