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
using Microsoft.Boogie.VCExprAST;

// Method to turn VCExprs into strings that can be fed into SMT
// solvers. This is currently quite similar to the
// SimplifyLikeLineariser (but the code is independent)

namespace Microsoft.Boogie.SMTLib
{

  // Options for the linearisation
  public class LineariserOptions {

    public readonly bool AsTerm;
    public LineariserOptions SetAsTerm(bool newVal) {
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);

      if (newVal)
        return DefaultTerm;
      else
        return Default;
    }

    internal LineariserOptions(bool asTerm) {
      this.AsTerm = asTerm;
    }

    [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(Default!=null);
      Contract.Invariant(DefaultTerm!=null);
}

    public static readonly LineariserOptions Default = new LineariserOptions (false);
    internal static readonly LineariserOptions DefaultTerm = new LineariserOptions (true);
  }


  ////////////////////////////////////////////////////////////////////////////////////////

  // Lineariser for expressions. The result (bool) is currently not used for anything
  public class SMTLibExprLineariser : IVCExprVisitor<bool, LineariserOptions/*!*/> {

    public static string ToString(VCExpr e, UniqueNamer namer) {
    Contract.Requires(e != null);
    Contract.Requires(namer != null);
    Contract.Ensures(Contract.Result<string>() != null);

      StringWriter sw = new StringWriter();
      SMTLibExprLineariser lin = new SMTLibExprLineariser (sw, namer);
      Contract.Assert(lin!=null);
      lin.Linearise(e, LineariserOptions.Default);
      return cce.NonNull(sw.ToString());
    }

    ////////////////////////////////////////////////////////////////////////////////////////

    private readonly TextWriter wr;
    [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(wr!=null);
      Contract.Invariant(Namer != null);
}

    private SMTLibOpLineariser OpLinObject = null;
    private IVCExprOpVisitor<bool, LineariserOptions>/*!>!*/ OpLineariser { get {
      Contract.Ensures(Contract.Result<IVCExprOpVisitor<bool,LineariserOptions>>() !=null);

      if (OpLinObject == null)
        OpLinObject = new SMTLibOpLineariser(this, wr);
      return OpLinObject;
    } }

    internal readonly UniqueNamer Namer;

    public SMTLibExprLineariser(TextWriter wr, UniqueNamer namer) {
      Contract.Requires(wr != null);Contract.Requires(namer != null);
      this.wr = wr;
      this.Namer = namer;
    }

    public void Linearise(VCExpr expr, LineariserOptions options) {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      expr.Accept<bool, LineariserOptions>(this, options);
    }

    public void LineariseAsTerm(VCExpr expr, LineariserOptions options) {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      Linearise(expr, options.SetAsTerm(true));
    }

    /////////////////////////////////////////////////////////////////////////////////////

    internal static string TypeToString(Type t) {
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<string>() != null);

      if (t.IsBool)
        return "TermBool";
      else if (t.IsInt)
        return "Int";
      else if (t.IsBv) {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      } // bitvectors are currently not handled for SMT-Lib solvers
      else {
        // at this point, only the types U, T should be left
        System.IO.StringWriter buffer = new System.IO.StringWriter();
        using (TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, false)) {
          t.Emit(stream);
        }
        return "boogie" + buffer.ToString();
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public static string MakeIdPrintable(string s) {
      Contract.Requires(s != null);
      Contract.Ensures(Contract.Result<string>() != null);

      // make sure that no keywords are used as identifiers
      switch(s) {
      case andName:
      case orName:
      case notName:
      case impliesName:
      case iffName:
      case eqName:
      case distinctName:
      case TRUEName:
      case FALSEName:
      case "Array":
        s = "nonkeyword_" + s;
        break;
      }

      string newS = "";
      foreach (char ch in s) {
        if (Char.IsLetterOrDigit(ch) || ch == '.' || ch == '\'' || ch == '_')
          newS = newS + ch;
        else
          // replace everything else with a .
          newS = newS + '.';
      }

      // ensure that the first character is not . or _ (some SMT-solvers do
      // not like that, e.g., yices and cvc3)
      if (newS[0] == '.' || newS[0] == '_')
        newS = "x" + newS;

      return newS;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    /// <summary>
    /// The name for logical conjunction in Simplify
    /// </summary>
    internal const string andName = "and"; // conjunction
    internal const string orName = "or"; // disjunction
    internal const string notName = "not"; // negation
    internal const string impliesName = "implies"; // implication
    internal const string iteName = "ite"; // if-then-else
    internal const string iffName = "iff"; // logical equivalence
    internal const string eqName = "="; // equality
    internal const string lessName = "<";
    internal const string greaterName = ">"; 
    internal const string atmostName = "<=";
    internal const string atleastName = ">=";
    internal const string TRUEName = "true"; // nullary predicate that is always true
    internal const string FALSEName = "false"; // nullary predicate that is always false
    internal const string subtypeName = "UOrdering2";
    internal const string subtypeArgsName = "UOrdering3";

    internal const string distinctName = "distinct";

    internal const string boolTrueName = "boolTrue";
    internal const string boolFalseName = "boolFalse";
    internal const string boolAndName = "boolAnd";
    internal const string boolOrName = "boolOr";
    internal const string boolNotName = "boolNot";
    internal const string boolIffName = "boolIff";
    internal const string boolImpliesName = "boolImplies";
    internal const string boolIteName = "ite";
    internal const string termUEqual = "UEqual";
    internal const string termTEqual = "TEqual";
    internal const string termIntEqual = "IntEqual";
    internal const string termLessName = "intLess";
    internal const string termGreaterName = "intGreater";
    internal const string termAtmostName = "intAtMost";
    internal const string termAtleastName = "intAtLeast";
    internal const string intAddName = "+";
    internal const string intSubName = "-";
    internal const string intMulName = "*";
    internal const string intDivName = "boogieIntDiv";
    internal const string intModName = "boogieIntMod";

    internal void AssertAsTerm(string x, LineariserOptions options) {
      Contract.Requires(x != null);
      Contract.Requires(options != null);
      if (!options.AsTerm)
        System.Diagnostics.Debug.Fail("One should never write " + x + " as a formula!");
    }

    internal void AssertAsFormula(string x, LineariserOptions options) {
    Contract.Requires(x != null);
    Contract.Requires(options != null);
      if (options.AsTerm)
        System.Diagnostics.Debug.Fail("One should never write " + x + " as a term!");
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLiteral node, LineariserOptions options) {
      Contract.Requires(node != null);
      Contract.Requires(options != null);
      if (options.AsTerm) {

        if (node == VCExpressionGenerator.True)
          wr.Write("{0}", boolTrueName);
        else if (node == VCExpressionGenerator.False)
          wr.Write("{0}", boolFalseName);
        else if (node is VCExprIntLit) {
          // some SMT-solvers do not understand negative literals
          // (e.g., yices)
          BigNum lit = ((VCExprIntLit)node).Val;
          if (lit.IsNegative)
            wr.Write("({0} 0 {1})", intSubName, lit.Abs);
          else
            wr.Write(lit);
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }

      } else {

        if (node == VCExpressionGenerator.True)
          wr.Write("{0}", TRUEName);
        else if (node == VCExpressionGenerator.False)
          wr.Write("{0}", FALSEName);
        else if (node is VCExprIntLit) {
          System.Diagnostics.Debug.Fail("One should never write IntLit as a predicate!");
        } else
         {Contract.Assert(false);  throw new cce.UnreachableException();}

      }

      return true;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprNAry node, LineariserOptions options) {
      Contract.Requires(node != null);
      Contract.Requires(options != null);
      
      VCExprOp op = node.Op;
      Contract.Assert(op!=null);

      if (!options.AsTerm &&
          (op.Equals(VCExpressionGenerator.AndOp) ||
           op.Equals(VCExpressionGenerator.OrOp))) {
        // handle these operators without recursion

        wr.Write("({0}",
                 op.Equals(VCExpressionGenerator.AndOp) ? andName : orName);
        IEnumerator enumerator = new VCExprNAryUniformOpEnumerator (node);
        Contract.Assert(enumerator!=null);
        while (enumerator.MoveNext()) {
          VCExprNAry naryExpr = enumerator.Current as VCExprNAry;
          if (naryExpr == null || !naryExpr.Op.Equals(op)) {
            wr.Write(" ");
            Linearise(cce.NonNull((VCExpr)enumerator.Current), options);
          }
        }

        wr.Write(")");

        return true;
      }

      return node.Accept<bool, LineariserOptions/*!*/>(OpLineariser, options);
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprVar node, LineariserOptions options) {
      Contract.Requires(node != null);
      Contract.Requires(options != null);
      string printedName = Namer.GetName(node, MakeIdPrintable(node.Name));
      Contract.Assert(printedName!=null);

      if (options.AsTerm ||
          // formula variables are easy to identify in SMT-Lib
          printedName[0] == '$')
        wr.Write("{0}", printedName);
      else
        wr.Write("({0} {1} {2})", eqName, printedName, boolTrueName);

      return true;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprQuantifier node, LineariserOptions options) {
      Contract.Requires(node != null);
      Contract.Requires(options != null);
      AssertAsFormula(node.Quan.ToString(), options);
     Contract.Assert(node.TypeParameters.Count == 0);

      Namer.PushScope(); try {

      string kind = node.Quan == Quantifier.ALL ? "forall" : "exists";
      wr.Write("({0} ", kind);

      for (int i = 0; i < node.BoundVars.Count; i++) 
        {
          VCExprVar var = node.BoundVars[i];
          Contract.Assert(var!=null);
          // ensure that the variable name starts with ?
          string printedName = Namer.GetLocalName(var, "?" + MakeIdPrintable(var.Name));
        Contract.Assert(printedName!=null);
         Contract.Assert(printedName[0] == '?');
          wr.Write("({0} {1}) ", printedName, TypeToString(var.Type));
        }
        
      /*      if (options.QuantifierIds) {
        // only needed for Z3
        VCQuantifierInfos! infos = node.Infos;
        if (infos.qid != null) {
          wr.Write("(QID ");
          wr.Write(infos.qid);
          wr.Write(") ");
        }
        if (0 <= infos.uniqueId) {
          wr.Write("(SKOLEMID ");
          wr.Write(infos.uniqueId);
          wr.Write(") ");
        }
        } */

      Linearise(node.Body, options);

      WriteTriggers(node.Triggers, options);        
      wr.Write(")");

      return true;

      } finally {
        Namer.PopScope();
      }
    }

    private void WriteTriggers(List<VCTrigger/*!>!*/> triggers, LineariserOptions options) {
      Contract.Requires(options != null);
      Contract.Requires(triggers != null);
      // first, count how many neg/pos triggers there are
      int negTriggers = 0;
      int posTriggers = 0;
      foreach (VCTrigger vcTrig in triggers) {
        Contract.Assert(vcTrig!=null);
        if (vcTrig.Pos) {
          posTriggers++;
        } else {
          negTriggers++;
        }
      }

      if (posTriggers > 0) {
        foreach (VCTrigger vcTrig in triggers) {
          Contract.Assert(vcTrig!=null);
          if (vcTrig.Pos) {
            wr.Write(" :pat {");
            foreach (VCExpr e in vcTrig.Exprs) {
              Contract.Assert(e!=null);
              wr.Write(" ");
              LineariseAsTerm(e, options);
            }
            wr.Write(" } ");
          }
        }
      } else if (negTriggers > 0) {
        // if also positive triggers are given, the SMT solver (at least Z3)
        // will ignore the negative patterns and output a warning. Therefore
        // we never specify both negative and positive triggers
        foreach (VCTrigger vcTrig in triggers) {
          Contract.Assert(vcTrig!=null);
          if (!vcTrig.Pos) {
            wr.Write(" :nopat { ");
           Contract.Assert(vcTrig.Exprs.Count == 1);
            wr.Write(" ");
            LineariseAsTerm(vcTrig.Exprs[0], options);
            wr.Write(" } ");
          }
        }
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLet node, LineariserOptions options) {
      Contract.Requires(node != null);
      Contract.Requires(options != null);
      Namer.PushScope(); try {

      foreach (VCExprLetBinding b in node) {
        Contract.Assert(b != null);
        bool formula = b.V.Type.IsBool;

        wr.Write("({0} (", formula ? "flet" : "let");
        string printedName = Namer.GetLocalName(b.V, "$" + MakeIdPrintable(b.V.Name));
       Contract.Assert(printedName[0] == '$');
        
        wr.Write("{0} ", printedName);
        Linearise(b.E, options.SetAsTerm(!formula));
        wr.Write(") ");
      }
      Linearise(node.Body, options);

      for (int i = 0; i < node.Length; ++i)
        wr.Write(")");

      return true;

      } finally {
        Namer.PopScope();
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////

    // Lineariser for operator terms. The result (bool) is currently not used for anything
    internal class SMTLibOpLineariser : IVCExprOpVisitor<bool, LineariserOptions/*!*/> {
      private readonly SMTLibExprLineariser ExprLineariser;
      private readonly TextWriter wr;
      [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(wr!=null);
        Contract.Invariant(ExprLineariser!=null);
}


      public SMTLibOpLineariser(SMTLibExprLineariser ExprLineariser, TextWriter wr) {
        Contract.Requires(ExprLineariser != null);
        Contract.Requires(wr != null);
        this.ExprLineariser = ExprLineariser;
        this.wr = wr;
      }

      ///////////////////////////////////////////////////////////////////////////////////

      private void WriteApplication(string op, IEnumerable<VCExpr/*!>!*/> args,
                                    LineariserOptions options,
                                    bool argsAsTerms) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(args ));
      Contract.Requires(options != null);
        WriteApplication(op, op, args, options, argsAsTerms);
      }

      private void WriteApplication(string op, IEnumerable<VCExpr/*!>!*/> args,
                                    LineariserOptions options) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(args ));
      Contract.Requires(options != null);
        WriteApplication(op, op, args, options, options.AsTerm);
      }

      private void WriteTermApplication(string op, IEnumerable<VCExpr/*!>!*/> args,
                                        LineariserOptions options) {
        Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(args ));
      Contract.Requires(options != null);
        ExprLineariser.AssertAsTerm(op, options);
        WriteApplication(op, op, args, options, options.AsTerm);
      }

      private void WriteApplication(string termOp, string predOp,
                                    IEnumerable<VCExpr/*!>!*/> args, LineariserOptions options) {
        Contract.Requires(predOp != null);
        Contract.Requires(termOp != null);
      Contract.Requires(cce.NonNullElements(args ));
      Contract.Requires(options != null);
        WriteApplication(termOp, predOp, args, options, options.AsTerm);
      }

      private void WriteApplication(string termOp, string predOp,
                                    IEnumerable<VCExpr>/*!>!*/ args, LineariserOptions options,
                                    // change the AsTerm option for the arguments?
                                    bool argsAsTerms) {
      Contract.Requires(predOp != null);
        Contract.Requires(termOp != null);
      Contract.Requires(cce.NonNullElements(args ));
      Contract.Requires(options != null);
        string opName = options.AsTerm ? termOp : predOp;
        Contract.Assert(opName!=null);
        LineariserOptions newOptions = options.SetAsTerm(argsAsTerms);
        Contract.Assert(newOptions!=null);

        bool hasArgs = false;
        foreach (VCExpr e in args) {
          Contract.Assert(e!=null);
          if (!hasArgs)
            wr.Write("({0}", opName);
          wr.Write(" ");
          ExprLineariser.Linearise(e, newOptions);
          hasArgs = true;
        }
        
        if (hasArgs)
          wr.Write(")");
        else
          wr.Write("{0}", opName);
      }

      // write an application that can only be a term.
      // if the expression is supposed to be printed as a formula,
      // it is turned into an equation (EQ (f args) |@true|)
      private void WriteApplicationTermOnly(string termOp,
                                            IEnumerable<VCExpr>/*!>!*/ args, LineariserOptions options) {
        Contract.Requires(termOp != null);
        Contract.Requires(cce.NonNullElements(args));
        Contract.Requires(options != null);
        if (!options.AsTerm)
          // Write: (EQ (f args) |@true|)
          // where "args" are written as terms
          wr.Write("({0} ", eqName);

        WriteApplication(termOp, args, options, true);

        if (!options.AsTerm)
          wr.Write(" {0})", boolTrueName);
      }

      ///////////////////////////////////////////////////////////////////////////////////
      
      public bool VisitNotOp      (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
        WriteApplication(boolNotName, notName, node, options);      // arguments can be both terms and formulas
        return true;
      }

      private bool PrintEq(VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
        if (options.AsTerm) {
          // use equality on terms, also if the arguments have type bool
         Contract.Assert(node[0].Type.Equals(node[1].Type));
          if (node[0].Type.IsBool) {
            WriteApplication(boolIffName, node, options);
          } else if (node[0].Type.IsInt) {
            WriteApplication(termIntEqual, node, options);
          } else {
            // TODO: make this less hackish
            CtorType t = node[0].Type as CtorType;
            if (t != null && t.Decl.Name.Equals("U")) {
              WriteApplication(termUEqual, node, options);
            } else if (t != null && t.Decl.Name.Equals("T")) {
              WriteApplication(termTEqual, node, options);
            } else {
             {Contract.Assert(false);  throw new cce.UnreachableException();}   // unknown type
            }
          }
        } else {
          if (node[0].Type.IsBool) {
           Contract.Assert(node[1].Type.IsBool);
            // use equivalence
            WriteApplication(iffName, node, options);
          } else {
            // use equality and write the arguments as terms
            WriteApplication(eqName, node, options, true);
          }
        }

        return true;        
      }

      public bool VisitEqOp       (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
        return PrintEq(node, options);
      }

      public bool VisitNeqOp      (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
        wr.Write("({0} ", options.AsTerm ? boolNotName : notName);
        PrintEq(node, options);
        wr.Write(")");
        return true;
      }

      public bool VisitAndOp      (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       Contract.Assert(options.AsTerm);
        WriteApplication(boolAndName, andName, node, options);
        return true;
      }

      public bool VisitOrOp       (VCExprNAry node, LineariserOptions options) {
      Contract.Requires(node != null);
        Contract.Requires(options != null);
       
       Contract.Assert(options.AsTerm);
        WriteApplication(boolOrName, orName, node, options);
        return true;
      }

      public bool VisitImpliesOp  (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteApplication(boolImpliesName, impliesName, node, options);
        return true;
      }

      public bool VisitIfThenElseOp  (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteApplication(boolIteName, iteName, node, options);
        return true;
      }

      public bool VisitDistinctOp (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        ExprLineariser.AssertAsFormula(distinctName, options);
        
        if (node.Length < 2) {
          ExprLineariser.Linearise(VCExpressionGenerator.True, options);
        } else {
          wr.Write("({0}", distinctName);
          foreach (VCExpr e in node) {
            Contract.Assert(e!=null);
            wr.Write(" ");
            ExprLineariser.LineariseAsTerm(e, options);
          }
          wr.Write(")");
        }

        return true;
      }

      public bool VisitLabelOp    (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
        Contract.Requires(node.Length>=1);
        // VCExprLabelOp! op = (VCExprLabelOp)node.Op;
        // TODO
        //        wr.Write(String.Format("({0} |{1}| ", op.pos ? "LBLPOS" : "LBLNEG", op.label));
        ExprLineariser.Linearise(node[0], options);
        //        wr.Write(")");
        return true;
      }

      public bool VisitSelectOp   (VCExprNAry node, LineariserOptions options) {
       Contract.Requires(node != null);
        Contract.Requires(options != null);
       
       {Contract.Assert(false);  throw new cce.UnreachableException();}      // should not occur in the output
      }

      public bool VisitStoreOp    (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
       {Contract.Assert(false);  throw new cce.UnreachableException();}       // should not occur in the output
      }

      public bool VisitBvOp       (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
       {Contract.Assert(false);  throw new NotImplementedException();}       // TODO
      }

      public bool VisitBvExtractOp(VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
       {Contract.Assert(false);  throw new NotImplementedException();}       // TODO
      }

      public bool VisitBvConcatOp (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
       {Contract.Assert(false);  throw new NotImplementedException();}       // TODO
      }

      public bool VisitAddOp            (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteTermApplication(intAddName, node, options);
        return true;
      }

      public bool VisitSubOp            (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteTermApplication(intSubName, node, options);
        return true;
      }

      public bool VisitMulOp            (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteTermApplication(intMulName, node, options);
        return true;
      }

      public bool VisitDivOp            (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteTermApplication(intDivName, node, options);
        return true;
      }

      public bool VisitModOp            (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteTermApplication(intModName, node, options);
        return true;
      }

      public bool VisitLtOp             (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteApplication(termLessName, lessName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitLeOp             (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteApplication(termAtmostName, atmostName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitGtOp             (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteApplication(termGreaterName, greaterName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitGeOp             (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteApplication(termAtleastName, atleastName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitSubtypeOp        (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteApplication(subtypeName, node, options, true);               // arguments are always terms
        return true;
      }

      public bool VisitSubtype3Op        (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        WriteApplication(subtypeArgsName, node, options, true);               // arguments are always terms
        return true;
      }

      public bool VisitBoogieFunctionOp (VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
       
        VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp)node.Op;
        Contract.Assert(op!=null);
        string printedName = ExprLineariser.Namer.GetName(op.Func, MakeIdPrintable(op.Func.Name));
        Contract.Assert(printedName!=null);

        // arguments are always terms
        WriteApplicationTermOnly(printedName, node, options);
        return true;
      }
      
    }
  }

}
