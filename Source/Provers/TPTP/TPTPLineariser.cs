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

// Method to turn VCExprs into strings that can be fed into TPTP provers.
// This is currently quite similar to the
// SimplifyLikeLineariser (but the code is independent)

namespace Microsoft.Boogie.TPTP
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
  public class TPTPExprLineariser : IVCExprVisitor<bool, LineariserOptions/*!*/> {

    public static string ToString(VCExpr e, UniqueNamer namer, TPTPProverOptions opts) {
    Contract.Requires(e != null);
    Contract.Requires(namer != null);
    Contract.Ensures(Contract.Result<string>() != null);

      StringWriter sw = new StringWriter();
      TPTPExprLineariser lin = new TPTPExprLineariser (sw, namer, opts);
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

    private TPTPOpLineariser OpLinObject = null;
    private IVCExprOpVisitor<bool, LineariserOptions>/*!>!*/ OpLineariser { get {
      Contract.Ensures(Contract.Result<IVCExprOpVisitor<bool,LineariserOptions>>() !=null);

      if (OpLinObject == null)
        OpLinObject = new TPTPOpLineariser(this, wr);
      return OpLinObject;
    } }

    internal readonly UniqueNamer Namer;
    internal readonly TPTPProverOptions Options;

    public TPTPExprLineariser(TextWriter wr, UniqueNamer namer, TPTPProverOptions opts) {
      Contract.Requires(wr != null);Contract.Requires(namer != null);
      this.wr = wr;
      this.Namer = namer;
      this.Options = opts;
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
      case TRUEName:
      case FALSEName:
      case "Array":
        s = "nonkeyword_" + s;
        break;
      }

      var res = new StringBuilder();
      
      foreach (char ch in s) {
        if (Char.IsLetterOrDigit(ch))
          res.Append(ch);
        else
          // replace everything else with a _
          res.Append('_');
      }

      return res.ToString();
    }

    public static string Lowercase(string s)
    {
      if (char.IsLower(s[0])) return MakeIdPrintable(s);
      else return MakeIdPrintable("x" + s);
    }

    /////////////////////////////////////////////////////////////////////////////////////

    internal const string andName = "&"; // conjunction
    internal const string orName = "|"; // disjunction
    internal const string notName = "~"; // negation
    internal const string impliesName = "=>"; // implication
    internal const string iteName = "$itef"; // if-then-else
    internal const string iffName = "<=>"; // logical equivalence
    internal const string eqName = "="; // equality
    internal const string lessName = "lt";
    internal const string greaterName = "gt";
    internal const string atmostName = "le";
    internal const string atleastName = "ge";
    internal const string TRUEName = "$true"; // nullary predicate that is always true
    internal const string FALSEName = "$false"; // nullary predicate that is always false
    internal const string subtypeName = "UOrdering2";
    internal const string subtypeArgsName = "UOrdering3";

    internal const string boolTrueName = "boolTrue";
    internal const string boolFalseName = "boolFalse";
    internal const string boolIteName = "ite";
    internal const string intAddName = "intAdd";
    internal const string intSubName = "intSub";
    internal const string intMulName = "intMul";
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
      //Contract.Requires(node != null);
      //Contract.Requires(options != null);
      if (options.AsTerm) {

        if (node == VCExpressionGenerator.True)
          wr.Write("{0}", boolTrueName);
        else if (node == VCExpressionGenerator.False)
          wr.Write("{0}", boolFalseName);
        else if (node is VCExprIntLit) {
          BigNum lit = ((VCExprIntLit)node).Val;
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
      //Contract.Requires(node != null);
      //Contract.Requires(options != null);
      
      VCExprOp op = node.Op;
      Contract.Assert(op!=null);

      if (!options.AsTerm &&
          (op.Equals(VCExpressionGenerator.AndOp) ||
           op.Equals(VCExpressionGenerator.OrOp))) {
        // handle these operators without recursion

        var sop = op.Equals(VCExpressionGenerator.AndOp) ? andName : orName;
        wr.Write("(");
        IEnumerator enumerator = new VCExprNAryUniformOpEnumerator (node);
        Contract.Assert(enumerator!=null);
        var cnt = 0;
        while (enumerator.MoveNext()) {
          VCExprNAry naryExpr = enumerator.Current as VCExprNAry;
          if (naryExpr == null || !naryExpr.Op.Equals(op)) {
            if (cnt > 0)
              wr.Write(" {0} ", sop);
            cnt++;
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
      //Contract.Requires(node != null);
      //Contract.Requires(options != null);
      string printedName = Namer.GetName(node, MakeIdPrintable(Lowercase(node.Name)));
      Contract.Assert(printedName!=null);

      if (options.AsTerm ||
          // formula variables are easy to identify in SMT-Lib
          printedName[0] == '$')
        wr.Write("{0}", printedName);
      else
        wr.Write("({0} = {1})", printedName, boolTrueName);

      return true;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprQuantifier node, LineariserOptions options) {
      //Contract.Requires(node != null);
      //Contract.Requires(options != null);
      AssertAsFormula(node.Quan.ToString(), options);
     Contract.Assert(node.TypeParameters.Count == 0);

      Namer.PushScope(); try {

      string kind = node.Quan == Quantifier.ALL ? "!" : "?";
      wr.Write("{0} [", kind);

      for (int i = 0; i < node.BoundVars.Count; i++) 
        {
          VCExprVar var = node.BoundVars[i];
          Contract.Assert(var!=null);
          // ensure that the variable name starts with ?
          string printedName = Namer.GetLocalName(var, "V" + MakeIdPrintable(var.Name));
        Contract.Assert(printedName!=null);
         Contract.Assert(printedName[0] == 'V');
         if (i > 0) wr.Write(",");
          wr.Write("{0}", printedName);
        }

      wr.Write("] : (");
        
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

      // WriteTriggers(node.Triggers, options);
      wr.Write(")");

      return true;

      } finally {
        Namer.PopScope();
      }
    }

    

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLet node, LineariserOptions options) {
      throw new NotImplementedException();
    }

    /////////////////////////////////////////////////////////////////////////////////////

    // Lineariser for operator terms. The result (bool) is currently not used for anything
    internal class TPTPOpLineariser : IVCExprOpVisitor<bool, LineariserOptions/*!*/> {
      private readonly TPTPExprLineariser ExprLineariser;
      private readonly TextWriter wr;
      [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(wr!=null);
        Contract.Invariant(ExprLineariser!=null);
}


      public TPTPOpLineariser(TPTPExprLineariser ExprLineariser, TextWriter wr) {
        Contract.Requires(ExprLineariser != null);
        Contract.Requires(wr != null);
        this.ExprLineariser = ExprLineariser;
        this.wr = wr;
      }

      ///////////////////////////////////////////////////////////////////////////////////
     
      private void WriteApplication(string op, IEnumerable<VCExpr/*!>!*/> args,
                                    LineariserOptions options) {
      Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(args ));
      Contract.Requires(options != null);
        WriteApplication(op, args, options, options.AsTerm);
      }

      private void WriteTermApplication(string op, IEnumerable<VCExpr/*!>!*/> args,
                                        LineariserOptions options) {
        Contract.Requires(op != null);
      Contract.Requires(cce.NonNullElements(args ));
      Contract.Requires(options != null);
        ExprLineariser.AssertAsTerm(op, options);
        WriteApplication(op, args, options, options.AsTerm);
      }

   
      private void WriteApplication(string termOp,
                                    IEnumerable<VCExpr>/*!>!*/ args, LineariserOptions options,
                                    // change the AsTerm option for the arguments?
                                    bool argsAsTerms) {
        Contract.Requires(termOp != null);
      Contract.Requires(cce.NonNullElements(args ));
      Contract.Requires(options != null);
        LineariserOptions newOptions = options.SetAsTerm(argsAsTerms);
        Contract.Assert(newOptions!=null);

        var argCnt = 0;
        if (termOp == "~") {
          wr.Write("(~ ");
          foreach (var e in args) {
            ExprLineariser.Linearise(e, newOptions);
            argCnt++;
          }
          Contract.Assert(argCnt == 1);
          wr.Write(")");
        } else if ("&|~=><".IndexOf(termOp[0]) >= 0) {
          wr.Write("(");
          foreach (var e in args) {
            ExprLineariser.Linearise(e, newOptions);
            argCnt++;
            if (argCnt == 1) {
              wr.Write(" {0} ", termOp);
            }
          }
          Contract.Assert(argCnt == 2);
          wr.Write(")");
        } else {
          wr.Write(termOp);
          foreach (var e in args) {
            Contract.Assert(e != null);
            if (argCnt == 0)
              wr.Write("(");
            else
              wr.Write(", ");
            argCnt++;
            ExprLineariser.Linearise(e, newOptions);            
          }

          if (argCnt > 0)
            wr.Write(")");
        }
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
          wr.Write("(", eqName);

        WriteApplication(termOp, args, options, true);

        if (!options.AsTerm)
          wr.Write(" = {0})", boolTrueName);
      }

      ///////////////////////////////////////////////////////////////////////////////////
      
      public bool VisitNotOp      (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
        WriteApplication(notName, node, options);      // arguments can be both terms and formulas
        return true;
      }

      private bool PrintEq(VCExprNAry node, LineariserOptions options) {
        Contract.Requires(node != null);
        Contract.Requires(options != null);
        if (options.AsTerm) {
          throw new NotImplementedException();
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
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
        return PrintEq(node, options);
      }

      public bool VisitNeqOp      (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
        wr.Write("(~ ");
        PrintEq(node, options);
        wr.Write(")");
        return true;
      }

      public bool VisitAndOp      (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       Contract.Assert(options.AsTerm);
        WriteApplication(andName, node, options);
        return true;
      }

      public bool VisitOrOp       (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
        
        Contract.Assert(options.AsTerm);
        WriteApplication(orName, node, options);
        return true;
      }

      public bool VisitImpliesOp  (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteApplication(impliesName, node, options);
        return true;
      }

      public bool VisitIfThenElseOp  (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
        throw new NotImplementedException();
      }

      public bool VisitCustomOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);

        VCExprCustomOp op = (VCExprCustomOp)node.Op;
        WriteApplicationTermOnly(op.Name, node, options);
        return true;
      }

      public bool VisitDistinctOp (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        ExprLineariser.AssertAsFormula("distinct", options);
        
        if (node.Length < 2) {
          ExprLineariser.Linearise(VCExpressionGenerator.True, options);
        } else {
          var bits = 0;
          var cnt = node.Length;
          while (cnt > 0) {
            cnt >>= 1;
            bits++;
          }

          wr.Write("($true ");
          foreach (VCExpr e in node) {
            for (var i = 0; i < bits; ++i) {
              var neg = (cnt & (1 << i)) != 0 ? "~" : "";
              wr.Write(" & {0}distinct__f__{1}(", neg, i);
              ExprLineariser.LineariseAsTerm(e, options);
              wr.Write(")");
            }
            wr.WriteLine();
            cnt++;
          }
          wr.Write(")");
        }

        return true;
      }

      public bool VisitLabelOp    (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
        //Contract.Requires(node.Length>=1);
        // VCExprLabelOp! op = (VCExprLabelOp)node.Op;
        // TODO
        //        wr.Write(String.Format("({0} |{1}| ", op.pos ? "LBLPOS" : "LBLNEG", op.label));
        ExprLineariser.Linearise(node[0], options);
        //        wr.Write(")");
        return true;
      }

      public bool VisitSelectOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        var name = Lowercase(SimplifyLikeExprLineariser.SelectOpName(node));
        wr.Write(name + "(");
        var cnt = 0;
        foreach (VCExpr/*!*/ e in node) {
          Contract.Assert(e != null);
          if (cnt++ > 0)
            wr.Write(", ");
          ExprLineariser.Linearise(e, options.SetAsTerm(!e.Type.IsBool));
        }
        wr.Write(")");
        return true;
      }

      public bool VisitStoreOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        var name = Lowercase(SimplifyLikeExprLineariser.StoreOpName(node));
        wr.Write(name + "(");
        var cnt = 0;
        foreach (VCExpr e in node) {
          Contract.Assert(e != null);
          if (cnt++ > 0)
            wr.Write(", ");
          ExprLineariser.Linearise(e, options.SetAsTerm(!e.Type.IsBool));
        }
        wr.Write(")");
        return true;
      }

      public bool VisitBvOp       (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
       {Contract.Assert(false);  throw new NotImplementedException();}       // TODO
      }

      public bool VisitBvExtractOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
       {Contract.Assert(false);  throw new NotImplementedException();}       // TODO
      }

      public bool VisitBvConcatOp (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
       {Contract.Assert(false);  throw new NotImplementedException();}       // TODO
      }

      public bool VisitAddOp            (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteTermApplication(intAddName, node, options);
        return true;
      }

      public bool VisitSubOp            (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteTermApplication(intSubName, node, options);
        return true;
      }

      public bool VisitMulOp            (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteTermApplication(intMulName, node, options);
        return true;
      }

      public bool VisitDivOp            (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteTermApplication(intDivName, node, options);
        return true;
      }

      public bool VisitModOp            (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteTermApplication(intModName, node, options);
        return true;
      }

      public bool VisitLtOp             (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteApplication(lessName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitLeOp             (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteApplication(atmostName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitGtOp             (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteApplication(greaterName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitGeOp             (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteApplication(atleastName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitSubtypeOp        (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteApplication(subtypeName, node, options, true);               // arguments are always terms
        return true;
      }

      public bool VisitSubtype3Op        (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        WriteApplication(subtypeArgsName, node, options, true);               // arguments are always terms
        return true;
      }

      public bool VisitBoogieFunctionOp (VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
       
        VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp)node.Op;
        Contract.Assert(op!=null);
        string printedName = ExprLineariser.Namer.GetName(op.Func, Lowercase(op.Func.Name));
        Contract.Assert(printedName!=null);

        if (ExprLineariser.Options.UsePredicates && op.Func.OutParams[0].TypedIdent.Type.IsBool)
          WriteApplication(printedName, node, options, true);
        else
          // arguments are always terms
          WriteApplicationTermOnly(printedName, node, options);
        return true;
      }
      
    }
  }

}
