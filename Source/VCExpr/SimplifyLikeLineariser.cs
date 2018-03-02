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

// a naive method to turn VCExprs into strings that can be fed into Simplify

namespace Microsoft.Boogie.VCExprAST {
  [ContractClassFor(typeof(LineariserOptions))]
  public abstract class LinOptContracts : LineariserOptions {
    public LinOptContracts()
      : base(true) {
    }
    public override LineariserOptions SetAsTerm(bool newVal) {
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);
      throw new NotImplementedException();
    }

  }

  // Options for the linearisation. Here one can choose, for instance,
  // whether Simplify or Z3 output is to be produced
  [ContractClass(typeof(LinOptContracts))]
  public abstract class LineariserOptions {

    public readonly bool AsTerm;
    public abstract LineariserOptions/*!*/ SetAsTerm(bool newVal);

    public abstract bool QuantifierIds {
      get;
    }

    public virtual bool UseWeights {
      get {
        return false;
      }
    }

    public virtual bool InverseImplies {
      get {
        return false;
      }
    }

    // whether to include type specifications in quantifiers
    public abstract bool UseTypes {
      get;
    }

    // variables representing formulas in let-bindings have to be
    // printed in a different way than other variables
    public virtual List<VCExprVar/*!*/>/*!*/ LetVariables {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
        return EmptyList;
      }
    }

    public virtual LineariserOptions AddLetVariable(VCExprVar furtherVar) {
      Contract.Requires(furtherVar != null);
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);
      return this;
    }

    public virtual LineariserOptions AddLetVariables(List<VCExprVar/*!*/>/*!*/ furtherVars) {
      Contract.Requires(cce.NonNullElements(furtherVars));
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);
      return this;
    }

    private static readonly List<VCExprVar/*!*/>/*!*/ EmptyList = new List<VCExprVar/*!*/>();
    [ContractInvariantMethod]
    void ObjectInvarinat() {
      Contract.Invariant(EmptyList != null);
    }

    ////////////////////////////////////////////////////////////////////////////////////////

    protected LineariserOptions(bool asTerm) {
      this.AsTerm = asTerm;
    }

    public static readonly LineariserOptions SimplifyDefault = new SimplifyOptions(false);
    internal static readonly LineariserOptions SimplifyDefaultTerm = new SimplifyOptions(true);

    ////////////////////////////////////////////////////////////////////////////////////////

    private class SimplifyOptions : LineariserOptions {
      internal SimplifyOptions(bool asTerm)
        : base(asTerm) {

      }
      public override bool QuantifierIds {
        get {
          return false;
        }
      }
      public override bool UseTypes {
        get {
          return false;
        }
      }
      public override LineariserOptions SetAsTerm(bool newVal) {
        Contract.Ensures(Contract.Result<LineariserOptions>() != null);
        if (newVal)
          return SimplifyDefaultTerm;
        else
          return SimplifyDefault;
      }
    }
  }

  ////////////////////////////////////////////////////////////////////////////////////////

  // Lineariser for expressions. The result (bool) is currently not used for anything
  public class SimplifyLikeExprLineariser : IVCExprVisitor<bool, LineariserOptions/*!*/> {

    public static string ToSimplifyString(VCExpr e, UniqueNamer namer) {
      Contract.Requires(namer != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<string>() != null);
      return ToString(e, LineariserOptions.SimplifyDefault, namer);
    }

    public static string ToString(VCExpr/*!*/ e, LineariserOptions/*!*/ options, UniqueNamer/*!*/ namer) {
      Contract.Requires(e != null);
      Contract.Requires(options != null);
      Contract.Requires(namer != null);
      Contract.Ensures(Contract.Result<string>() != null);

      StringWriter sw = new StringWriter();
      SimplifyLikeExprLineariser lin = new SimplifyLikeExprLineariser(sw, namer);
      lin.Linearise(e, options);
      return sw.ToString();
    }

    ////////////////////////////////////////////////////////////////////////////////////////

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(wr != null);
      Contract.Invariant(Namer != null);
    }

    private readonly TextWriter/*!*/ wr;
    private SimplifyLikeOpLineariser OpLinObject = null;
    private IVCExprOpVisitor<bool, LineariserOptions/*!*/>/*!*/ OpLineariser {
      get {
        Contract.Ensures(Contract.Result<IVCExprOpVisitor<bool, LineariserOptions>>() != null);
        if (OpLinObject == null)
          OpLinObject = new SimplifyLikeOpLineariser(this, wr);
        return OpLinObject;
      }
    }

    internal readonly UniqueNamer Namer;

    public SimplifyLikeExprLineariser(TextWriter wr, UniqueNamer namer) {
      Contract.Requires(namer != null);
      Contract.Requires(wr != null);
      this.wr = wr;
      this.Namer = namer;
    }

    public void Linearise(VCExpr expr, LineariserOptions options) {
      Contract.Requires(options != null);
      Contract.Requires(expr != null);
      expr.Accept<bool, LineariserOptions>(this, options);
    }

    public void LineariseAsTerm(VCExpr expr, LineariserOptions options) {
      Contract.Requires(options != null);
      Contract.Requires(expr != null);
      Linearise(expr, options.SetAsTerm(true));
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public static string MakeIdPrintable(string s) {
      Contract.Requires(s != null);
      Contract.Requires(s != "");
      Contract.Ensures(Contract.Result<string>() != null);
      // make sure that no keywords are used as identifiers
      switch (s) {
        case andName:
        case orName:
        case notName:
        case impliesName:
        case iffName:
        case eqName:
        case neqName:
        case distinctName:
        case TRUEName:
        case FALSEName:
          s = "nonkeyword_" + s;
          break;
      }

      if (CommandLineOptions.Clo.BracketIdsInVC == 0) {
        // In this form, we go with any identifier, so we don't ever bother about brackets.
        // Except: @true and @false are always written with brackets
        return s;
      }
      bool looksLikeOperator = true;
      bool looksLikeSimpleId = true;
      bool useBrackets = false;
      foreach (char ch in s) {
        switch (ch) {
          case '=':
          case '<':
          case '>':
          case '+':
          case '-':
          case '*':
          case '/':
          case '%':
          case ':':
            // looks like operator, not simple id
            looksLikeSimpleId = false;
            break;
          default:
            if (Char.IsLetterOrDigit(ch)) {
              // looks like simple id, not operator
              looksLikeOperator = false;
            } else {
              // looks like neither operator nor simple id
              looksLikeOperator = false;
              looksLikeSimpleId = false;
            }
            break;
        }
        if (!looksLikeOperator && !looksLikeSimpleId) {
          useBrackets = true;
          break;
        }
      }
      if (useBrackets) {
        return "|" + s + "|";
      } else {
        return s;
      }
    }

    private static void TypeToStringHelper(Type t, StringBuilder sb) {
      Contract.Requires(t != null);

      TypeSynonymAnnotation syn = t as TypeSynonymAnnotation;
      if (syn != null) {
        TypeToStringHelper(syn.ExpandedType, sb);
      } else {
        if (t.IsMap) {
          MapType m = t.AsMap;
          sb.Append('[');
          for (int i = 0; i < m.MapArity; ++i) {
            if (i != 0)
              sb.Append(',');
            TypeToStringHelper(m.Arguments[i], sb);
          }
          sb.Append(']');
          TypeToStringHelper(m.Result, sb);
        } else if (t.IsBool || t.IsInt || t.IsBv) {
          sb.Append(TypeToString(t));
        } else {
          System.IO.StringWriter buffer = new System.IO.StringWriter();
          using (TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, /*setTokens=*/ false, /*pretty=*/ false)) {
            t.Emit(stream);
          }
          sb.Append(buffer.ToString());
        }
      }

    }


    public static string TypeToString(Type t) {
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<string>() != null);

      if (t.IsBool)
        return "$bool";
      else if (t.IsInt)
        return "$int";
      else if (t.IsBv)
        return "$bv" + t.BvBits;
      else {
        StringBuilder sb = new StringBuilder();
        TypeToStringHelper(t, sb);
        return sb.ToString();
      }
    }

    public static string BvConcatOpName(VCExprNAry node) {
      Contract.Requires(node != null);
      Contract.Requires((node.Op is VCExprBvConcatOp));
      Contract.Ensures(Contract.Result<string>() != null);
      int bits1 = node[0].Type.BvBits;
      int bits2 = node[1].Type.BvBits;
      return "$bv" + (bits1 + bits2) + "_concat[" + bits1 + "." + bits2 + "]";
    }

    public static string BvExtractOpName(VCExprNAry node) {
      Contract.Requires(node != null);
      Contract.Requires(node.Op is VCExprBvExtractOp);
      Contract.Ensures(Contract.Result<string>() != null);
      VCExprBvExtractOp op = (VCExprBvExtractOp)node.Op;
      return "$bv" + node.Type.BvBits + "_extract" + op.Total + "[" + op.Start + ":" + op.End + "]";
    }

    public static string StoreOpName(VCExprNAry node) {
      Contract.Requires(node != null);
      Contract.Requires((node.Op is VCExprSelectOp) || (node.Op is VCExprStoreOp));
      Contract.Ensures(Contract.Result<string>() != null);
      return "Store_" + TypeToString(node[0].Type);
    }

    public static string SelectOpName(VCExprNAry node) {
      Contract.Requires(node != null);
      Contract.Requires((node.Op is VCExprSelectOp) || (node.Op is VCExprStoreOp));
      Contract.Ensures(Contract.Result<string>() != null);
      return "Select_" + TypeToString(node[0].Type);
    }

    internal void WriteId(string s) {
      Contract.Requires(s != null);
      wr.Write(MakeIdPrintable(s));
    }

    /////////////////////////////////////////////////////////////////////////////////////

    /// <summary>
    /// The name for logical conjunction in Simplify
    /// </summary>
    internal const string andName = "AND"; // conjunction
    internal const string orName = "OR"; // disjunction
    internal const string notName = "NOT"; // negation
    internal const string impliesName = "IMPLIES"; // implication
    internal const string iffName = "IFF"; // logical equivalence
    internal const string eqName = "EQ"; // equality
    internal const string neqName = "NEQ"; // inequality
    internal const string lessName = "<";
    internal const string greaterName = ">";
    internal const string atmostName = "<=";
    internal const string atleastName = ">=";
    internal const string TRUEName = "TRUE"; // nullary predicate that is always true
    internal const string FALSEName = "FALSE"; // nullary predicate that is always false
    internal const string subtypeName = "<:";
    internal const string subtypeArgsName = "<::";

    internal const string distinctName = "DISTINCT";
    /// <summary>
    /// name of the main inclusion relation
    /// </summary>
    internal const string boolTrueName = "|@true|";
    internal const string boolFalseName = "|@false|";
    internal const string boolAndName = "boolAnd";
    internal const string boolOrName = "boolOr";
    internal const string boolNotName = "boolNot";
    internal const string termEqName = "anyEqual";
    internal const string termNeqName = "anyNeq";
    internal const string termLessName = "intLess";
    internal const string termGreaterName = "intGreater";
    internal const string termAtmostName = "intAtMost";
    internal const string termAtleastName = "intAtLeast";
    internal const string intAddName = "+";
    internal const string intAddNameReflect = "Reflect$Add";
    internal const string intSubName = "-";
    internal const string intMulName = "*";
    internal const string intDivName = "/";
    internal const string intModName = "%";
    internal const string realAddName = "realAdd";
    internal const string realSubName = "realSub";
    internal const string realMulName = "realMul";
    internal const string realDivName = "realDiv";
    internal const string floatAddName = "floatAdd";
    internal const string floatSubName = "floatSub";
    internal const string floatMulName = "floatMul";
    internal const string floatDivName = "floatDiv";
    internal const string floatLeqName = "floatLeq";
    internal const string floatLtName = "floatLt";
    internal const string floatGeqName = "floatGeq";
    internal const string floatGtName = "floatGt";
    internal const string floatEqName = "floatEq";
    internal const string floatNeqName = "floatNeq";
    internal const string realPowName = "realPow";
    internal const string toIntName = "toIntCoercion";
    internal const string toRealName = "toRealCoercion";
    internal const string toFloatName = "toFloatCoercion";

    internal void AssertAsTerm(string x, LineariserOptions options) {
      Contract.Requires(options != null);
      Contract.Requires(x != null);
      if (!options.AsTerm)
        System.Diagnostics.Debug.Fail("One should never write " + x + " as a formula!");
    }

    internal void AssertAsFormula(string x, LineariserOptions options) {
      Contract.Requires(options != null);
      Contract.Requires(x != null);
      if (options.AsTerm)
        System.Diagnostics.Debug.Fail("One should never write " + x + " as a term!");
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLiteral node, LineariserOptions options) {
      //Contract.Requires(options != null);
      //Contract.Requires(node != null);
      if (options.AsTerm) {

        if (node == VCExpressionGenerator.True)
          wr.Write(options.UseTypes ? TRUEName : boolTrueName);
        else if (node == VCExpressionGenerator.False)
          wr.Write(options.UseTypes ? FALSEName : boolFalseName);
        else if (node is VCExprIntLit) {
          wr.Write(((VCExprIntLit)node).Val);
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }

      } else {

        if (node == VCExpressionGenerator.True)
          wr.Write(TRUEName);
        else if (node == VCExpressionGenerator.False)
          wr.Write(FALSEName);
        else if (node is VCExprIntLit) {
          System.Diagnostics.Debug.Fail("One should never write IntLit as a predicate!");
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }

      }

      return true;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprNAry node, LineariserOptions options) {
      //Contract.Requires(options != null);
      //Contract.Requires(node != null);
      VCExprOp op = node.Op;
      Contract.Assert(op != null);

      if (!options.AsTerm &&
          (op.Equals(VCExpressionGenerator.AndOp) ||
           op.Equals(VCExpressionGenerator.OrOp))) {
        // handle these operators without recursion

        wr.Write("({0}",
                 op.Equals(VCExpressionGenerator.AndOp) ? andName : orName);
        IEnumerator enumerator = new VCExprNAryUniformOpEnumerator(node);
        Contract.Assert(enumerator != null);
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

      return node.Accept<bool, LineariserOptions>(OpLineariser, options);
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprVar node, LineariserOptions options) {
      //Contract.Requires(options != null);
      //Contract.Requires(node != null);
      string printedName = Namer.GetName(node, node.Name);
      Contract.Assert(printedName != null);

      if (options.AsTerm ||
        // variables for formulas bound in a let-binding are never
        // written as an equation
          options.LetVariables.Contains(node) ||
        // if variables are properly typed, they cannot be written as
        // equation either
          options.UseTypes) {
        WriteId(printedName);
      } else {
        wr.Write("({0} ", eqName);
        WriteId(printedName);
        wr.Write(" {0})", boolTrueName);
      }

      return true;
    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprQuantifier node, LineariserOptions options) {
      //Contract.Requires(options != null);
      //Contract.Requires(node != null);
      AssertAsFormula(node.Quan.ToString(), options);
      Contract.Assert(node.TypeParameters.Count == 0);

      Namer.PushScope();
      try {

        string kind = node.Quan == Quantifier.ALL ? "FORALL" : "EXISTS";
        wr.Write("({0} (", kind);

        for (int i = 0; i < node.BoundVars.Count; i++) {
          VCExprVar var = node.BoundVars[i];
          Contract.Assert(var != null);
          string printedName = Namer.GetLocalName(var, var.Name);
          Contract.Assert(printedName != null);
          if (i != 0)
            wr.Write(" ");
          WriteId(printedName);
          if (options.UseTypes)
            wr.Write(" :TYPE {0}", TypeToString(var.Type));
        }
        wr.Write(") ");

        WriteTriggers(node.Triggers, options);

        if (options.QuantifierIds) {
          // only needed for Z3
          VCQuantifierInfos infos = node.Infos;
          Contract.Assert(infos != null);
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
        }

        if (options.UseWeights) {
          int weight = QKeyValue.FindIntAttribute(node.Infos.attributes, "weight", 1);
          if (weight != 1) {
            wr.Write("(WEIGHT ");
            wr.Write(weight);
            wr.Write(") ");
          }
        }

        Linearise(node.Body, options);
        wr.Write(")");

        return true;

      } finally {
        Namer.PopScope();
      }
    }

    private void WriteTriggers(List<VCTrigger/*!*/>/*!*/ triggers, LineariserOptions options) {
      Contract.Requires(options != null);
      Contract.Requires(cce.NonNullElements(triggers));
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
        wr.Write("(PATS");
        foreach (VCTrigger vcTrig in triggers) {
          Contract.Assert(vcTrig != null);
          if (vcTrig.Pos) {
            if (vcTrig.Exprs.Count > 1) {
              wr.Write(" (MPAT");
            }
            foreach (VCExpr e in vcTrig.Exprs) {
              Contract.Assert(e != null);
              wr.Write(" ");
              LineariseAsTerm(e, options);
            }
            if (vcTrig.Exprs.Count > 1) {
              wr.Write(")");
            }
          }
        }
        wr.Write(") ");
      } else if (negTriggers > 0) {
        // if also positive triggers are given, the SMT solver (at least Z3)
        // will ignore the negative patterns and output a warning. Therefore
        // we never specify both negative and positive triggers
        wr.Write("(NOPATS");
        foreach (VCTrigger vcTrig in triggers) {
          Contract.Assert(vcTrig != null);
          if (!vcTrig.Pos) {
            wr.Write(" ");
            Contract.Assert(vcTrig.Exprs.Count == 1);
            LineariseAsTerm(vcTrig.Exprs[0], options);
          }
        }
        wr.Write(") ");
      }

    }

    /////////////////////////////////////////////////////////////////////////////////////

    public bool Visit(VCExprLet node, LineariserOptions options) {
      //Contract.Requires(options != null);
      //Contract.Requires(node != null);
      Namer.PushScope();
      try {

        wr.Write("(LET (");

        LineariserOptions optionsWithVars = options.AddLetVariables(node.BoundVars);
        Contract.Assert(optionsWithVars != null);

        string s = "(";
        foreach (VCExprLetBinding b in node) {
          Contract.Assert(b != null);
          wr.Write(s);
          string printedName = Namer.GetLocalName(b.V, b.V.Name);

          bool formula = b.V.Type.IsBool;
          if (formula)
            wr.Write("FORMULA ");
          else
            wr.Write("TERM ");
          WriteId(printedName);
          wr.Write(" ");
          Linearise(b.E, optionsWithVars.SetAsTerm(!formula));
          wr.Write(")");
          s = " (";
        }
        wr.Write(") ");
        Linearise(node.Body, optionsWithVars);
        wr.Write(")");

        return true;

      } finally {
        Namer.PopScope();
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////

    // Lineariser for operator terms. The result (bool) is currently not used for anything
    internal class SimplifyLikeOpLineariser : IVCExprOpVisitor<bool, LineariserOptions/*!*/> {
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(ExprLineariser != null);
        Contract.Invariant(wr != null);
      }

      private readonly SimplifyLikeExprLineariser/*!*/ ExprLineariser;
      private readonly TextWriter/*!*/ wr;

      public SimplifyLikeOpLineariser(SimplifyLikeExprLineariser ExprLineariser, TextWriter wr) {
        Contract.Requires(wr != null);
        Contract.Requires(ExprLineariser != null);
        this.ExprLineariser = ExprLineariser;
        this.wr = wr;
      }

      ///////////////////////////////////////////////////////////////////////////////////

      private void WriteApplication(string op, IEnumerable<VCExpr/*!*/>/*!*/ args, LineariserOptions options, bool argsAsTerms) {
        Contract.Requires(options != null);
        Contract.Requires(op != null);
        Contract.Requires(cce.NonNullElements(args));
        WriteApplication(op, op, args, options, argsAsTerms);
      }

      private void WriteApplication(string op, IEnumerable<VCExpr/*!*/>/*!*/ args, LineariserOptions options) {
        Contract.Requires(options != null);
        Contract.Requires(op != null);
        Contract.Requires(cce.NonNullElements(args));
        WriteApplication(op, op, args, options, options.AsTerm);
      }

      private void WriteTermApplication(string op, IEnumerable<VCExpr/*!*/>/*!*/ args, LineariserOptions options) {
        Contract.Requires(options != null);
        Contract.Requires(op != null);
        Contract.Requires(cce.NonNullElements(args));
        ExprLineariser.AssertAsTerm(op, options);
        WriteApplication(op, op, args, options, options.AsTerm);
      }

      private void WriteApplication(string termOp, string predOp, IEnumerable<VCExpr/*!*/>/*!*/ args, LineariserOptions options) {
        Contract.Requires(options != null);
        Contract.Requires(predOp != null);
        Contract.Requires(termOp != null);
        Contract.Requires(cce.NonNullElements(args));
        WriteApplication(termOp, predOp, args, options, options.AsTerm);
      }

      private void WriteApplication(string termOp, string predOp, IEnumerable<VCExpr/*!*/>/*!*/ args, LineariserOptions options, bool argsAsTerms) {
        Contract.Requires(options != null);
        Contract.Requires(predOp != null);
        Contract.Requires(termOp != null);
        Contract.Requires(cce.NonNullElements(args));// change the AsTerm option for the arguments?
        wr.Write("({0}", options.AsTerm ? termOp : predOp);

        LineariserOptions newOptions = options.SetAsTerm(argsAsTerms);

        foreach (VCExpr e in args) {
          Contract.Assert(e != null);
          wr.Write(" ");
          ExprLineariser.Linearise(e, newOptions);
        }

        wr.Write(")");
      }

      // write an application that can only be a term.
      // if the expression is supposed to be printed as a formula,
      // it is turned into an equation (EQ (f args) |@true|)
      private void WriteApplicationTermOnly(string termOp, IEnumerable<VCExpr/*!*/>/*!*/ args, LineariserOptions options) {
        Contract.Requires(options != null);
        Contract.Requires(termOp != null);
        Contract.Requires(cce.NonNullElements(args));
        if (!options.AsTerm)
          // Write: (EQ (f args) |@true|)
          // where "args" are written as terms
          wr.Write("({0} ", eqName);

        WriteApplication(termOp, args, options, true);

        if (!options.AsTerm)
          wr.Write(" {0})", boolTrueName);
      }

      ///////////////////////////////////////////////////////////////////////////////////

      public bool VisitNotOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(boolNotName, notName, node, options);      // arguments can be both terms and formulas
        return true;
      }

      public bool VisitEqOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        if (options.AsTerm) {
          // use equality on terms, also if the arguments have type bool
          WriteApplication(termEqName, node, options);
        } else {
          if (node[0].Type.IsBool) {
            Contract.Assert(node[1].Type.IsBool);
            // use equivalence
            WriteApplication(iffName, node, options);
          } else {
            Contract.Assert(!node[1].Type.IsBool);
            // use equality and write the arguments as terms
            WriteApplication(eqName, node, options, true);
          }
        }

        return true;
      }

      public bool VisitNeqOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        if (options.AsTerm) {
          // use equality on terms, also if the arguments have type bool
          WriteApplication(termNeqName, node, options);
        } else {
          if (node[0].Type.IsBool) {
            Contract.Assert(node[1].Type.IsBool);
            // use equivalence and negate the whole thing
            wr.Write("({0} ", notName);
            WriteApplication(iffName, node, options);
            wr.Write(")");
          } else {
            // use equality and write the arguments as terms
            WriteApplication(neqName, node, options, true);
          }
        }

        return true;
      }

      public bool VisitAndOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        Contract.Assert(options.AsTerm);
        WriteApplication(boolAndName, andName, node, options);        // arguments can be both terms and formulas
        return true;
      }

      public bool VisitOrOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        Contract.Assert(options.AsTerm);
        WriteApplication(boolOrName, orName, node, options);        // arguments can be both terms and formulas
        return true;
      }

      public bool VisitImpliesOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        if (options.AsTerm) {
          wr.Write("({0} ({1} ", boolOrName, boolNotName);
          ExprLineariser.Linearise(node[0], options);
          wr.Write(") ");
          ExprLineariser.Linearise(node[1], options);
          wr.Write(")");
        } else if (options.InverseImplies) {
          wr.Write("({0} ", orName);
          ExprLineariser.Linearise(node[1], options);
          wr.Write(" ({0} ", notName);
          ExprLineariser.Linearise(node[0], options);
          wr.Write("))");
        } else {
          WriteApplication(impliesName, node, options);
        }
        return true;
      }

      public bool VisitDistinctOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        ExprLineariser.AssertAsFormula(distinctName, options);

        if (node.Length < 2) {
          ExprLineariser.Linearise(VCExpressionGenerator.True, options);
        } else {
          wr.Write("({0}", distinctName);
          foreach (VCExpr e in node) {
            Contract.Assert(e != null);
            wr.Write(" ");
            ExprLineariser.LineariseAsTerm(e, options);
          }
          wr.Write(")");
        }

        return true;
      }

      public bool VisitLabelOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        VCExprLabelOp op = (VCExprLabelOp)node.Op;
        Contract.Assert(op != null);
        wr.Write(String.Format("({0} |{1}| ", op.pos ? "LBLPOS" : "LBLNEG", op.label));
        ExprLineariser.Linearise(node[0], options);
        wr.Write(")");
        return true;
      }

      public bool VisitSelectOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        wr.Write("(" + SelectOpName(node));
        foreach (VCExpr/*!*/ e in node) {
          Contract.Assert(e != null);
          wr.Write(" ");
          ExprLineariser.Linearise(e, options.SetAsTerm(!e.Type.IsBool));
        }
        wr.Write(")");
        return true;
      }

      public bool VisitStoreOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        wr.Write("(" + StoreOpName(node));
        foreach (VCExpr e in node) {
          Contract.Assert(e != null);
          wr.Write(" ");
          ExprLineariser.Linearise(e, options.SetAsTerm(!e.Type.IsBool));
        }
        wr.Write(")");
        return true;
      }

      public bool VisitFloatAddOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatAddName, node, options);
        return true;
      }

      public bool VisitFloatSubOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatSubName, node, options);
        return true;
      }

      public bool VisitFloatMulOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatMulName, node, options);
        return true;
      }

      public bool VisitFloatDivOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatDivName, node, options);
        return true;
      }

      public bool VisitFloatLeqOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatLeqName, node, options);
        return true;
      }

      public bool VisitFloatLtOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatLtName, node, options);
        return true;
      }

      public bool VisitFloatGeqOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatGeqName, node, options);
        return true;
      }

      public bool VisitFloatGtOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatGtName, node, options);
        return true;
      }

      public bool VisitFloatEqOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatEqName, node, options);
        return true;
      }

      public bool VisitFloatNeqOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(floatNeqName, node, options);
        return true;
      }

      public bool VisitBvOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication("$make_bv" + node.Type.BvBits, node, options);
        return true;
      }

      public bool VisitBvExtractOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(BvExtractOpName(node), node, options);
        return true;
      }

      public bool VisitBvConcatOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(BvConcatOpName(node), node, options);
        return true;
      }

      public bool VisitIfThenElseOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);

        wr.Write("(ITE ");
        ExprLineariser.Linearise(node[0], options.SetAsTerm(false));
        wr.Write(" ");
        ExprLineariser.Linearise(node[1], options);
        wr.Write(" ");
        ExprLineariser.Linearise(node[2], options);
        wr.Write(")");

        return true;
      }

      public bool VisitCustomOp(VCExprNAry/*!*/ node, LineariserOptions/*!*/ options) {
        //Contract.Requires(node != null);
        //Contract.Requires(options != null);
        VCExprCustomOp op = (VCExprCustomOp)node.Op;
        wr.Write("({0}", op.Name);
        foreach (VCExpr arg in node) {
          wr.Write(" ");
          ExprLineariser.Linearise(arg, options);
        }
        wr.Write(")");
        return true;
      }

      public bool VisitAddOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        if (node.Type.IsInt) {
          if (CommandLineOptions.Clo.ReflectAdd) {
            WriteTermApplication(intAddNameReflect, node, options);
          }
          else {
            WriteTermApplication(intAddName, node, options);
          }
        }
        else {
          WriteTermApplication(realAddName, node, options);
        }
        return true;
      }

      public bool VisitSubOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        if (node.Type.IsInt) {
          WriteTermApplication(intSubName, node, options);
        }
        else if (node.Type.IsReal) {
          WriteTermApplication(realSubName, node, options);
        }
        else {
          WriteTermApplication(floatSubName, node, options);
        }
        return true;
      }

      public bool VisitMulOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        if (node.Type.IsInt) {
          WriteTermApplication(intMulName, node, options);
        }
        else if (node.Type.IsReal) {
          WriteTermApplication(realMulName, node, options);
        }
        else {
          WriteTermApplication(floatMulName, node, options);
        }
        return true;
      }

      public bool VisitDivOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(intDivName, node, options);
        return true;
      }

      public bool VisitModOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(intModName, node, options);
        return true;
      }

      public bool VisitRealDivOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(realDivName, node, options);
        return true;
      }

      public bool VisitPowOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteTermApplication(realPowName, node, options);
        return true;
      }

      public bool VisitLtOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(termLessName, lessName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitLeOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(termAtmostName, atmostName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitGtOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(termGreaterName, greaterName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitGeOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(termAtleastName, atleastName, node, options, true);  // arguments are always terms
        return true;
      }

      public bool VisitSubtypeOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(subtypeName, node, options, true);               // arguments are always terms
        return true;
      }

      public bool VisitSubtype3Op(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(subtypeArgsName, node, options, true);               // arguments are always terms
        return true;
      }

      public bool VisitToIntOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(toIntName, node, options);
        return true;
      }

      public bool VisitToRealOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(toRealName, node, options);
        return true;
      }

      public bool VisitToFloatOp(VCExprNAry node, LineariserOptions options)
      {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        WriteApplication(toFloatName, node, options);
        return true;
      }

      public bool VisitBoogieFunctionOp(VCExprNAry node, LineariserOptions options) {
        //Contract.Requires(options != null);
        //Contract.Requires(node != null);
        VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp)node.Op;
        Contract.Assert(op != null);
        string funcName = op.Func.Name;
        Contract.Assert(funcName != null);
        string bvzName = op.Func.FindStringAttribute("external");
        string printedName = ExprLineariser.Namer.GetName(op.Func, funcName);
        Contract.Assert(printedName != null);
        if (bvzName != null)
          printedName = bvzName;

        if (options.UseTypes) {
          // we use term notation for arguments whose type is not bool, and
          // formula notation for boolean arguments

          wr.Write("(");
          ExprLineariser.WriteId(printedName);

          foreach (VCExpr e in node) {
            Contract.Assert(e != null);
            wr.Write(" ");
            ExprLineariser.Linearise(e, options.SetAsTerm(!e.Type.IsBool));
          }

          wr.Write(")");
        } else {
          // arguments are always terms
          WriteApplicationTermOnly(SimplifyLikeExprLineariser.MakeIdPrintable(printedName),
                                   node, options);
        }
        return true;
      }

    }
  }

}
