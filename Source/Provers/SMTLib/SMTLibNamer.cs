using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibNamer : UniqueNamer
  {
    // The following Boogie ID characters are not SMT ID characters: `'\#    
    const string idCharacters = "~!@$%^&*_-+=<>.?/";


    static string[] reservedSmtWordsList = 
    { // Basic symbols:
      "", "!", "_", "as", "DECIMAL", "exists", "forall", "let", "NUMERAL", "par", "STRING", 
      // Commands:
      "assert", "check-sat", "declare-sort", "declare-fun", "define-sort,", "define-fun", "exit",
      "get-assertions", "get-assignment", "get-info", "get-option,", "get-proof", "get-unsat-core",
      "get-value", "pop", "push", "set-logic", "set-info", "set-option",
      // Core theory:
      "and", "or", "not", "iff", "true", "false", "xor", "distinct", "ite", "=", "Bool",
      "=>", // implies (sic!)
      // Integers and reals
      "Int", "Real", "*", "/", "-", "~", "+", "<", "<=", ">", ">=", "div", "mod", "rem",
      "^", "sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh", "pi", "euler",
      "to_real", "to_int", "is_int",
      // Bitvectors
      "extract", "concat", 
      "bvnot", "bvneg", "bvand", "bvor", "bvadd", "bvmul", "bvudiv", "bvurem", "bvshl", "bvlshr", "bvult",
      // arrays
      "store", "select", "const", "default", "map", "union", "intersect", "difference", "complement",
      "subset", "array-ext", "as-array", "Array",
      // Z3 (and not only?) extensions to bitvectors
      "bit1", "bit0", "bvsub", "bvsdiv", "bvsrem", "bvsmod", "bvsdiv0", "bvudiv0", "bvsrem0", "bvurem0",
      "bvsmod0", "bvsdiv_i", "bvudiv_i", "bvsrem_i", "bvurem_i", "bvumod_i", "bvule", "bvsle", "bvuge",
      "bvsge", "bvslt", "bvugt", "bvsgt", "bvxor", "bvnand", "bvnor", "bvxnor", "sign_extend", "zero_extend", 
      "repeat", "bvredor", "bvredand", "bvcomp", "bvumul_noovfl", "bvsmul_noovfl", "bvsmul_noudfl", "bvashr",
      "rotate_left", "rotate_right", "ext_rotate_left", "ext_rotate_right", "int2bv", "bv2int", "mkbv",
      // floating point (FIXME: Legacy, remove this)
      "plusInfinity", "minusInfinity",
      "+", "-", "/", "*", "==", "<", ">", "<=", ">=", 
      "abs", "remainder", "fusedMA", "squareRoot", "roundToIntegral", 
      "isZero", "isNZero", "isPZero", "isSignMinus", "min", "max", "asFloat", 
      // SMT v1 stuff (FIXME: Legacy, remove this)
      "flet", "implies", "!=", "if_then_else",
      // Z3 extensions
      "lblneg", "lblpos", "lbl-lit",
      "if", "&&", "||", "equals", "equiv", "bool", "minimize", "maximize",
      // Boogie-defined
      "real_pow", "UOrdering2", "UOrdering3", 
      // Floating point (final draft SMTLIB-v2.5)
      "NaN",
      "fp.abs", "fp.neg", "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.fma", "fp.sqrt", "fp.rem", "fp.roundToIntegral",
      "fp.min", "fp.max", "fp.leq", "fp.lt", "fp.geq", "fp.gt", "fp.eq",
      "fp.isNormal", "fp.isSubnormal", "fp.isZero", "fp.isInfinite", "fp.isNaN", "fp.isNegative", "fp.isPositive",
      "fp", "fp.to_ubv", "fp.to_sbv", "to_fp",
      // Rounding mode
      "rmode",
      "roundNearestTiesToEven", "roundNearestTiesToAway", "roundTowardPositive", "roundTowardNegative", "roundTowardZero",
      "RNE", "RNA", "RTP", "RTN", "RTZ",
    };

    static HashSet<string> reservedSmtWords;
    static bool[] validIdChar;
    static bool symbolListsInitilized;

    static void InitSymbolLists()
    {
      lock (reservedSmtWordsList) {
        // don't move out, c.f. http://en.wikipedia.org/wiki/Double-checked_locking
        if (symbolListsInitilized)
          return;
        reservedSmtWords = new HashSet<string>();
        foreach (var w in reservedSmtWordsList)
          reservedSmtWords.Add(w);
        validIdChar = new bool[255];
        for (int i = 0; i < validIdChar.Length; ++i)
          validIdChar[i] = char.IsLetterOrDigit((char)i) || idCharacters.IndexOf((char)i) >= 0;
        symbolListsInitilized = true;
      }
    }

    static string AddQuotes(string s)
    {
      var allGood = true;

      foreach (char ch in s) {
        var c = (int)ch;
        if (c >= validIdChar.Length || !validIdChar[c]) {
          allGood = false;
          break;
        }
      }

      if (allGood)
        return s;

      return "|" + s + "|";
    }

    static string FilterReserved(string s)
    {
      // Note symbols starting with ``.`` and ``@`` are reserved for internal
      // solver use in SMT-LIBv2 however if we check for the first character
      // being ``@`` then Boogie's tests fail spectacularly because they are
      // used for labels so we don't check for it here. It hopefully won't matter
      // in practice because ``@`` cannot be legally used in Boogie identifiers.
      if (reservedSmtWords.Contains(s) || char.IsDigit(s[0]) || s[0] == '.')
        s = "q@" + s;

      // | and \ are illegal even in quoted identifiers
      if (s.IndexOf('|') >= 0)
        s = s.Replace("|", "_");

      if (s.IndexOf('\\') >= 0)
        s = s.Replace("\\", "_");

      return s;
    }

    public IDictionary<string/*!*/, string/*!*/>/*!*/ LabelCounters; // Absy id -> local id
    public IDictionary<string/*!*/, string/*!*/>/*!*/ CounterToLabels; // local id -> Absy id
    private int CurrentLabelId;

    public override void ResetLabelCount()
    {
      LabelCounters = new Dictionary<string, string>();
      CounterToLabels = new Dictionary<string, string>();
      CurrentLabelId = 0;
    }

    public override string LabelVar(string s)
    {
      return "%lbl%" + LabelName(s);
    }

    public override string LabelName(string s)
    {

      if (s[0] == '+' || s[0] == '@') {
       return s[0] + AbsyIndexToLocalIndex(s.Substring(1));
      } else {
        return AbsyIndexToLocalIndex(s);
      }
    }
    
    private string AbsyIndexToLocalIndex (string s) { 
      string counter;
      if (!LabelCounters.TryGetValue(s, out counter)) { 
        counter = CurrentLabelId.ToString();
        CurrentLabelId++;
        LabelCounters[s] = counter;
        CounterToLabels[counter] = s;
      }
      return counter;
    }

    public override string AbsyLabel(string s)
    {
      if (s[0] == '+' || s[0] == '@') {
        return s[0] + cce.NonNull(CounterToLabels[s.Substring(1)]);
      } else {
        return cce.NonNull(CounterToLabels[s.Substring(1)]);
      }
    }

    public static string QuoteId(string s)
    {
      return AddQuotes(FilterReserved(s));
    }

    public override string GetQuotedLocalName(object thingie, string inherentName)
    {
      return AddQuotes(base.GetLocalName(thingie, FilterReserved(inherentName)));
    }

    public override string GetQuotedName(object thingie, string inherentName)
    {
      return AddQuotes(base.GetName(thingie, FilterReserved(inherentName)));
    }

    public SMTLibNamer()
    {
      this.Spacer = "@@";
      InitSymbolLists();
      LabelCounters = new Dictionary<string, string>();
      CounterToLabels = new Dictionary<string, string>();
      CurrentLabelId = 0;
    }

    private SMTLibNamer(SMTLibNamer namer) : base(namer) { }

    public override object Clone()
    {
      return new SMTLibNamer(this);
    }

    public override void Reset()
    {
      LabelCounters.Clear();
      CounterToLabels.Clear();
      CurrentLabelId = 0;
      base.Reset();
    }
  }
}
