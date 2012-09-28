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
      "Int", "Real", "*", "/", "-", "+", "<", "<=", ">", ">=", "div", "mod",
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
      "rotate_left", "rotate_right", "ext_rotate_left", "ext_rotate_right", "int2bv", "bv2int",
      // floating point
      "plusInfinity", "minusInfinity", "NaN", 
      "roundNearestTiesToEven", "roundNearestTiesToAway", "roundTowardPositive", "roundTowardNegative", "roundTowardZero", 
      "+", "-", "/", "*", "==", "<", ">", "<=", ">=", 
      "abs", "remainder", "fusedMA", "squareRoot", "roundToIntegral", 
      "isZero", "isNZero", "isPZero", "isSignMinus", "min", "max", "asFloat", 
      // SMT v1 stuff
      "flet", "implies", "!=", "if_then_else",
      // Z3 extensions
      "lblneg", "lblpos", "lbl-lit",
      "if", "&&", "||", "equals", "equiv", "bool",
      // Boogie-defined
      "real_pow", "UOrdering2", "UOrdering3", 
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

    static string NonKeyword(string s)
    {
      if (reservedSmtWords.Contains(s) || char.IsDigit(s[0]))
        s = "q@" + s;

      // | and \ are illegal even in quoted identifiers
      if (s.IndexOf('|') >= 0)
        s = s.Replace("|", "_");

      if (s.IndexOf('\\') >= 0)
        s = s.Replace("\\", "_");

      return s;
    }

    public static string LabelVar(string s)
    {
      return "%lbl%" + s;
    }

    public static string QuoteId(string s)
    {
      return AddQuotes(NonKeyword(s));
    }

    public override string GetQuotedLocalName(object thingie, string inherentName)
    {
      return AddQuotes(base.GetLocalName(thingie, NonKeyword(inherentName)));
    }

    public override string GetQuotedName(object thingie, string inherentName)
    {
      return AddQuotes(base.GetName(thingie, NonKeyword(inherentName)));
    }

    public SMTLibNamer()
    {
      this.Spacer = "@@";
      InitSymbolLists();
    }
  }
}
