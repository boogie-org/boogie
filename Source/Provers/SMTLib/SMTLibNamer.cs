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
      // Integers
      "Int", "*", "/", "-", "+", "<", "<=", ">", ">=",
      // SMT v1 stuff
      "flet", "implies", "!=", "if_then_else",
      // Z3 extensions
      "lblneg", "lblpos", "lbl-lit",
      "if", "&&", "||", "equals", "equiv", "bool",
    };

    static Dictionary<string, bool> reservedSmtWords;
    static bool[] validIdChar;
    static bool symbolListsInitilized;

    static void InitSymbolLists()
    {
      if (symbolListsInitilized)
        return;

      lock (reservedSmtWordsList) {
        if (symbolListsInitilized)
          return;
        reservedSmtWords = new Dictionary<string, bool>();
        foreach (var w in reservedSmtWordsList)
          reservedSmtWords.Add(w, true);
        validIdChar = new bool[255];
        for (int i = 0; i < validIdChar.Length; ++i)
          validIdChar[i] = char.IsLetterOrDigit((char)i) || idCharacters.IndexOf((char)i) >= 0;
        System.Threading.Thread.MemoryBarrier(); // c.f. http://en.wikipedia.org/wiki/Double-checked_locking
        symbolListsInitilized = true;
      }
    }

    static string AddQuotes(string s)
    {
      InitSymbolLists();

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
      InitSymbolLists();

      if (reservedSmtWords.ContainsKey(s) || char.IsDigit(s[0]))
        s = "q@" + s;

      // | and \ are illegal even in quoted identifiers
      if (s.IndexOf('|') >= 0)
        s = s.Replace("|", "");

      if (s.IndexOf('\\') >= 0)
        s = s.Replace("\\", "");

      return s;
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
    }
  }
}
