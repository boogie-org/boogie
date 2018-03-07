//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.Boogie {
  using System;
  using System.IO;
  using System.Collections;
  using System.Diagnostics.Contracts;
  using System.Collections.Generic;
  using System.Linq;
  using System.Text;

  public static class LinqExtender
  {
    public static string Concat(this IEnumerable<string> strings, string separator)
    {
      var sb = new StringBuilder();
      var first = true;
      foreach (var s in strings) {
        if (!first)
          sb.Append(separator);
        first = false;
        sb.Append(s);
      }
      return sb.ToString();
    }

    public static IEnumerable<T> Concat1<T>(this IEnumerable<T> objects, T final)
    {
      foreach (var s in objects) {
        yield return s;
      }
      yield return final;
    }

    public static string MapConcat<T>(this IEnumerable<T> objects, Func<T,string> toString, string separator)
    {
      var sb = new StringBuilder();
      var first = true;
      foreach (var s in objects) {
        if (!first)
          sb.Append(separator);
        first = false;
        sb.Append(toString(s));
      }
      return sb.ToString();
    }

    public static IEnumerable<T> SkipEnd<T>(this IEnumerable<T> source, int count)
    {
      var l = source.ToList();
      if (count >= l.Count)
        return Enumerable.Empty<T>();
      l.RemoveRange(l.Count - count, count);
      return l;
    }

    public static void Iter<T>(this IEnumerable<T> coll, Action<T> fn)
    {
      foreach (var e in coll) fn(e);
    }

    public static IEnumerable<Tuple<TSource1, TSource2>> Zip<TSource1, TSource2>(this IEnumerable<TSource1> source1, IEnumerable<TSource2> source2)
    {
      return source1.Zip(source2, (e1, e2) => new Tuple<TSource1, TSource2>(e1, e2));
    }
  }

  public class TokenTextWriter : IDisposable {
    string/*!*/ filename;
    TextWriter/*!*/ writer;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(filename != null);
      Contract.Invariant(writer != null);
    }

    bool setTokens = true;
    int line = 1;
    int col;
    public bool UseForComputingChecksums;

    private const int indent_size = 2;
    private int most_recent_indent_level = 0;
    protected string Indent(int level) {
      Contract.Ensures(Contract.Result<string>() != null);
      most_recent_indent_level = level;
      return new string(' ', (indent_size * level));
    }


    // Keywords, this array *must* be sorted
    public static readonly string[]/*!*/ BplKeywords =
        {
                "assert",
                "assume",
                "axiom",
                "bool",
                "break",
                "call",
                "cast",
                "const",
                "else",
                "ensures",
                "exists",
                "false",
                "forall",
                "free",
                "function",
                "goto",
                "havoc",
                "if",
                "implementation",
                "int",
                "invariant",
                "modifies",
                "old",
                "procedure",
                "public",
                "requires",
                "return",
                "returns",
                "rmode",
                "true",
                "type",
                "unique",
                "var",
                "where",
                "while",
        };

    // "Pretty" printing: not very efficient, and not necessarily very pretty, but helps a bit 
    private readonly bool pretty;
    
    // The stack of writers in a current separator-block.
    // The string is an optional identifier that allows you
    // to not start a new indentation for e.g. "&&" in "a && b && c".
    // When the pretty printing is finished, this should be empty.
    Stack<KeyValuePair<string, List<TextWriter>>> wstk;

    // The original writer: where everything should finally end up.
    TextWriter actual_writer;

    public bool push(string type = null) {
      if (pretty) {
        if (wstk == null) {
          wstk = new Stack<KeyValuePair<string, List<TextWriter>>>();
          actual_writer = writer;
        }
        if (wstk.Count > 0 && wstk.Peek().Key == type && type != null) {
          sep();
          return false; // don't actually pop this thing (send this bool to pop)
        } else {
          wstk.Push(new KeyValuePair<string, List<TextWriter>>(type, new List<TextWriter> { }));
          sep();
          return true;  // this needs to be popped
        }
      } else {
        return false;
      }
    }

    public void pop(bool do_it = true) {
      if (pretty) {
        if (do_it) {
          List<TextWriter> ws = wstk.Pop().Value;
          // try to figure out if you should insert line breaks between
          // them or print them on one single line
          // this breaks down when there are newlines inserted
          List<String> ss = new List<String>();
          int len = 0;
          foreach (TextWriter w in ws) {
            foreach (String s in w.ToString().Split(new String[] { "\r\n", "\n" }, StringSplitOptions.None)) {
              if (s.Length > 0) {
                ss.Add(s);
                len += s.Length;
                // len = Math.Max(len, s.Length);
              }
            }
          }
          // figure out which is the next writer to use
          List<TextWriter> tw = wstk.Count > 0 ? wstk.Peek().Value : null;
          string indent_string;
          if (tw == null) {
            writer = actual_writer;
            indent_string = new string(' ', indent_size * most_recent_indent_level + indent_size);
          } else {
            writer = tw.Last();
            indent_string = new string(' ', indent_size);
          }
          // write the strings (we would like to know WHERE we are in the document here)
          if (len > 80 /* - wstk.Count * 2 */) {
            for (int i = 0; i < ss.Count; i++) {
              if (i != ss.Count - 1) {
                writer.WriteLine(ss[i]);
                writer.Write(indent_string);
              } else {
                writer.Write(ss[i]);
              }
            }
          } else {
            foreach (String s in ss) {
              writer.Write(s);
            }
          }
        }
      }
    }

    public void sep() {
      if (pretty) {
        List<TextWriter> ws = wstk.Peek().Value;

        writer = new StringWriter();
        wstk.Peek().Value.Add(writer);
      }
    }

    private IToken/*!*/ CurrentToken {
      get {
        Contract.Ensures(Contract.Result<IToken>() != null);

        Token token = new Token();
        token.filename = filename;
        token.line = line;
        token.col = col;
        return token;
      }
    }

    public void SetToken(Absy absy) {
      Contract.Requires(absy != null);
      this.SetToken(t => absy.tok = t);
    }

    public void SetToken(IfThenElse expr)
    {
      Contract.Requires(expr != null);
      this.SetToken(t => expr.tok = t);
    }

    public void SetToken(Action<IToken> setter) {
      Contract.Requires(setter != null);
      if (this.setTokens) {
        setter(this.CurrentToken);
      }
    }

    public void SetToken(ref IToken tok) {
      Contract.Requires(tok != null);
      if (this.setTokens) {
        tok = this.CurrentToken;
      }
    }

    public static string SanitizeIdentifier(string name) {
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<string>() != null);
      int index = Array.BinarySearch(TokenTextWriter.BplKeywords, name);
      if (index >= 0) {
        return "\\" + name;
      } else if (name.Length > 2 && name[0] == 'b' && name[1] == 'v') {
        int dummy;
        return int.TryParse(name.Substring(2), out dummy) ? "\\" + name : name;
      } else if (name.Contains('@')) {
        return SanitizeIdentifier(name.Replace("@", "#AT#"));
      } else {
        return name;
      }
    }

    public TokenTextWriter(string filename)
        : this(filename, false)
    {
    }

    public TokenTextWriter(string filename, bool pretty)
      : base() {
      Contract.Requires(filename != null);
      this.pretty = pretty;
      this.filename = filename;
      this.writer = new StreamWriter(filename);
    }

    public TokenTextWriter(string filename, bool setTokens, bool pretty)
      : base() {
      Contract.Requires(filename != null);
      this.pretty = pretty;
      this.filename = filename;
      this.writer = new StreamWriter(filename);
      this.setTokens = setTokens;
    }

    public TokenTextWriter(string filename, TextWriter writer, bool setTokens, bool pretty)
      : base() {
      Contract.Requires(writer != null);
      Contract.Requires(filename != null);
      this.pretty = pretty;
      this.filename = filename;
      this.writer = writer;
      this.setTokens = setTokens;
    }

    public TokenTextWriter(string filename, TextWriter writer, bool pretty)
      : base() {
      Contract.Requires(writer != null);
      Contract.Requires(filename != null);
      this.pretty = pretty;
      this.filename = filename;
      this.writer = writer;
    }

    public TokenTextWriter(TextWriter writer)
        : this(writer, false)
    {
    }

    public TokenTextWriter(TextWriter writer, bool pretty)
      : base() {
      Contract.Requires(writer != null);
      this.pretty = pretty;
      this.filename = "<no file>";
      this.writer = writer;
    }

    public void Write(string text) {
      Contract.Requires(text != null);
      this.writer.Write(text);
      this.col += text.Length;
    }

    public void WriteIndent(int level) {
      if (!UseForComputingChecksums)
      {
        this.Write(Indent(level));
      }
    }

    public void Write(string text, params object[] args) {
      Contract.Requires(text != null);
      this.Write(string.Format(text, args));
    }

    public void Write(int level, string text) {
      Contract.Requires(text != null);
      this.WriteIndent(level);
      this.Write(text);
    }

    public void Write(int level, string text, params object[] args) {
      Contract.Requires(text != null);
      this.WriteIndent(level);
      this.Write(text, args);
    }

    public void Write(Absy node, string text) {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.Write(text);
    }

    public void Write(Absy node, string text, params string[] args) {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.Write(text, args);
    }

    public void Write(Absy node, int level, string text) {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.WriteIndent(level);
      this.SetToken(node);
      this.Write(text);
    }

    public void Write(Absy node, int level, string text, params object[] args) {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.WriteIndent(level);
      this.SetToken(node);
      this.Write(text, args);
    }

    public void WriteLine() {
      this.writer.WriteLine();
      this.line++;
      this.col = 0;
    }

    public void WriteLine(string text) {
      Contract.Requires(text != null);
      this.writer.WriteLine(text);
      this.line++;
      this.col = 0;
    }

    public void WriteText(string text) {
      Contract.Requires(text != null);
      int processed = 0;
      while (true) {
        int n = text.IndexOf('\n', processed);
        if (n == -1) {
          this.writer.Write(text);
          this.col += text.Length - processed;
          return;
        }
        processed = n + 1;
        this.line++;
        this.col = 0;
      }
    }

    public void WriteLine(string text, params object[] args) {
      Contract.Requires(text != null);
      this.WriteLine(string.Format(text, args));
    }

    public void WriteLine(int level, string text) {
      Contract.Requires(text != null);
      this.WriteIndent(level);
      this.WriteLine(text);
    }

    public void WriteLine(int level, string text, params object[] args) {
      Contract.Requires(text != null);
      this.WriteIndent(level);
      this.WriteLine(text, args);
    }

    public void WriteLine(Absy node, string text) {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.WriteLine(text);
    }

    public void WriteLine(Absy node, int level, string text) {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.WriteLine(level, text);
    }

    public void WriteLine(Absy node, int level, string text, params object[] args) {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.WriteLine(level, text, args);
    }

    public void Close() {
      this.writer.Close();
    }

    public void Dispose() {
      this.Close();
    }
  }

  public class Helpers {
    public static string BeautifyBplString(string s) {
      Contract.Requires(s != null);
      Contract.Ensures(Contract.Result<string>() != null);
      // strip "^" if it is the first character, change "$result" to "result"
      if (s.StartsWith("^") || s == "$result") {
        s = s.Substring(1);
      } else if (s.StartsWith("call")) {
        s = s.Substring(s.IndexOf('@') + 1);
        if (s.StartsWith("formal@")) {
          s = "(value of formal parameter: " + s.Substring(7) + ")";
        }
      }
      // strip "$in" from the end of identifier names
      if (s.EndsWith("$in")) {
        return "(initial value of: " + s.Substring(0, s.Length - 3) + ")";
      } else {
        return s;
      }
    }
    public static string PrettyPrintBplExpr(Expr e) {
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<string>() != null);
      // anything that is unknown will just be printed via ToString
      // OldExpr and QuantifierExpr, BvExtractExpr, BvConcatExpr are ignored for now
      // LiteralExpr is printed as itself by ToString
      if (e is IdentifierExpr) {
        string s = e.ToString();
        return Helpers.BeautifyBplString(s);
      } else if (e is NAryExpr) {
        NAryExpr ne = (NAryExpr)e;
        IAppliable fun = ne.Fun;
        var eSeq = ne.Args;
        if (fun != null) {
          if ((fun.FunctionName == "$Length" || fun.FunctionName == "$StringLength") && eSeq.Count == 1) {
            Expr e0 = eSeq[0];
            if (e0 != null) {
              string s0 = PrettyPrintBplExpr(e0);
              return s0 + ".Length";
            }
            //unexpected, just fall outside to the default
          } else if (fun.FunctionName == "$typeof" && eSeq.Count == 1) {
            Expr e0 = eSeq[0];
            if (e0 != null) {
              string s0 = PrettyPrintBplExpr(e0);
              return "(the dynamic type of: " + s0 + ")";
            }
            //unexpected, just fall outside to the default
          } else if (fun.FunctionName == "IntArrayGet" && eSeq.Count == 2) {
            Expr e0 = eSeq[0];
            Expr e1 = eSeq[1];
            if (e0 != null && e1 != null) {
              string s0 = PrettyPrintBplExpr(e0);
              string s1 = PrettyPrintBplExpr(e1);
              return s0 + "[" + s1 + "]";
            }
            //unexpected, just fall outside to the default
          } else if (fun.FunctionName == "$Is" && eSeq.Count == 2) {
            Expr e0 = eSeq[0];
            Expr e1 = eSeq[1];
            if (e0 != null && e1 != null) {
              string s0 = PrettyPrintBplExpr(e0);
              string s1 = PrettyPrintBplExpr(e1);
              return "(" + s0 + " == null || (" + s0 + " is " + s1 + "))";
            }
            //unexpected, just fall outside to the default
          } else if (fun.FunctionName == "$IsNotNull" && eSeq.Count == 2) {
            Expr e0 = eSeq[0];
            Expr e1 = eSeq[1];
            if (e0 != null && e1 != null) {
              string s0 = PrettyPrintBplExpr(e0);
              string s1 = PrettyPrintBplExpr(e1);
              return "(" + s0 + " is " + s1 + ")";
            }
            //unexpected, just fall outside to the default
          } else if (fun is MapSelect && eSeq.Count <= 3) {
            // only maps with up to two arguments are supported right now (here)
            if (cce.NonNull(eSeq[0]).ToString() == "$Heap") {
              //print Index0.Index1, unless Index1 is "$elements", then just print Index0
              string s0 = PrettyPrintBplExpr(cce.NonNull(eSeq[1]));
              if (eSeq.Count > 2) {
                string s1 = PrettyPrintBplExpr(cce.NonNull(eSeq[2]));
                if (s1 == "$elements") {
                  return s0;
                } else {
                  if (eSeq[2] is IdentifierExpr) {
                    // strip the class name out of a fieldname
                    s1 = s1.Substring(s1.LastIndexOf('.') + 1);
                  }
                  return s0 + "." + s1;
                }
              }
            }
            //unexpected, just fall outside to the default
          } else if (fun is Microsoft.Boogie.BinaryOperator && eSeq.Count == 2) {
            Microsoft.Boogie.BinaryOperator f = (Microsoft.Boogie.BinaryOperator)fun;
            Expr e0 = eSeq[0];
            Expr e1 = eSeq[1];
            if (e0 != null && e1 != null) {
              string s0 = PrettyPrintBplExpr(e0);
              string s1 = PrettyPrintBplExpr(e1);
              string op = "";
              switch (f.Op) {
                case Microsoft.Boogie.BinaryOperator.Opcode.Add:
                  op = " + ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.And:
                  op = " && ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Div:
                  op = " div ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Eq:
                  op = " == ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Ge:
                  op = " >= ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Gt:
                  op = " > ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Iff:
                  op = " <==> ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Imp:
                  op = " ==> ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Le:
                  op = " <= ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Lt:
                  op = " < ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Mod:
                  op = " mod ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Mul:
                  op = " * ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Neq:
                  op = " != ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Or:
                  op = " || ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Pow:
                  op = " ** ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.RealDiv:
                  op = " / ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Sub:
                  op = " - ";
                  break;
                case Microsoft.Boogie.BinaryOperator.Opcode.Subtype:
                  op = " <: ";
                  break;
                default:
                  op = " ";
                  break;
              }
              return "(" + s0 + op + s1 + ")";
            }
            //unexpected, just fall outside to the default
          } else {
            string s = fun.FunctionName + "(";
            for (int i = 0; i < eSeq.Count; i++) {
              Expr ex = eSeq[i];
              Contract.Assume(ex != null);
              if (i > 0) {
                s += ", ";
              }
              string t = PrettyPrintBplExpr(ex);
              if (t.StartsWith("(") && t.EndsWith(")")) {
                t = t.Substring(1, t.Length - 2);
              }
              s += t;
            }
            s += ")";
            return s;
            //unexpected, just fall outside to the default
          }
        }
      }

      return e.ToString();
    }

    private static readonly DateTime StartUp = DateTime.UtcNow;

    public static void ExtraTraceInformation(string point) {
      Contract.Requires(point != null);
      if (CommandLineOptions.Clo.TraceTimes) {
        DateTime now = DateTime.UtcNow;
        TimeSpan timeSinceStartUp = now - StartUp;
        Console.WriteLine(">>> {0}   [{1} s]", point, timeSinceStartUp.TotalSeconds);
      }
    }

    // Substitute @PROC@ in a filename with the given descName
    public static string SubstituteAtPROC(string descName, string fileName) {
      Contract.Requires(fileName != null);
      Contract.Requires(descName != null);
      Contract.Ensures(Contract.Result<string>() != null);
      System.Text.StringBuilder/*!*/ sb =
        new System.Text.StringBuilder(descName.Length);
      // quote the name, characters like ^ cause trouble in CMD
      // while $ could cause trouble in SH
      foreach (char c in descName) {
        if (Char.IsLetterOrDigit(c) || c == '.') {
          sb.Append(c);
        } else {
          sb.Append('_');
        }
      }
      string pn = sb.ToString();
      // We attempt to avoid filenames that are too long, but we only
      // do it by truncating the @PROC@ replacement, which leaves unchanged
      // any filename extension specified by the user.  We base our
      // calculations on that there is at most one occurrence of @PROC@.
      if (180 <= fileName.Length - 6 + pn.Length) {
        pn = pn.Substring(0, Math.Max(180 - (fileName.Length - 6), 0)) + "-n" + System.Threading.Interlocked.Increment(ref sequenceId);
      }

      return fileName.Replace("@PROC@", pn);
    }

    private static int sequenceId = -1;

  }
}
