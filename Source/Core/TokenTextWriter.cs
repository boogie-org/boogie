using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Boogie
{
  public class TokenTextWriter : IDisposable
  {
    string /*!*/
      filename;

    TextWriter /*!*/
      writer;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(filename != null);
      Contract.Invariant(writer != null);
    }

    bool setTokens = true;
    int line = 1;
    int col;
    public bool UseForComputingChecksums;

    private const int indent_size = 2;
    private int most_recent_indent_level = 0;

    protected string Indent(int level)
    {
      Contract.Ensures(Contract.Result<string>() != null);
      most_recent_indent_level = level;
      return new string(' ', (indent_size * level));
    }


    // Keywords, this array *must* be sorted
    public static readonly string[] /*!*/
      BplKeywords =
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

    public bool push(string type = null)
    {
      if (pretty)
      {
        if (wstk == null)
        {
          wstk = new Stack<KeyValuePair<string, List<TextWriter>>>();
          actual_writer = writer;
        }

        if (wstk.Count > 0 && wstk.Peek().Key == type && type != null)
        {
          sep();
          return false; // don't actually pop this thing (send this bool to pop)
        }
        else
        {
          wstk.Push(new KeyValuePair<string, List<TextWriter>>(type, new List<TextWriter> { }));
          sep();
          return true; // this needs to be popped
        }
      }
      else
      {
        return false;
      }
    }

    public void pop(bool do_it = true)
    {
      if (pretty)
      {
        if (do_it)
        {
          List<TextWriter> ws = wstk.Pop().Value;
          // try to figure out if you should insert line breaks between
          // them or print them on one single line
          // this breaks down when there are newlines inserted
          List<String> ss = new List<String>();
          int len = 0;
          foreach (TextWriter w in ws)
          {
            foreach (String s in w.ToString().Split(new String[] {"\r\n", "\n"}, StringSplitOptions.None))
            {
              if (s.Length > 0)
              {
                ss.Add(s);
                len += s.Length;
                // len = Math.Max(len, s.Length);
              }
            }
          }

          // figure out which is the next writer to use
          List<TextWriter> tw = wstk.Count > 0 ? wstk.Peek().Value : null;
          string indent_string;
          if (tw == null)
          {
            writer = actual_writer;
            indent_string = new string(' ', indent_size * most_recent_indent_level + indent_size);
          }
          else
          {
            writer = tw.Last();
            indent_string = new string(' ', indent_size);
          }

          // write the strings (we would like to know WHERE we are in the document here)
          if (len > 80 /* - wstk.Count * 2 */)
          {
            for (int i = 0; i < ss.Count; i++)
            {
              if (i != ss.Count - 1)
              {
                writer.WriteLine(ss[i]);
                writer.Write(indent_string);
              }
              else
              {
                writer.Write(ss[i]);
              }
            }
          }
          else
          {
            foreach (String s in ss)
            {
              writer.Write(s);
            }
          }
        }
      }
    }

    public void sep()
    {
      if (pretty)
      {
        List<TextWriter> ws = wstk.Peek().Value;

        writer = new StringWriter();
        wstk.Peek().Value.Add(writer);
      }
    }

    private IToken /*!*/ CurrentToken
    {
      get
      {
        Contract.Ensures(Contract.Result<IToken>() != null);

        Token token = new Token();
        token.filename = filename;
        token.line = line;
        token.col = col;
        return token;
      }
    }

    public void SetToken(Absy absy)
    {
      Contract.Requires(absy != null);
      this.SetToken(t => absy.tok = t);
    }

    public void SetToken(IfThenElse expr)
    {
      Contract.Requires(expr != null);
      this.SetToken(t => expr.tok = t);
    }

    public void SetToken(Action<IToken> setter)
    {
      Contract.Requires(setter != null);
      if (this.setTokens)
      {
        setter(this.CurrentToken);
      }
    }

    public void SetToken(ref IToken tok)
    {
      Contract.Requires(tok != null);
      if (this.setTokens)
      {
        tok = this.CurrentToken;
      }
    }

    public static string SanitizeIdentifier(string name)
    {
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<string>() != null);
      int index = Array.BinarySearch(TokenTextWriter.BplKeywords, name);
      if (index >= 0)
      {
        return "\\" + name;
      }
      else if (name.Length > 2 && name[0] == 'b' && name[1] == 'v')
      {
        return int.TryParse(name.Substring(2), out var dummy) ? "\\" + name : name;
      }
      else if (name.Contains('@'))
      {
        return SanitizeIdentifier(name.Replace("@", "#AT#"));
      }
      else
      {
        return name;
      }
    }

    public TokenTextWriter(string filename)
      : this(filename, false)
    {
    }

    public TokenTextWriter(string filename, bool pretty)
      : base()
    {
      Contract.Requires(filename != null);
      this.pretty = pretty;
      this.filename = filename;
      this.writer = new StreamWriter(filename);
    }

    public TokenTextWriter(string filename, bool setTokens, bool pretty)
      : base()
    {
      Contract.Requires(filename != null);
      this.pretty = pretty;
      this.filename = filename;
      this.writer = new StreamWriter(filename);
      this.setTokens = setTokens;
    }

    public TokenTextWriter(string filename, TextWriter writer, bool setTokens, bool pretty)
      : base()
    {
      Contract.Requires(writer != null);
      Contract.Requires(filename != null);
      this.pretty = pretty;
      this.filename = filename;
      this.writer = writer;
      this.setTokens = setTokens;
    }

    public TokenTextWriter(string filename, TextWriter writer, bool pretty)
      : base()
    {
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
      : base()
    {
      Contract.Requires(writer != null);
      this.pretty = pretty;
      this.filename = "<no file>";
      this.writer = writer;
    }

    public void Write(string text)
    {
      Contract.Requires(text != null);
      this.writer.Write(text);
      this.col += text.Length;
    }

    public void WriteIndent(int level)
    {
      if (!UseForComputingChecksums)
      {
        this.Write(Indent(level));
      }
    }

    public void Write(string text, params object[] args)
    {
      Contract.Requires(text != null);
      this.Write(string.Format(text, args));
    }

    public void Write(int level, string text)
    {
      Contract.Requires(text != null);
      this.WriteIndent(level);
      this.Write(text);
    }

    public void Write(int level, string text, params object[] args)
    {
      Contract.Requires(text != null);
      this.WriteIndent(level);
      this.Write(text, args);
    }

    public void Write(Absy node, string text)
    {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.Write(text);
    }

    public void Write(Absy node, string text, params string[] args)
    {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.Write(text, args);
    }

    public void Write(Absy node, int level, string text)
    {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.WriteIndent(level);
      this.SetToken(node);
      this.Write(text);
    }

    public void Write(Absy node, int level, string text, params object[] args)
    {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.WriteIndent(level);
      this.SetToken(node);
      this.Write(text, args);
    }

    public void WriteLine()
    {
      this.writer.WriteLine();
      this.line++;
      this.col = 0;
    }

    public void WriteLine(string text)
    {
      Contract.Requires(text != null);
      this.writer.WriteLine(text);
      this.line++;
      this.col = 0;
    }

    public void WriteText(string text)
    {
      Contract.Requires(text != null);
      int processed = 0;
      while (true)
      {
        int n = text.IndexOf('\n', processed);
        if (n == -1)
        {
          this.writer.Write(text);
          this.col += text.Length - processed;
          return;
        }

        processed = n + 1;
        this.line++;
        this.col = 0;
      }
    }

    public void WriteLine(string text, params object[] args)
    {
      Contract.Requires(text != null);
      this.WriteLine(string.Format(text, args));
    }

    public void WriteLine(int level, string text)
    {
      Contract.Requires(text != null);
      this.WriteIndent(level);
      this.WriteLine(text);
    }

    public void WriteLine(int level, string text, params object[] args)
    {
      Contract.Requires(text != null);
      this.WriteIndent(level);
      this.WriteLine(text, args);
    }

    public void WriteLine(Absy node, string text)
    {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.WriteLine(text);
    }

    public void WriteLine(Absy node, int level, string text)
    {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.WriteLine(level, text);
    }

    public void WriteLine(Absy node, int level, string text, params object[] args)
    {
      Contract.Requires(text != null);
      Contract.Requires(node != null);
      this.SetToken(node);
      this.WriteLine(level, text, args);
    }

    public void Close()
    {
      this.writer.Close();
    }

    public void Dispose()
    {
      this.Close();
    }
  }
}