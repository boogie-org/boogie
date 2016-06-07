//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Linq;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Text;
using System.Diagnostics.Contracts;
using System.Globalization;

namespace Microsoft.Boogie
{
  public class SExpr
  {
    static readonly SExpr[] EmptyArgs = new SExpr[0];
    public readonly string Name;
    public SExpr[] Arguments
    {
      get
      {
        Contract.Ensures(Contract.Result<SExpr[]>() != null);
        Contract.Ensures(Contract.ForAll(Contract.Result<SExpr[]>(), expr => expr != null));

        return this.arguments;
      }
    }

    public SExpr this[int idx]
    {
      get
      {
        return Arguments[idx];
      }
    }

    public int ArgCount
    {
      get { return arguments.Length; }
    }

    public bool IsId
    {
      get { return Arguments.Length == 0; }
    }

    private readonly SExpr[] arguments;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this.Name != null);
      Contract.Invariant(this.arguments != null);
      Contract.Invariant(Contract.ForAll(this.arguments, arg => arg != null));
    }

    public SExpr(string name, params SExpr[] args)
      : this(name, (IEnumerable<SExpr>)args)
    {
      Contract.Requires(name != null);
      Contract.Requires(args != null);
      Contract.Requires(Contract.ForAll(args, x => x != null));
    }

    public SExpr(string name, IEnumerable<SExpr> args)
    {
      Contract.Requires(name != null);
      Contract.Requires(args != null);
      // We don't want to evaluate args twice!
      // Contract.Requires(Contract.ForAll(args, x => x != null));
      Name = name;
      arguments = args.ToArray();
    }

    public SExpr(string name)
      : this(name, EmptyArgs)
    {
      Contract.Requires(name != null);
    }

    #region pretty-printing
    void WriteTo(StringBuilder sb)
    {
      Contract.Requires(sb != null);

      if (Arguments.Length > 0) sb.Append('(');
      if (Name.Any(Char.IsWhiteSpace))
        sb.Append("\"").Append(Name).Append("\"");
      else if (Name.Length == 0)
        sb.Append("()");
      else
        sb.Append(Name);
      foreach (var a in Arguments) {
        sb.Append(' ');
        a.WriteTo(sb);
      }
      if (Arguments.Length > 0) sb.Append(')');
    }

    public override string ToString()
    {
      var sb = new StringBuilder();
      this.WriteTo(sb);
      return sb.ToString();
    }
    #endregion

    #region parsing

    public abstract class Parser
    {
        System.IO.StreamReader sr;
        int linePos = 0;
        string currLine = null;

        public Parser(System.IO.StreamReader _sr)
        {
            sr = _sr;
        }
        string Read()
        {
            return sr.ReadLine();
        }
        char SkipWs()
        {
            while (true)
            {
                if (currLine == null)
                {
                    currLine = Read();
                    if (currLine == null)
                        return '\0';
                }

                while (linePos < currLine.Length && char.IsWhiteSpace(currLine[linePos]))
                    linePos++;

                if (linePos < currLine.Length)
                    return currLine[linePos];
                else
                {
                    currLine = null;
                    linePos = 0;
                }
            }
        }

        void Shift()
        {
            linePos++;
        }

        string ParseId()
        {
            var sb = new StringBuilder();

            var beg = SkipWs();

            var quoted = beg == '"' || beg == '|';
            if (quoted)
                Shift();
            while (true)
            {
                if (linePos >= currLine.Length)
                {
                    if (quoted)
                    {
                        sb.Append("\n");
                        currLine = Read();
                        linePos = 0;
                        if (currLine == null)
                            break;
                    }
                    else break;
                }

                var c = currLine[linePos++];
                if (quoted && c == beg)
                    break;
                if (!quoted && (char.IsWhiteSpace(c) || c == '(' || c == ')'))
                {
                    linePos--;
                    break;
                }
                if (quoted && c == '\\' && linePos < currLine.Length && currLine[linePos] == '"')
                {
                    sb.Append('"');
                    linePos++;
                    continue;
                }
                sb.Append(c);
            }

            return sb.ToString();
        }

        public abstract void ParseError(string msg);

        public IEnumerable<SExpr> ParseSExprs(bool top)
        {
            while (true)
            {
                var c = SkipWs();
                if (c == '\0')
                    break;

                if (c == ')')
                {
                    if (top)
                        ParseError("stray ')'");
                    break;
                }

                string id;

                if (c == '(')
                {
                    Shift();
                    c = SkipWs();
                    if (c == '\0')
                    {
                        ParseError("expecting something after '('");
                        break;
                    }
                    else if (c == '(')
                    {
                        id = "";
                    }
                    else
                    {
                        id = ParseId();
                    }

                    var args = ParseSExprs(false).ToArray();

                    c = SkipWs();
                    if (c == ')')
                    {
                        Shift();
                    }
                    else
                    {
                        ParseError("unclosed '(" + id + "'");
                    }
                    yield return new SExpr(id, args);
                }
                else
                {
                    id = ParseId();
                    yield return new SExpr(id);
                }

                if (top) break;
            }
        }
    }
    #endregion
  }
}

