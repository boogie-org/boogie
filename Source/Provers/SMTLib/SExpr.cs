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

  }
}

