using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class QKeyValue : Absy
{
  public readonly string /*!*/
    Key;

  private readonly List<object /*!*/> /*!*/
    _params; // each element is either a string or an Expr

  public void AddParam(object p)
  {
    Contract.Requires(p != null);
    this._params.Add(p);
  }

  public void AddParams(IEnumerable<object> ps)
  {
    Contract.Requires(cce.NonNullElements(ps));
    this._params.AddRange(ps);
  }

  public void ClearParams()
  {
    this._params.Clear();
  }

  public IList<object> Params
  {
    get
    {
      Contract.Ensures(cce.NonNullElements(Contract.Result<IList<object>>()));
      Contract.Ensures(Contract.Result<IList<object>>().IsReadOnly);
      return this._params.AsReadOnly();
    }
  }

  public QKeyValue Next;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Key != null);
    Contract.Invariant(cce.NonNullElements(this._params));
  }

  public QKeyValue(IToken tok, string key, IList<object /*!*/> /*!*/ parameters = null, QKeyValue next = null)
    : base(tok)
  {
    Contract.Requires(key != null);
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(parameters));
    Key = key;
    this._params = parameters == null ? new List<object>() : new List<object>(parameters);
    Next = next;
  }

  public void Emit(TokenTextWriter stream)
  {
    Contract.Requires(stream != null);
    stream.Write("{:");
    stream.Write(Key);
    string sep = " ";
    foreach (object p in Params)
    {
      stream.Write(sep);
      sep = ", ";
      if (p is string)
      {
        stream.Write("\"");
        stream.Write((string) p);
        stream.Write("\"");
      }
      else
      {
        ((Expr) p).Emit(stream);
      }
    }

    stream.Write("}");
  }

  public override void Resolve(ResolutionContext rc)
  {
    //Contract.Requires(rc != null);

    if ((Key == "minimize" || Key == "maximize") && Params.Count != 1)
    {
      rc.Error(this, "attributes :minimize and :maximize accept only one argument");
    }

    if (Key == "verified_under" && Params.Count != 1)
    {
      rc.Error(this, "attribute :verified_under accepts only one argument");
    }

    if (Key == CivlAttributes.LAYER)
    {
      foreach (var o in Params)
      {
        if (o is LiteralExpr l && l.isBigNum)
        {
          var n = l.asBigNum;
          if (n.IsNegative)
          {
            rc.Error(this, "layer must be non-negative");
          }
          else if (!n.InInt32)
          {
            rc.Error(this, "layer is too large (max value is Int32.MaxValue)");
          }
        }
        else
        {
          rc.Error(this, "layer must be a non-negative integer");
        }
      }
    }

    foreach (object p in Params)
    {
      if (p is Expr)
      {
        var oldCtxtState = rc.StateMode;
        if (oldCtxtState == ResolutionContext.State.Single)
        {
          rc.StateMode = ResolutionContext.State.Two;
        }

        ((Expr) p).Resolve(rc);
        if (oldCtxtState != rc.StateMode)
        {
          rc.StateMode = oldCtxtState;
        }
      }
    }
  }

  public override void Typecheck(TypecheckingContext tc)
  {
    //Contract.Requires(tc != null);
    foreach (object p in Params)
    {
      var expr = p as Expr;
      if (expr != null)
      {
        expr.Typecheck(tc);
      }

      if ((Key == "minimize" || Key == "maximize")
          && (expr == null || !(expr.Type.IsInt || expr.Type.IsReal || expr.Type.IsBv)))
      {
        tc.Error(this, "attributes :minimize and :maximize accept only one argument of type int, real or bv");
        break;
      }

      if (Key == "verified_under" && (expr == null || !expr.Type.IsBool))
      {
        tc.Error(this, "attribute :verified_under accepts only one argument of type bool");
        break;
      }
    }
  }

  public void AddLast(QKeyValue other)
  {
    Contract.Requires(other != null);
    QKeyValue current = this;
    while (current.Next != null)
    {
      current = current.Next;
    }

    current.Next = other;
  }

  public static QKeyValue FindAttribute(QKeyValue kv, Func<QKeyValue, bool> property)
  {
    for (; kv != null; kv = kv.Next)
    {
      if (property(kv))
      {
        return kv;
      }
    }
    return null;
  }

  // Look for {:name string} in list of attributes.
  [Pure]
  public static string FindStringAttribute(QKeyValue kv, string name)
  {
    Contract.Requires(name != null);
    kv = FindAttribute(kv, qkv => qkv.Key == name && qkv.Params.Count == 1 && qkv.Params[0] is string);
    if (kv != null)
    {
      Contract.Assert(kv.Params.Count == 1 && kv.Params[0] is string);
      return (string) kv.Params[0];
    }
    return null;
  }

  // Look for {:name expr} in list of attributes.
  public static Expr FindExprAttribute(QKeyValue kv, string name)
  {
    Contract.Requires(name != null);
    kv = FindAttribute(kv, qkv => qkv.Key == name && qkv.Params.Count == 1 && qkv.Params[0] is Expr);
    if (kv != null)
    {
      Contract.Assert(kv.Params.Count == 1 && kv.Params[0] is Expr);
      return (Expr) kv.Params[0];
    }
    return null;
  }

  public static int FindIntAttribute(QKeyValue kv, string name, int defl)
  {
    Contract.Requires(name != null);
    Expr e = FindExprAttribute(kv, name);
    LiteralExpr l = e as LiteralExpr;
    if (l != null && l.isBigNum)
    {
      return l.asBigNum.ToIntSafe;
    }

    return defl;
  }

  public override Absy Clone()
  {
    List<object> newParams = new List<object>();
    foreach (object o in Params)
    {
      newParams.Add(o);
    }

    return new QKeyValue(tok, Key, newParams, (Next == null) ? null : (QKeyValue) Next.Clone());
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    return visitor.VisitQKeyValue(this);
  }

  public override bool Equals(object obj)
  {
    var other = obj as QKeyValue;
    if (other == null)
    {
      return false;
    }
    else
    {
      return Key == other.Key && object.Equals(Params, other.Params) &&
             (Next == null
               ? other.Next == null
               : object.Equals(Next, other.Next));
    }
  }

  public override int GetHashCode()
  {
    throw new NotImplementedException();
  }
}