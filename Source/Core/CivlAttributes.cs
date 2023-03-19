using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public static class CivlAttributes
  {
    public const string LAYER = "layer";

    public const string YIELDS = "yields";

    public const string REFINES = "refines";
    public const string HIDE = "hide";

    public const string LINEAR = "linear";
    public const string LINEAR_IN = "linear_in";
    public const string LINEAR_OUT = "linear_out";

    public const string LEMMA = "lemma";

    public const string PENDING_ASYNC = "pending_async";
    public const string SYNC = "sync";
    
    public const string ELIM = "elim";

    private static string[] CIVL_ATTRIBUTES =
    {
      LAYER,
      YIELDS,
      REFINES, HIDE,
      LEMMA,
      PENDING_ASYNC, SYNC,
      ELIM
    };

    private static string[] LINEAR_ATTRIBUTES =
      {LINEAR, LINEAR_IN, LINEAR_OUT};

    public static bool HasCivlAttribute(this ICarriesAttributes obj)
    {
      for (var kv = obj.Attributes; kv != null; kv = kv.Next)
      {
        if (CIVL_ATTRIBUTES.Contains(kv.Key) || LINEAR_ATTRIBUTES.Contains(kv.Key))
        {
          return true;
        }
      }

      return false;
    }

    public static List<QKeyValue> FindAllAttributes(this ICarriesAttributes obj, string name)
    {
      var attributes = new List<QKeyValue>();
      for (var kv = obj.Attributes; kv != null; kv = kv.Next)
      {
        if (kv.Key == name)
        {
          attributes.Add(kv);
        }
      }

      return attributes;
    }

    public static bool HasAttribute(this ICarriesAttributes obj, string name)
    {
      return QKeyValue.FindBoolAttribute(obj.Attributes, name);
    }

    public static bool RemoveAttributes(ICarriesAttributes obj, Func<QKeyValue, bool> cond)
    {
      QKeyValue curr = obj.Attributes;
      bool removed = false;

      while (curr != null && cond(curr))
      {
        curr = curr.Next;
        removed = true;
      }

      obj.Attributes = curr;
      while (curr != null)
      {
        QKeyValue next = curr.Next;
        while (next != null && cond(next))
        {
          next = next.Next;
          removed = true;
        }

        curr.Next = next;
        curr = next;
      }

      return removed;
    }

    public static void RemoveAttributes(ICarriesAttributes obj, ICollection<string> keys)
    {
      RemoveAttributes(obj, kv => keys.Contains(kv.Key));
    }

    public static void RemoveCivlAttributes(ICarriesAttributes obj)
    {
      RemoveAttributes(obj, CIVL_ATTRIBUTES);
    }

    public static void RemoveLinearAttributes(ICarriesAttributes obj)
    {
      RemoveAttributes(obj, LINEAR_ATTRIBUTES);
    }
  }
}