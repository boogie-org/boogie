using System;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public static class CivlAttributes
  {
    public const string LAYER = "layer";

    public const string YIELDS = "yields";

    public const string YIELD_INVARIANT = "yield_invariant";
    public const string YIELD_REQUIRES = "yield_requires";
    public const string YIELD_ENSURES = "yield_ensures";
    public const string YIELD_PRESERVES = "yield_preserves";
    public const string YIELD_LOOP = "yield_loop";

    public const string INTRO = "intro";

    public const string ATOMIC = "atomic";
    public const string LEFT = "left";
    public const string RIGHT = "right";
    public const string BOTH = "both";

    public static string REFINES = "refines";
    public static string HIDE = "hide";

    public const string TERMINATES = "terminates";

    public const string LINEAR = "linear";
    public const string LINEAR_IN = "linear_in";
    public const string LINEAR_OUT = "linear_out";

    public const string BACKWARD = "backward";
    public const string COMMUTATIVITY = "commutativity";
    public const string LEMMA = "lemma";
    public const string WITNESS = "witness";

    public const string PENDING_ASYNC = "pending_async";
    public const string SYNC = "sync";

    public const string IS = "IS";
    public const string IS_INVARIANT = "IS_invariant";
    public const string IS_ABSTRACTION = "IS_abstraction";
    public const string ELIM = "elim";
    public const string CHOICE = "choice";

    private static string[] CIVL_ATTRIBUTES =
    {
      LAYER, YIELDS, YIELD_INVARIANT, INTRO, ATOMIC, LEFT, RIGHT, BOTH, REFINES, HIDE,
      COMMUTATIVITY, LEMMA, WITNESS,
      PENDING_ASYNC, IS, IS_INVARIANT, IS_ABSTRACTION, ELIM, CHOICE,
      YIELD_REQUIRES, YIELD_ENSURES, YIELD_PRESERVES, YIELD_LOOP,
      TERMINATES
    };

    private static string[] LINEAR_ATTRIBUTES =
      {LINEAR, LINEAR_IN, LINEAR_OUT};

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