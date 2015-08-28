using System;
using SA=System.Attribute;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Text;
//using Microsoft.Boogie;

/// <summary>
/// A class containing static methods to extend the functionality of Code Contracts
/// </summary>

public static class cce {
  //[Pure]
  //public static bool NonNullElements<T>(Microsoft.Dafny.Graph<T> collection) {
  //  return collection != null && cce.NonNullElements(collection.TopologicallySortedComponents());
  //}
  [Pure]
  public static T NonNull<T>(T t) {
    Contract.Assert(t != null);
    return t;
  }
  [Pure]
  public static bool NonNullElements<T>(IEnumerable<T> collection) {
    return collection != null && Contract.ForAll(collection, c => c != null);
  }
  [Pure]
  public static bool NonNullElements<TKey, TValue>(IDictionary<TKey, TValue> collection) {
    return collection != null && Contract.ForAll(collection, pair => NonNullElements(pair));
  }
  //[Pure]
  //public static bool NonNullElements(VariableSeq collection) {
  //  return collection != null && Contract.ForAll(0, collection.Length, i => collection[i] != null);
  //}
  /// <summary>
  /// For possibly-null lists of non-null elements
  /// </summary>
  /// <typeparam name="T"></typeparam>
  /// <param name="collection"></param>
  /// <param name="nullability">If true, the collection is treated as an IEnumerable&lt;T!&gt;?, rather than an IEnumerable&lt;T!&gt;!</param>
  /// <returns></returns>
  [Pure]
  public static bool NonNullElements<T>(IEnumerable<T> collection, bool nullability) {
    return (nullability && collection == null) || cce.NonNullElements(collection);
    //Should be the same as:
    /*if(nullability&&collection==null)
     * return true;
     * return cce.NonNullElements(collection)
     */

  }
  [Pure]
  public static bool NonNullElements<TKey, TValue>(KeyValuePair<TKey, TValue> kvp) {
    return kvp.Key != null && kvp.Value != null;
  }
  [Pure]
  public static bool NonNullElements<T>(IEnumerator<T> iEnumerator) {
    return iEnumerator != null;
  }
  //[Pure]
  //public static bool NonNullElements<T>(Graphing.Graph<T> graph) {
  //  return cce.NonNullElements(graph.TopologicalSort());
  //}
  [Pure]
  public static void BeginExpose(object o) {
  }
  [Pure]
  public static void EndExpose() {
  }
  [Pure]
  public static bool IsPeerConsistent(object o) {
    return true;
  }
  [Pure]
  public static bool IsConsistent(object o) {
    return true;
  }
  [Pure]
  public static bool IsExposable(object o) {
    return true;
  }
  [Pure]
  public static bool IsExposed(object o) {
    return true;
  }
  [Pure]
  public static bool IsNew(object o) {
    return true;
  }
  public static class Owner {
    [Pure]
    public static bool Same(object o, object p) {
      return true;
    }
    [Pure]
    public static void AssignSame(object o, object p) {
    }
    [Pure]
    public static object ElementProxy(object o) {
      return o;
    }
    [Pure]
    public static bool None(object o) {
      return true;
    }
    [Pure]
    public static bool Different(object o, object p) {
      return true;
    }
    [Pure]
    public static bool New(object o) {
      return true;
    }
  }
  [Pure]
  public static void LoopInvariant(bool p) {
    Contract.Assert(p);
  }
  public class UnreachableException : Exception {
    public UnreachableException() {
    }
  }
  //[Pure]
  //public static bool IsValid(Microsoft.Dafny.Expression expression) {
  //  return true;
  //}
  //public static List<T> toList<T>(PureCollections.Sequence s) {
  //  List<T> toRet = new List<T>();
  //  foreach (T t in s.elems)
  //    if(t!=null)
  //    toRet.Add(t);
  //  return toRet;
  //}

  //internal static bool NonNullElements(Set set) {
  //  return set != null && Contract.ForAll(0,set.Count, i => set[i] != null);
  //}
}

public class PeerAttribute : SA {
}
public class RepAttribute : SA {
}
public class CapturedAttribute : SA {
}
public class NotDelayedAttribute : SA {
}
public class NoDefaultContractAttribute : SA {
}
public class VerifyAttribute : SA {
  public VerifyAttribute(bool b) {

  }
}
public class StrictReadonlyAttribute : SA {
}
public class AdditiveAttribute : SA {
}
public class ReadsAttribute : SA {
  public enum Reads {
    Nothing,
    Everything,
  };
  public ReadsAttribute(object o) {
  }
}
public class GlobalAccessAttribute : SA {
  public GlobalAccessAttribute(bool b) {
  }
}
public class EscapesAttribute : SA {
  public EscapesAttribute(bool b, bool b_2) {
  }
}
public class NeedsContractsAttribute : SA {
  public NeedsContractsAttribute() {
  }
  public NeedsContractsAttribute(bool ret, bool parameters) {
  }
  public NeedsContractsAttribute(bool ret, int[] parameters) {
  }
}
public class ImmutableAttribute : SA {
}
public class InsideAttribute : SA {
}
public class SpecPublicAttribute : SA {
}
public class ElementsPeerAttribute : SA {
}
public class ResultNotNewlyAllocatedAttribute : SA {
}
public class OnceAttribute : SA {
}