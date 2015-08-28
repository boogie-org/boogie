
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Text;
using Microsoft.Boogie;

  /// <summary>
    /// A class containing static methods to extend the functionality of Code Contracts
    /// </summary>

public static class cce {
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
  public static bool NonNullElements(VariableSeq collection) {
    return collection != null && Contract.ForAll(0, collection.Length, i => collection[i] != null);
  }

  public class UnreachableException : Exception {
    public UnreachableException() {
    }
  }

  [Pure]
  public static void BeginExpose(object o) {
  }
  [Pure]
  public static void EndExpose() {
  }

  public static bool IsPeerConsistent(this object o) {
    return true;
  }

  public static bool IsConsistent(this object o) {
    return true;
  }

  public static bool IsExposable(this object o) {
    return true;
  }
  public static class Owner {
    [Pure]
    public static bool Same(object o, object p) {
      return true;
    }
  }
}
public class PeerAttribute : System.Attribute {
}
public class RepAttribute : System.Attribute {
}
public class CapturedAttribute : System.Attribute {
}
