//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Diagnostics.Contracts;
namespace Microsoft.AbstractInterpretationFramework.Collections {
  using System.Collections;
  using System.Diagnostics.Contracts;

  /// <summary>
  ///  Extend sets for using as a IWorkList.
  /// </summary>
  public class WorkSet : Microsoft.Boogie.GSet<object>, Microsoft.Boogie.IWorkList {

    // See Bug #148 for an explanation of why this is here.
    // Without it, the contract inheritance rules will complain since it
    // has nowhere to attach the out-of-band contract it gets from
    // ICollection.Count that it gets from IWorkList.
    public override int Count {
      get {
        return base.Count;
      }
    }

    [Pure]
    public bool IsEmpty() {
      return Count == 0;
    }

    /// <summary>
    ///  Pull an element out of the workset.
    /// </summary>
    public object Pull() {
      IEnumerator iter = GetEnumerator();
      iter.MoveNext();

      object result = cce.NonNull(iter.Current);
      Remove(result);

      return result;
    }

    bool Microsoft.Boogie.IWorkList.Add(object o) {
      if (o == null)
        throw new System.ArgumentNullException();
      this.Add(o);
      return true;
    }
    bool Microsoft.Boogie.IWorkList.AddAll(IEnumerable objs) {
      if (objs == null)
        throw new System.ArgumentNullException();
      return this.AddAll(objs);
    }

    // ICollection members
    public void CopyTo(System.Array/*!*/ a, int i) {
      //Contract.Requires(a != null); 
      if (this.Count > a.Length - i)
        throw new System.ArgumentException();
      int j = i;
      foreach (object o in this) {
        a.SetValue(o, j++);
      }
      return;
    }
    object/*!*/ ICollection.SyncRoot {
      [Pure]
      get {
        Contract.Ensures(Contract.Result<object>() != null);
        return this;
      }
    }
    public bool IsSynchronized {
      get {
        return false;
      }
    }

  }
}

namespace Microsoft.AbstractInterpretationFramework.Collections.Generic {
  using System.Collections.Generic;

  public class HashMultiset<T> {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(dict != null);
    }

    private readonly IDictionary<T, int>/*!*/ dict;

    //Contract.Invariant(Contract.ForAll(dict , entry => entry.Value >= 1));

    public HashMultiset() {
      this.dict = new Dictionary<T, int>();
      // base();
    }

    public HashMultiset(int size) {
      this.dict = new Dictionary<T, int>(size);
      // base();
    }

    public void Add(T t) {
      cce.BeginExpose(this);
      {
        if (dict.ContainsKey(t)) {
          dict[t] = dict[t] + 1;
        } else {
          dict.Add(t, 1);
        }
      }
      cce.EndExpose();
    }

    public void Remove(T t) {
      if (dict.ContainsKey(t)) {
        cce.BeginExpose(this);
        {
          int count = dict[t];
          if (count == 1) {
            dict.Remove(t);
          } else {
            dict[t] = count - 1;
          }
        }
        cce.EndExpose();
      }
    }

    public bool Contains(T t) {
      return dict.ContainsKey(t);
    }
  }
}
