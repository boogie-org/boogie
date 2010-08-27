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

  /// <summary>
  /// A class representing a mathematical set.
  /// </summary>
  public class Set : ICloneable, IEnumerable {
    /*[Own]*/
    Hashtable ht;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(ht != null);
    }


    public Set() {
      ht = new Hashtable();
      //:base();
    }

    private Set(Hashtable/*!*/ ht) {
      Contract.Requires(ht != null);
      this.ht = ht;
      //:base();
    }

    public Set(int capacity) {
      ht = new Hashtable(capacity);
      //:base();
    }


    public readonly static Set/*!*/ Empty = new Set();

    public void Clear() {
      ht.Clear();
    }

    /// <summary>
    /// This method idempotently adds "o" to the set.
    /// In notation:
    ///   this.SetElements =  this.SetElements_old \union {o};
    /// </summary>
    public void Add(object/*!*/ o) {
      Contract.Requires(o != null);
      ht[o] = o;
    }

    /// <summary>
    /// this.SetElements =  this.SetElements_old \union s.SetElements;
    /// </summary>
    public void AddRange(Set/*!*/ s) {
      Contract.Requires(s != null);
      foreach (object/*!*/ o in s) {
        Contract.Assert(o != null);
        Add(o);
      }
    }

    /// <summary>
    /// this.SetElements =  this.SetElements_old \setminus {o};
    /// </summary>
    public void Remove(object/*!*/ o) {
      Contract.Requires(o != null);
      ht.Remove(o);
    }

    /// <summary>
    /// this.SetElements =  this.SetElements_old \setminus s.SetElements;
    /// </summary>
    public void RemoveRange(Set/*!*/ s) {
      Contract.Requires(s != null);
      if (s == this) {
        ht.Clear();
      } else {
        foreach (object/*!*/ o in s) {
          Contract.Assert(o != null);
          ht.Remove(o);
        }
      }
    }

    /// <summary>
    /// Returns an arbitrary element from the set.
    /// </summary>
    public object/*!*/ Choose() {
      Contract.Requires((Count > 0));
      Contract.Ensures(Contract.Result<object>() != null);
      IEnumerator iter = GetEnumerator();
      iter.MoveNext();
      return cce.NonNull(iter.Current);
    }

    /// <summary>
    /// Picks an arbitrary element from the set, removes it, and returns it.
    /// </summary>
    public object/*!*/ Take() {
      Contract.Requires((Count > 0));
      Contract.Ensures(Contract.Result<object>() != null);
      Contract.Ensures(Count == Contract.OldValue(Count) - 1);
      object r = Choose();
      Remove(r);
      return r;
    }

    public void Intersect(Set/*!*/ s) {
      Contract.Requires(s != null);
      Hashtable h = new Hashtable(ht.Count);
      foreach (object/*!*/ key in ht.Keys) {
        Contract.Assert(key != null);
        if (s.ht.ContainsKey(key)) {
          h.Add(key, key);
        }
      }
      ht = h;
    }

    /// <summary>
    /// The getter returns true iff "o" is in the set.
    /// The setter adds the value "o" (for "true") or removes "o" (for "false")
    /// </summary>
    public bool this[object/*!*/ o] {
      get {
        Contract.Requires(o != null);
        return ht.ContainsKey(o);
      }
      set {
        if (value) {
          Add(o);
        } else {
          Remove(o);
        }
      }
    }

    /// <summary>
    /// Returns true iff "o" is an element of "this".
    /// </summary>
    /// <param name="o"></param>
    /// <returns></returns>
    [Pure]
    public bool Contains(object/*!*/ o) {
      Contract.Requires(o != null);
      if (!this.ht.ContainsKey(o)) {
        return false;
      }
      return true;
    }

    /// <summary>
    /// Returns true iff every element of "s" is an element of "this", that is, if
    /// "s" is a subset of "this".
    /// </summary>
    /// <param name="s"></param>
    /// <returns></returns>
    public bool ContainsRange(Set/*!*/ s) {
      Contract.Requires(s != null);
      if (s != this) {
        foreach (object/*!*/ key in s.ht.Keys) {
          Contract.Assert(key != null);
          if (!this.ht.ContainsKey(key)) {
            return false;
          }
        }
      }
      return true;
    }

    public object/*!*/ Clone() {
      Contract.Ensures(Contract.Result<object>() != null);
      return new Set((Hashtable/*!*/)cce.NonNull(ht.Clone()));
    }

    public virtual int Count {
      get {
        return ht.Count;
      }
    }

    [Pure]
    public IEnumerator/*!*/ GetEnumerator() {
      Contract.Ensures(Contract.Result<IEnumerator>() != null);
      return ht.Keys.GetEnumerator();
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      string s = null;
      foreach (object/*!*/ key in ht.Keys) {
        Contract.Assert(key != null);
        if (s == null) {
          s = "{";
        } else {
          s += ", ";
        }
        s += key.ToString();
      }
      if (s == null) {
        return "{}";
      } else {
        return s + "}";
      }
    }

    public bool AddAll(IEnumerable/*!*/ objs) {
      Contract.Requires(objs != null);
      foreach (object/*!*/ o in objs) {
        Contract.Assert(o != null);
        this.Add(o);
      }
      return true;
    }
    //----------------------------- Static Methods ---------------------------------

    // Functional Intersect
    public static Set/*!*/ Intersect(Set/*!*/ a, Set/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Set>() != null);
      //Contract.Ensures(Contract.ForAll(result, x => a[x] && b[x] ));
      Set/*!*/ res = (Set/*!*/)cce.NonNull(a.Clone());
      res.Intersect(b);
      return res;
    }
    // Functional Union
    public static Set/*!*/ Union(Set/*!*/ a, Set/*!*/ b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Set>() != null);
      //  Contract.Ensures(Contract.ForAll(result, x => a[x] || b[x] ));
      Set/*!*/ res = (Set/*!*/)cce.NonNull(a.Clone());
      res.AddRange(b);
      return res;
    }

    public delegate bool SetFilter(object/*!*/ obj);

    public static Set/*!*/ Filter(Set/*!*/ a, SetFilter/*!*/ filter) {
      Contract.Requires(filter != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Set>() != null);
      Set inter = new Set();

      foreach (object/*!*/ elem in a) {
        Contract.Assert(elem != null);
        if (filter(elem)) {
          inter.Add(elem);
        }
      }
      return inter;
    }

  }

  public interface IWorkList : ICollection {
    bool Add(object o);
    bool AddAll(IEnumerable objs);
    bool IsEmpty();
    object Pull();
  }


}