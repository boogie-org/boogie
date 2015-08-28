//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Diagnostics.Contracts;

namespace Microsoft.AbstractInterpretationFramework.Collections {
  using System.Collections;

  /// <summary>Represents a functional collection of key/value pairs.</summary>
  /// <filterpriority>2</filterpriority>
  [ContractClass(typeof(IFunctionalMapContracts))]
  public interface IFunctionalMap : System.Collections.ICollection, System.Collections.IEnumerable {
    /// <summary>Adds an element with the provided key and value to the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />.</summary>
    /// <param name="value">The <see cref="T:System.Object" /> to use as the value of the element to add. </param>
    /// <param name="key">The <see cref="T:System.Object" /> to use as the key of the element to add. </param>
    /// <filterpriority>2</filterpriority>
    IFunctionalMap/*!*/ Add(object/*!*/ key, object value);

    /// <summary>
    /// Set the value of the key (that is already in the map)
    /// </summary>
    IFunctionalMap/*!*/ Set(object/*!*/ key, object value);

    /// <summary>Determines whether the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" /> contains an element with the specified key.</summary>
    /// <returns>true if the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" /> contains an element with the key; otherwise, false.</returns>
    /// <param name="key">The key to locate in the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />. </param>
    /// <filterpriority>2</filterpriority>
    [Pure]
    bool Contains(object/*!*/ key);

    /// <summary>Returns an <see cref="T:System.Collections.IDictionaryEnumerator" /> for the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />.</summary>
    /// <returns>An <see cref="T:System.Collections.IDictionaryEnumerator" /> for the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />.</returns>
    /// <filterpriority>2</filterpriority>
    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    new System.Collections.IDictionaryEnumerator GetEnumerator();

    /// <summary>Gets an <see cref="T:System.Collections.ICollection" /> containing the keys of the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />.</summary>
    /// <returns>An <see cref="T:System.Collections.ICollection" /> containing the keys of the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />.</returns>
    /// <filterpriority>2</filterpriority>
    System.Collections.ICollection Keys {
      get;
    }

    /// <summary>Removes the element with the specified key from the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />.</summary>
    /// <param name="key">The key of the element to remove. </param>
    /// <filterpriority>2</filterpriority>
    IFunctionalMap/*!*/ Remove(object/*!*/ key);

    /// <summary>Gets an <see cref="T:System.Collections.ICollection" /> containing the values in the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />.</summary>
    /// <returns>An <see cref="T:System.Collections.ICollection" /> containing the values in the <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />.</returns>
    /// <filterpriority>2</filterpriority>
    System.Collections.ICollection Values {
      get;
    }

    object this[object/*!*/ key] {
      get; /*set;*/
    }
  }
  [ContractClassFor(typeof(IFunctionalMap))]
  public abstract class IFunctionalMapContracts : IFunctionalMap {

    #region IFunctionalMap Members

    IFunctionalMap IFunctionalMap.Add(object key, object value) {
      Contract.Requires(key != null);
      Contract.Ensures(Contract.Result<IFunctionalMap>() != null);

      throw new System.NotImplementedException();
    }

    IFunctionalMap IFunctionalMap.Set(object key, object value) {
      Contract.Requires(key != null);
      Contract.Ensures(Contract.Result<IFunctionalMap>() != null);

      throw new System.NotImplementedException();
    }

    bool IFunctionalMap.Contains(object key) {
      Contract.Requires(key != null);

      throw new System.NotImplementedException();
    }

    IDictionaryEnumerator IFunctionalMap.GetEnumerator() {
      throw new System.NotImplementedException();
    }

    ICollection IFunctionalMap.Keys {
      get {
        throw new System.NotImplementedException();
      }
    }

    IFunctionalMap IFunctionalMap.Remove(object key) {
      Contract.Requires(key != null);
      Contract.Ensures(Contract.Result<IFunctionalMap>() != null);

      throw new System.NotImplementedException();
    }

    ICollection IFunctionalMap.Values {
      get {
        throw new System.NotImplementedException();
      }
    }

    object IFunctionalMap.this[object key] {
      get {
        Contract.Requires(key != null);
        throw new System.NotImplementedException();
      }
    }

    #endregion

    #region ICollection Members

    void ICollection.CopyTo(System.Array array, int index) {
      throw new System.NotImplementedException();
    }

    int ICollection.Count {
      get {
        throw new System.NotImplementedException();
      }
    }

    bool ICollection.IsSynchronized {
      get {
        throw new System.NotImplementedException();
      }
    }

    object ICollection.SyncRoot {
      get {
        throw new System.NotImplementedException();
      }
    }

    #endregion

    #region IEnumerable Members

    IEnumerator IEnumerable.GetEnumerator() {
      throw new System.NotImplementedException();
    }

    #endregion
  }



  /// <summary>
  ///  An implementation of the
  ///  <see cref="T:Microsoft.AbstractInterpretationFramework.Collections.IFunctionalMap" />
  ///  interface with a <see cref="T:System.Collections.Hashtable" /> as the backing store.
  /// </summary>
  class FunctionalHashtable : IFunctionalMap {
    private readonly Hashtable/*!*/ h;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(h != null);
    }


    /// <summary>
    ///  Cannot directly construct an instance of a FunctionalHashtbl.
    /// </summary>
    private FunctionalHashtable() {
      this.h = new Hashtable();
      //            base();
    }

    /// <summary>
    ///  Cannot directly construct an instance of a FunctionalHashtbl.
    /// </summary>
    private FunctionalHashtable(Hashtable/*!*/ h) {
      Contract.Requires(h != null);
      this.h = h;
      //            base();
    }

    private static readonly IFunctionalMap/*!*/ empty = new FunctionalHashtable();
    public static IFunctionalMap/*!*/ Empty {
      get {
        Contract.Ensures(Contract.Result<IFunctionalMap>() != null);
        return empty;
      }
    }

    public IFunctionalMap/*!*/ Add(object/*!*/ key, object value) {
      //Contract.Requires(key != null);
      Contract.Ensures(Contract.Result<IFunctionalMap>() != null);
      Hashtable r = h.Clone() as Hashtable;
      Contract.Assume(r != null);
      r.Add(key, value);
      return new FunctionalHashtable(r);
    }

    public IFunctionalMap/*!*/ Set(object/*!*/ key, object value) {
      //Contract.Requires(key != null);
      Contract.Ensures(Contract.Result<IFunctionalMap>() != null);
      Hashtable r = h.Clone() as Hashtable;

      Contract.Assume(r != null);
      Contract.Assert(this.Contains(key));    // The entry must be defined

      r[key] = value;
      return new FunctionalHashtable(r);
    }

    [Pure]
    public bool Contains(object/*!*/ key) {
      //Contract.Requires(key != null);
      return h.Contains(key);
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IEnumerator/*!*/ IEnumerable.GetEnumerator() {
      Contract.Ensures(Contract.Result<IEnumerator>() != null);

      return h.GetEnumerator();
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IDictionaryEnumerator IFunctionalMap.GetEnumerator() {
      return h.GetEnumerator();
    }

    public ICollection Keys {
      get {
        return h.Keys;
      }
    }

    public IFunctionalMap/*!*/ Remove(object/*!*/ key) {
      //Contract.Requires(key != null);
      Contract.Ensures(Contract.Result<IFunctionalMap>() != null);
      Hashtable r = h.Clone() as Hashtable;
      Contract.Assume(r != null);
      r.Remove(key);
      return new FunctionalHashtable(r);
    }

    public ICollection Values {
      get {
        return h.Values;
      }
    }


    public object this[object/*!*/ key] {
      get {
        //Contract.Requires(key != null);
        return h[key];
      }
    }

    public int Count {
      [Pure]
      get {
        return h.Count;
      }
    }

    public bool IsSynchronized {
      [Pure]
      get {
        return h.IsSynchronized;
      }
    }

    public object/*!*/ SyncRoot {
      [Pure]
      get {
        Contract.Ensures(Contract.Result<object>() != null);
        return h.SyncRoot;
      }
    }

    public void CopyTo(System.Array/*!*/ a, int index) {
      //Contract.Requires(a != null);
      h.CopyTo(a, index);
    }
  }

  public struct Pair/*<T1,T2>*/
  {
    private object first;
    private object second;

    public object First {
      get {
        return first;
      }
    }
    public object Second {
      get {
        return second;
      }
    }

    public Pair(object first, object second) {
      this.first = first;
      this.second = second;
    }

    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is Pair))
        return false;

      Pair other = (Pair)obj;
      return object.Equals(this.first, other.first) && object.Equals(this.second, other.second);
    }

    public override int GetHashCode() {
      int h = this.first == null ? 0 : this.first.GetHashCode();
      h ^= this.second == null ? 0 : this.second.GetHashCode();
      return h;
    }
  }
}


namespace Microsoft.AbstractInterpretationFramework.Collections.Generic {
  using System.Collections.Generic;

  public struct Pair<T1, T2> {
    private T1 first;
    private T2 second;

    public T1 First {
      get {
        return first;
      }
    }
    public T2 Second {
      get {
        return second;
      }
    }

    public Pair(T1 first, T2 second) {
      this.first = first;
      this.second = second;
    }

    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is Pair<T1, T2>))
        return false;

      Pair<T1, T2> other = (Pair<T1, T2>)obj;
      return object.Equals(this.first, other.first) && object.Equals(this.second, other.second);
    }

    public override int GetHashCode() {
      int h = this.first == null ? 0 : this.first.GetHashCode();
      h ^= this.second == null ? 0 : this.second.GetHashCode();
      return h;
    }

    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return string.Format("({0},{1})", first, second);
    }
  }

  public struct Triple<T1, T2, T3> {
    private T1 first;
    private T2 second;
    private T3 third;

    public T1 First {
      get {
        return first;
      }
    }
    public T2 Second {
      get {
        return second;
      }
    }
    public T3 Third {
      get {
        return third;
      }
    }

    public Triple(T1 first, T2 second, T3 third) {
      this.first = first;
      this.second = second;
      this.third = third;
    }

    public override bool Equals(object obj) {
      if (obj == null)
        return false;
      if (!(obj is Triple<T1, T2, T3>))
        return false;

      Triple<T1, T2, T3> other = (Triple<T1, T2, T3>)obj;
      return object.Equals(this.first, other.first) && object.Equals(this.second, other.second) && object.Equals(this.third, other.third);
    }

    public override int GetHashCode() {
      int h = this.first == null ? 0 : this.first.GetHashCode();
      h ^= this.second == null ? 0 : this.second.GetHashCode();
      h ^= this.third == null ? 0 : this.third.GetHashCode();
      return h;
    }

    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return string.Format("({0},{1},{2})", first, second, third);
    }
  }
}
