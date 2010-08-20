//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

//---------------------------------------------------------------------
// PureCollections.cs
//       - Mostly pure functions for tuples, sets, maps, Sequences
// Version 1.0, WS, 3/23/2002 
//---------------------------------------------------------------------


using System;
using System.Collections;
using System.Diagnostics.Contracts;

namespace PureCollections {
  //-------------------------------------------------------------------
  // General types
  //-------------------------------------------------------------------

  public class MissingCase : Exception {
  }

  public struct Capacity {
    public int capacity;
    public Capacity(int i) {
      capacity = i;
    }
  }

  abstract public class Coll {
    public object[] elems;      // null is used to show empty spots!
    protected int card;
    protected Coll() {
    }
    protected Coll(object[] elems, int card) {
      this.elems = elems;
      this.card = card;
    }
    protected Coll(Coll c) {
      Contract.Requires(c != null);
      Contract.Requires(c.elems != null);
      this.elems = (object[])c.elems.Clone();
      this.card = c.card;
    }
  }


  // ------------------------------------------------------------------
  // Tuple
  // ------------------------------------------------------------------

  public class Tuple : Coll, IComparable {
    //public object[] elems;

    //invariant this.elems != null;

    // Constructor - - - - - - - - - - - - - - - - - - - - - - - - - - 
    public Tuple(params object[] ts) {
      Contract.Requires(ts != null);
      elems = ts;
      card = ts.Length;
    }
    public Tuple(Capacity c) {
      elems = new object[c.capacity];
      card = c.capacity;
    }

    //Equality - - - - - - - - - - - - - - - - - - - - - - - - - - - - 

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object o) {
      Contract.Assert(this.elems != null);
      if (o == null || !(o is Tuple) || elems.Length != (cce.NonNull((Tuple)o).elems).Length)
        return false;

      Tuple s = (Tuple)o;
      for (int i = 0; i < elems.Length; i++)
        if (!Equals(this.elems[i], s.elems[i]))
          return false;
      return true;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]  // ugh, is this right?  --KRML
    public static bool operator ==(Tuple s, Tuple t) {
      return s == null ? t == null : s.Equals(t);
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]  // ugh, is this right?  --KRML
    public static bool operator !=(Tuple s, Tuple t) {
      return !(t == s);
    }

    [Pure]
    public override int GetHashCode() {
      int h = 0;
      Contract.Assume(this.elems != null);
      for (int i = 0; i < elems.Length; i++) {
        object elem = elems[i];
        if (elem != null)
          h += elem.GetHashCode();
      }
      return h;
    }

    //Compare - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    int IComparable.CompareTo(object o) {
      Contract.Assert(this.elems != null);
      if (o == null || !(o is Tuple) || elems.Length != (cce.NonNull((Tuple)o).elems).Length)
        throw new MissingCase();

      Tuple t = (Tuple)o;
      for (int i = 0; i < elems.Length; i++) {
        int c = cce.NonNull((IComparable)elems[i]).CompareTo(t.elems[i]);
        if (c < 0)
          return -1;
        else if (c > 0)
          return +1;
      }
      return 0;
    }

    public static bool operator <=(Tuple s, Tuple t) {
      return s == null ? t == null : ((IComparable)s).CompareTo(t) <= 0;
    }
    public static bool operator <(Tuple s, Tuple t) {
      return s == null ? false : ((IComparable)s).CompareTo(t) < 0;
    }
    public static bool operator >=(Tuple s, Tuple t) {
      return t <= s;
    }
    public static bool operator >(Tuple s, Tuple t) {
      return t < s;
    }

    //Select and Update - - - - - - - - - - - - - - - - - - - - - - - -
    public object this[int index] {
      get {
        Contract.Assert(this.elems != null);
        return elems[index];
      }
      set {
        Contract.Assert(this.elems != null);
        elems[index] = value;
      }
    }

    //ToString - - - -  - - - - - - - - - - - - - - - - - - - - - - - -
    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assert(this.elems != null);
      if (elems.Length == 0)
        return "()";

      string s = "(";
      for (int i = 0; i < elems.Length - 1; i++)
        s += cce.NonNull(elems[i]).ToString() + ", ";
      return s + cce.NonNull(elems[elems.Length - 1]).ToString() + ")";
    }
  }

  // ------------------------------------------------------------------
  // Pair
  public class Pair : Tuple {
    protected Pair() {
    }
    public Pair(object first, object second) {
      elems = new object[] { first, second };
    }
    public object First {
      get {
        Contract.Assert(this.elems != null);
        return elems[0];
      }
      set {
        Contract.Assert(this.elems != null);
        elems[0] = value;
      }
    }
    public object Second {
      get {
        Contract.Assert(this.elems != null);
        return elems[1];
      }
      set {
        Contract.Assert(this.elems != null);
        elems[1] = value;
      }
    }
  }

  // --------------------------------------------------------------------
  // Map
  // --------------------------------------------------------------------

  public class MapEnumerator : IEnumerator {
    private Map/*!*/ map;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(map != null);
    }

    private int index = -1;
    public MapEnumerator(Map m) {
      Contract.Requires(m != null);
      map = m;
    }
    public bool MoveNext() {
      do {
        index++;
        Contract.Assert(map.elems != null);
      } while (index < map.elems.Length && map.elems[index] == null);
      return index < map.elems.Length;
    }
    public object Current {
      get {
        Contract.Assert(map.elems != null);
        return new Pair(map.elems[index], map.vals[index]);
      }
    }
    public void Reset() {
      index = -1;
    }
  }

  public class Map : Coll, IEnumerable, IComparable {
    public Object[]/*!*/ vals;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(vals != null);
    }


    //invariant this.elems != null;

    // constructors - - - - - - - - - - - - - - - - - - - - - - - - - - - 
    public Map(Capacity c) {
      elems = new Object[c.capacity * 2];
      vals = new Object[c.capacity * 2];
      card = 0;
    }

    [NotDelayed]
    public Map(params Pair[] ps)
      : base() {//BASEMOVE DANGER
      Contract.Requires(ps != null);
      elems = new Object[ps.Length * 2];
      vals = new Object[ps.Length * 2];
      //base();
      card = 0;
      for (int i = 0; i < ps.Length; i++)
        Insert(cce.NonNull(ps[i]).First, cce.NonNull(ps[i]).Second);
    }

    // iterators - - - - - - - - - - - - - - - - - - - - - - - - - - - 
    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    public IEnumerator GetEnumerator() {
      Contract.Ensures(Contract.Result<IEnumerator>() != null);
      return new MapEnumerator(this);
    }
    public Pair[] ToArray() {
      Pair[] n = new Pair[card];
      int ct = 0;
      Contract.Assert(this.elems != null);
      for (int i = 0; i < elems.Length; i++)
        if (elems[i] != null)
          n[ct++] = new Pair(elems[i], vals[i]);
      return n;
    }

    //(ASM) Update- - - - - - - - - - - - - - - - - - - - - - - - - - -
    public Map Update(object k, object v) {
      Map n = new Map(new Capacity(card + 1));
      Contract.Assert(this.elems != null);
      for (int i = 0; i < elems.Length; i++)
        if (elems[i] != null && !Equals(elems[i], k))
          n.Insert(elems[i], vals[i]);
      n.Insert(k, v);
      return n;
    }

    //In place Update (and Remove)- - - - - - - - - - - - - - - - - - -
    public object this[object index] {
      get {
        return this.Apply(index);
      }
      set {
        this.Insert(index, value);
      }
    }

    public void Remove(object o) {
      Contract.Requires(o != null);
      Contract.Assert(this.elems != null);
      int h = Math.Abs(o.GetHashCode()) % elems.Length;
      for (int i = 0; i < elems.Length; i++) {
        int j = (i + h) % elems.Length;
        if (elems[j] == null) {
          break;
        } else if (Equals(elems[j], o)) {
          elems[j] = null;
          vals[j] = null;
          break;
        }
      }
    }

    public void Insert(Object key, Object val) {
      if (key == null)
        throw new MissingCase();

      Contract.Assert(this.elems != null);
      if (elems.Length == 0 || 2 * card >= elems.Length) {
        int m = card * 2;
        if (m < 4)
          m = 4;
        object[] newElems = new object[m];
        object[] newVals = new object[m];
        for (int k = 0; k < elems.Length; k++) {
          object elem = elems[k];
          if (elem != null) {
            int newHash = Math.Abs(elem.GetHashCode()) % newElems.Length;
            for (int i = 0; i < newElems.Length; i++) {
              int j = (i + newHash) % newElems.Length;
              if (newElems[j] == null) {
                newElems[j] = elem;
                newVals[j] = vals[k];
                break;
              }
            }
          }
        }
        elems = newElems;
        vals = newVals;
      }
      int h = Math.Abs(key.GetHashCode()) % elems.Length;
      for (int i = 0; i < elems.Length; i++) {
        int j = (i + h) % elems.Length;
        if (elems[j] == null) {
          elems[j] = key;
          vals[j] = val;
          card++;
          return;
        } else if (key.Equals(elems[j])) {
          vals[j] = val;
          return;
        }
      }
    }

    //ToString - - - - - - - - - - - - - - - - - - - - - - - - -
    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      if (card == 0)
        return "{|->}";
      else {
        string s = "{";
        int ct = 0;
        Contract.Assert(this.elems != null);
        for (int i = 0; i < elems.Length; i++) {
          object elem = elems[i];
          if (elem != null) {
            s += elem.ToString() + "|->" + cce.NonNull(vals[i]).ToString();
            s += (ct != card - 1) ? ", " : "";
            ct++;
          }
        }
        return s + "}";
      }
    }

    // Subset operations - - - - - - - - - - - - - - - - - - - - - - -
    // View Map as Set of Pairs

    int IComparable.CompareTo(object o) {
      if (o == null || !(o is Map))
        throw new MissingCase();
      // WS Improve performance!
      Map t = (Map)o;
      if (this < t)
        return -1;
      else if (this > t)
        return +1;
      else
        return 0;
    }
    public static bool operator <=(Map s, Map t) {
      if (s == null)
        return t == null;
      if (t == null)
        return false;
      Contract.Assert(s.elems != null);
      for (int i = 0; i < s.elems.Length; i++)
        if (s.elems[i] != null) {
          object o = t.Apply(s.elems[i]);
          if (o == null || !o.Equals(s.vals[i]))
            return false;
        }
      return true;
    }
    public static bool operator <(Map s, Map t) {
      return s == null || t == null ? false : s.card < t.card && s <= t;
    }
    public static bool operator >=(Map s, Map t) {
      return t <= s;
    }
    public static bool operator >(Map s, Map t) {
      return t < s;
    }

    // Equality - - - - - - - - - - - - - - - - - - - - - - -
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(Object t) {
      return t != null && t is Map && card == ((Map)t).card && this <= ((Map)t);
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]  // ugh, is this right?  --KRML
    public static bool operator ==(Map s, Map t) {
      if ((object)s == null)
        if ((object)t == null)
          return true;
        else
          return t.Equals(s);
      else
        return s.Equals(t);
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]  // ugh, is this right?  --KRML
    public static bool operator !=(Map s, Map t) {
      return !(t == s);
    }
    [Pure]
    public override int GetHashCode() {
      int h = 0;
      Contract.Assert(this.elems != null);
      for (int i = 0; i < elems.Length; i++) {
        object elem = elems[i];
        if (elem != null) {
          h += elem.GetHashCode() + cce.NonNull(vals[i]).GetHashCode();
        }
      }
      return h;
    }

    //Ordinary map operations- - - - - - - - - - - - - - - - - - - - - - - - 

    [Pure]
    public bool Has(Object x) {
      if (x == null)
        throw new MissingCase();

      Contract.Assert(this.elems != null);
      if (elems.Length == 0)
        return false;
      int h = Math.Abs(x.GetHashCode()) % elems.Length;
      for (int i = 0; i < elems.Length; i++) {
        int j = (i + h) % elems.Length;
        if (x.Equals(elems[j]))
          return true;
      }
      return false;
    }

    public object Apply(object x) {
      if (x == null)
        throw new MissingCase();
      Contract.Assert(this.elems != null);
      if (elems.Length == 0)
        return null;
      int h = Math.Abs(x.GetHashCode()) % elems.Length;
      for (int i = 0; i < elems.Length; i++) {
        int j = (i + h) % elems.Length;
        if (elems[j] != null && x.Equals(elems[j]))
          return vals[j];
      }
      return null;
    }

    public static Map Override(Map s, Map t) {
      Contract.Requires(t != null);
      Contract.Requires(s != null);
      Map m = new Map(new Capacity(s.card + t.card));
      Contract.Assert(s.elems != null);
      for (int i = 0; i < s.elems.Length; i++)
        if (s.elems[i] != null)
          m.Insert(s.elems[i], s.vals[i]);
      Contract.Assert(t.elems != null);
      for (int i = 0; i < t.elems.Length; i++)
        if (t.elems[i] != null)
          m.Insert(t.elems[i], t.vals[i]);
      return m;
    }
  }

  // --------------------------------------------------------------------
  // Sequence

  public class SequenceEnumerator : IEnumerator {
    [Peer]
    private Sequence/*!*/ seq;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(seq != null);
    }

    private int index = -1;
    [Captured]
    public SequenceEnumerator(Sequence s) {
      Contract.Requires(s != null);
      seq = s;
    }
    public bool MoveNext() {
      index++;
      //while (index < seq.elems.Length); // Sequences allow nils ... && seq.elems[index] == null);
      return index < seq.Length;
    }
    public object Current {
      get {
        Contract.Assert(seq.elems != null);
        return seq.elems[index];
      }
    }
    public void Reset() {
      index = -1;
    }
  }

  public class Sequence : Coll, IEnumerable, IComparable {
    public Sequence() {
      elems = new object[4];
    }

    //invariant this.elems != null;

    //constructors - - - - - - - - - - - - - - - - - - - - - - - - - - - 
    public Sequence(params object[] ds) {
      Contract.Requires(ds != null);
      card = ds.Length;
      elems = ds;
    }
    public Sequence(Sequence seq)
      : base(seq) {//BASEMOVEA
      Contract.Requires(seq != null);
      //base(seq);
    }
    public Sequence(Capacity c) {
      elems = new object[c.capacity];
    }

    // Iterators - - - - - - - - - - - - - - - - - - - - - - - - - - - 
    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    public IEnumerator/*!*/ GetEnumerator() {
      Contract.Ensures(cce.Owner.Same(Contract.Result<IEnumerator>(), this));
      Contract.Ensures(Contract.Result<IEnumerator>() != null);
      Contract.Ensures(cce.IsNew(Contract.Result<IEnumerator>()));
      return new SequenceEnumerator(this);
    }

    public object[] ToArray() {
      object[] n = new object[card];
      int ct = 0;
      Contract.Assert(this.elems != null);
      for (int i = 0; i < elems.Length; i++)
        n[ct++] = elems[i];
      return n;
    }

    //ASM Update - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    public Sequence Update(int i, object v) {
      Sequence n = new Sequence(new Capacity(card + 1));
      Contract.Assert(this.elems != null);
      Contract.Assert(n.elems != null);
      for (int j = 0; j < elems.Length; j++)
        n.elems[j] = elems[j];
      if (i >= 0 && i < card) {
        n.elems[i] = v;
        n.card = card;
        return n;
      } else if (i == card) {
        n.elems[i] = v;
        n.card = card + 1;
        return n;
      } else
        throw new Exception("Sequence Update out of range");
    }

    //In place Update (and Remove) and Length - - - - - - - - - - - - - - - 
    public int Length {
      get {
        return this.card;
      }
    }

    public object this[int index] {
      get {
        Contract.Assert(this.elems != null);
        return this.elems[index];
      }
      set {
        Contract.Assert(this.elems != null);
        this.elems[index] = value;
      }
    }

    public void Add(object o) {
      Contract.Assert(this.elems != null);
      int n = this.elems.Length;
      int i = this.card++;
      if (i == n) {
        int m = n * 2;
        if (m < 4)
          m = 4;
        object[] newElems = new object[m];
        for (int j = 0; j < n; j++)
          newElems[j] = elems[j];
        elems = newElems;
      }
      elems[i] = o;
    }

    public void AddRange(Sequence seq) {
      Contract.Requires(seq != null);
      foreach (object o in seq) {
        Add(o);
      }
    }

    public void Remove() {
      if (card == 0)
        return;
      card--;
    }

    // remove the first occurrence of o from this sequence
    public void Remove(Object x) {
      if (x == null)
        throw new MissingCase();
      Contract.Assert(this.elems != null);
      for (int i = 0; i < card; i++) {
        if (x.Equals(elems[i])) {
          ++i;
          while (i < card) {
            elems[i - 1] = elems[i];
            ++i;
          }
          card--;
          elems[card] = null;
          return;
        }
      }
    }

    public void Truncate(int newLen) {
      Contract.Requires(0 <= newLen && newLen <= Length);
      Contract.Assert(elems != null);
      for (int i = newLen; i < card; i++) {
        elems[i] = null;
      }
      card = newLen;
    }

    //ToString - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      string s = "";
      if (this.elems == null)
        return "(null)";
      Contract.Assert(this.elems != null);
      if (card > 0 && elems[0] is Char) {
        for (int i = 0; i < card; i++) {
          object elem = elems[i];
          if (elem != null) {
            s += elem.ToString();
          }
        }
        return s;
      } else {
        s = "[";
        for (int i = 0; i < card - 1; i++) {
          object elem = elems[i];
          if (elem != null) {
            s += elem.ToString() + ", ";
          }
        }
        if (card > 0) {
          object last = elems[card - 1];
          if (last != null) {
            s += last.ToString();
          }
        }
        s += "]";
        return s;
      }
    }
    //Equality- - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that) {
      return that != null && that is Sequence && ((Sequence)this == (Sequence)that);
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]  // ugh, is this right?  --KRML
    public static bool operator ==(Sequence s, Sequence t) {
      if ((object)s == (object)t) {
        return true;
      } else if ((object)s == null || (object)t == null) {
        return false;
      }
      if (s.card != t.card)
        return false;
      Contract.Assert(s.elems != null);
      Contract.Assert(t.elems != null);
      for (int i = 0; i < s.card; i++)
        if (!Equals(s.elems[i], t.elems[i]))
          return false;
      return true;
    }
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]  // ugh, is this right?  --KRML
    public static bool operator !=(Sequence s, Sequence t) {
      return !(s == t);
    }
    [Pure]
    public override int GetHashCode() {
      int h = 0;
      for (int i = 0; i < card; i++) {
        Contract.Assert(this.elems != null);
        object elem = elems[i];
        if (elem != null) {
          h += elem.GetHashCode();
        }
      }
      return h;
    }
    //Subset- - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
    // View Sequence of T as Set of (Integer,T) 
    int IComparable.CompareTo(object o) {
      if (o == null || !(o is Sequence))
        throw new MissingCase();
      // WS Improve performance!
      Sequence t = (Sequence)o;
      if (this < t)
        return -1;
      else if (this > t)
        return +1;
      else
        return 0;
    }

    public static bool operator <(Sequence s, Sequence t) {
      if (s == null)
        throw new ArgumentNullException("s");
      if (t == null)
        throw new ArgumentNullException("t");
      if (s.card >= t.card)
        return false;
      Contract.Assert(s.elems != null);
      Contract.Assert(t.elems != null);
      for (int i = 0; i < s.card; i++)
        if (!Equals(s.elems[i], t.elems[i]))
          return false;
      return true;
    }
    public static bool operator <=(Sequence s, Sequence t) {
      if (s == null)
        throw new ArgumentNullException("s");
      if (t == null)
        throw new ArgumentNullException("t");
      if (s.card > t.card)
        return false;
      Contract.Assert(s.elems != null);
      Contract.Assert(t.elems != null);
      for (int i = 0; i < s.card; i++)
        if (!Equals(s.elems[i], t.elems[i]))
          return false;
      return true;
    }
    public static bool operator >(Sequence s, Sequence t) {
      return t < s;
    }
    public static bool operator >=(Sequence s, Sequence t) {
      return t <= s;
    }

    //pure---------------------------------------------------------------
    [Pure]
    public bool Has(object x) {         // WS translate to tailrecursion 
      if (x == null)
        throw new MissingCase();
      Contract.Assert(this.elems != null);
      for (int i = 0; i < card; i++)
        if (x.Equals(elems[i]))
          return true;
      return false;
    }

    // the index of the first occurrence of x in this sequence,
    // or -1 if x does not occur
    [Pure]
    public int IndexOf(object x) {
      if (x == null)
        throw new MissingCase();
      Contract.Assert(this.elems != null);
      for (int i = 0; i < card; i++)
        if (x.Equals(elems[i]))
          return i;
      return -1;
    }

    // the index of the last occurrence of x in this sequence,
    // or -1 if x does not occur
    [Pure]
    public int LastIndexOf(object x) {
      if (x == null)
        throw new MissingCase();
      Contract.Assert(this.elems != null);
      for (int i = card - 1; i >= 0; i--)
        if (x.Equals(elems[i]))
          return i;
      return -1;
    }

    public object Head() {
      Contract.Assert(this.elems != null);
      return elems[0];
    }
    public object Last() {
      Contract.Assert(this.elems != null);
      return elems[card - 1];
    }

    public static Sequence Tail(Sequence s) {
      Contract.Requires(s != null);
      Sequence n = new Sequence(new Capacity(s.card - 1));
      Contract.Assert(n.elems != null);
      Contract.Assert(s.elems != null);
      for (int i = 1; i < s.card; i++)
        n.elems[n.card++] = s.elems[i];
      return n;
    }

    public static Sequence Front(Sequence s) {
      Contract.Requires(s != null);
      Sequence n = new Sequence(new Capacity(s.card - 1));
      Contract.Assert(n.elems != null);
      Contract.Assert(s.elems != null);
      for (int i = 0; i < s.card - 1; i++)
        n.elems[n.card++] = s.elems[i];
      return n;
    }
    public static Sequence Concat(Sequence s) {
      Contract.Requires(s != null);
      Sequence n = new Sequence(new Capacity(s.card));
      Contract.Assert(n.elems != null);
      Contract.Assert(s.elems != null);
      for (int i = 0; i < s.card; i++) {
        Sequence t = (Sequence)cce.NonNull(s.elems[i]);
        Contract.Assert(t.elems != null);
        for (int j = 0; j < t.card; j++)
          n.Add(t.elems[j]);
      }
      return n;
    }

    public static Sequence Reverse(Sequence s) {
      Contract.Requires(s != null);
      Sequence n = new Sequence(new Capacity(s.card));
      Contract.Assert(n.elems != null);
      Contract.Assert(s.elems != null);
      for (int i = s.card - 1; i >= 0; i--)
        n.elems[n.card++] = s.elems[i];
      return n;
    }

    public static Sequence operator +(Sequence s, Sequence t) {
      if (s == null)
        throw new ArgumentNullException("s");
      if (t == null)
        throw new ArgumentNullException("t");
      return Append(t, s);
    }

    public static Sequence Append(Sequence s, Sequence t) {
      Contract.Requires(t != null);
      Contract.Requires(s != null);
      Contract.Ensures(Contract.Result<Sequence>() != null);
      Sequence n = new Sequence(new Capacity(s.card + t.card));
      Contract.Assert(n != null);
      Contract.Assert(n.elems != null);
      Contract.Assert(s.elems != null);
      Contract.Assert(t.elems != null);
      for (int i = 0; i < s.card; i++)
        n.elems[n.card++] = s.elems[i];
      for (int i = 0; i < t.card; i++)
        n.elems[n.card++] = t.elems[i];
      return n;
    }
    public static Sequence Zip(Sequence s, Sequence t) {
      Contract.Requires(t != null);
      Contract.Requires(s != null);
      int min = s.card < t.card ? s.card : t.card;
      Sequence n = new Sequence(new Capacity(min));
      Contract.Assert(n.elems != null);
      Contract.Assert(s.elems != null);
      Contract.Assert(t.elems != null);
      for (int i = 0; i < min; i++)
        n.elems[n.card++] = new Tuple(s.elems[i], t.elems[i]);
      return n;
    }
    public static Tuple Unzip(Sequence s) {
      Contract.Requires(s != null);
      Sequence n0 = new Sequence(new Capacity(s.card));
      Sequence n1 = new Sequence(new Capacity(s.card));
      Contract.Assert(s.elems != null);
      Contract.Assert(n0.elems != null);
      Contract.Assert(n1.elems != null);
      for (int i = 0; i < s.card; i++) {
        n0.elems[n0.card++] = (cce.NonNull((Tuple)s.elems[i]).elems)[0];
        n1.elems[n1.card++] = (cce.NonNull((Tuple)s.elems[i]).elems)[1];
      }
      return new Tuple(n0, n1);
    }

    public static Sequence FromTo(int from, int to) {       //WS hash the result! 
      if (from > to)
        return new Sequence();
      Sequence n = new Sequence(new Capacity(to - from + 1));
      Contract.Assert(n.elems != null);
      for (int i = from; i <= to; i++)
        n.elems[n.card++] = i;
      return n;
    }

    public static Sequence FromStepTo(int from, int step, int to) {
      Sequence n = new Sequence();
      int incr = step - from;
      if (incr > 0)
        for (int i = from; i <= to; i += incr)
          n.Add(i);
      else if (incr < 0)
        for (int i = to; i >= from; i -= incr)
          n.Add(i);
      return n;
    }

  }
}