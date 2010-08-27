//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.Boogie
{
    using System;
    using System.IO;
    using System.Collections;
    using Microsoft.Contracts;

    /// <summary>
    /// A class representing a mathematical set.
    /// </summary>
    public class Set : ICloneable, IEnumerable 
    {
        /*[Own]*/ Hashtable! ht;

        public Set() 
        {
            ht = new Hashtable();
            base();
        }

        private Set(Hashtable! ht) 
        {
            this.ht = ht;
            base();
        }

        public Set(int capacity) 
        {
            ht = new Hashtable(capacity);
            base();
        }
        
        
        public readonly static Set! Empty = new Set();

        public void Clear() 
        {
            ht.Clear();
        }

        /// <summary>
        /// This method idempotently adds "o" to the set.
        /// In notation:
        ///   this.SetElements =  this.SetElements_old \union {o};
        /// </summary>
        public void Add(object! o) 
        {
            ht[o] = o;
        }

        /// <summary>
        /// this.SetElements =  this.SetElements_old \union s.SetElements;
        /// </summary>
        public void AddRange(Set! s) 
        {
            foreach (object! o in s) 
            {
                Add(o);
            }
        }

        /// <summary>
        /// this.SetElements =  this.SetElements_old \setminus {o};
        /// </summary>
        public void Remove(object! o) 
        {
            ht.Remove(o);
        }

        /// <summary>
        /// this.SetElements =  this.SetElements_old \setminus s.SetElements;
        /// </summary>
        public void RemoveRange(Set! s) 
        {
            if (s == this) 
            {
                ht.Clear();
            } 
            else 
            {
                foreach (object! o in s) 
                {
                    ht.Remove(o);
                }
            }
        }
        
        /// <summary>
        /// Returns an arbitrary element from the set.
        /// </summary>
        public object! Choose()
          requires Count > 0;
        {
            IEnumerator iter = GetEnumerator();
            iter.MoveNext();
            return (!)iter.Current;
        }
        
        /// <summary>
        /// Picks an arbitrary element from the set, removes it, and returns it.
        /// </summary>
        public object! Take()
          requires Count > 0;
          ensures Count == old(Count) - 1;
        {
            object r = Choose();
            Remove(r);
            return r;
        }

        public void Intersect(Set! s) 
        {
            Hashtable h = new Hashtable(ht.Count);
            foreach (object! key in ht.Keys) 
            {
                if (s.ht.ContainsKey(key)) 
                {
                    h.Add(key, key);
                }
            }
            ht = h;
        }
        
        /// <summary>
        /// The getter returns true iff "o" is in the set.
        /// The setter adds the value "o" (for "true") or removes "o" (for "false")
        /// </summary>
        public bool this[object! o] 
        {
            get 
            {
                return ht.ContainsKey(o);
            }
            set
            {
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
        public bool Contains(object! o) 
        {
          if (!this.ht.ContainsKey(o)) 
          {
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
        public bool ContainsRange(Set! s) 
        {
            if (s != this) 
            {
                foreach (object! key in s.ht.Keys) 
                {
                    if (!this.ht.ContainsKey(key)) 
                    {
                        return false;
                    }
                }
            }
            return true;
        }

        public object! Clone() 
        {
            return new Set((Hashtable!)ht.Clone());
        }

        public virtual int Count 
        {
            get 
            {
                return ht.Count;
            }
        }

        [Pure]
        public IEnumerator! GetEnumerator() 
        {
            return ht.Keys.GetEnumerator();
        }

        [Pure]
        public override string! ToString() 
        {
            string s = null;
            foreach (object! key in ht.Keys) 
            {
                if (s == null) 
                {
                    s = "{";
                } 
                else 
                {
                    s += ", ";
                }
                s += key.ToString();
            }
            if (s == null) 
            {
                return "{}";
            } 
            else 
            {
                return s + "}";
            }
        }
        
         public bool AddAll(IEnumerable! objs){
          foreach (object! o in objs){
            this.Add(o);
          }
          return true;
        }
       //----------------------------- Static Methods ---------------------------------
        
        // Functional Intersect
        public static Set! Intersect(Set! a, Set! b) 
        //  ensures Forall{ object x in result; a[x] && b[x] };
        {
            Set! res = (Set!) a.Clone();
            res.Intersect(b);
            return res;
        }
        // Functional Union
        public static Set! Union(Set! a, Set! b) 
        //  ensures Forall{ object x in result; a[x] || b[x] };
        {
            Set! res = (Set!) a.Clone();
            res.AddRange(b);
            return res;
        }
 
       public delegate bool SetFilter(object! obj);

       public static Set! Filter(Set! a, SetFilter! filter) 
       {
         Set inter = new Set();

         foreach(object! elem in a) 
         {
           if (filter(elem))
           {
             inter.Add(elem);
           }
         }	
         return inter;
       }

  }
 
   public interface IWorkList: ICollection
  {
    bool Add(object o);
    bool AddAll(IEnumerable objs);
    bool IsEmpty();
    object Pull();
  }
   

}