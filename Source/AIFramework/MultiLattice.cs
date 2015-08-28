//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework {
  using System.Diagnostics.Contracts;
  using System.Collections;
  using System.Collections.Generic;
  using System.Diagnostics;
  using Microsoft.AbstractInterpretationFramework.Collections;

  using Microsoft.Boogie;

  using ISet = Microsoft.Boogie.GSet<object>;
  using Set = Microsoft.Boogie.GSet<object>;


  /// <summary>
  ///  The cartesian product lattice.
  /// </summary>
  public class MultiLattice : Lattice, IEnumerable {
    internal class Elt : Element {
      public /*MaybeNull*/Element[] elementPerLattice;

      public Elt(int domainCount, bool isBottom) {
        this.elementPerLattice = (domainCount == 0 && isBottom) ? null : new Element[domainCount];
      }

      private Elt(Elt/*!*/ other) {
        Contract.Requires(other != null);
        Element[] otherEPL = other.elementPerLattice;
        if (otherEPL != null) {
          Element[] newEPL = new Element[otherEPL.Length];
          for (int i = 0; i < newEPL.Length; i++) {
            newEPL[i] = (Element)(cce.NonNull(otherEPL[i])).Clone();
          }
          this.elementPerLattice = newEPL;
        }
      }

      public override Element/*!*/ Clone() {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(this);
      }

      [Pure]
      public override string/*!*/ ToString() {
        Contract.Ensures(Contract.Result<string>() != null);
        //                string s = "MultiLattice+Elt{";
        //                string sep = "";
        //                Element[] epl = this.elementPerLattice;
        //                if (epl != null)
        //                {
        //                    foreach (Element! e in epl)
        //                    {
        //                        s += sep + e.ToString();
        //                        sep = ", ";
        //                    }
        //                }
        //                return s + "}";
        if (elementPerLattice == null)
          return "";
        System.Text.StringBuilder buffer = new System.Text.StringBuilder();
        for (int i = 0; i < this.Count; i++) {
          if (i > 0)
            buffer.Append("; ");
          buffer.AppendFormat("{0}", elementPerLattice[i]);
        }
        return buffer.ToString();
      }

      public override void Dump(string/*!*/ msg) {
        //Contract.Requires(msg != null);
        System.Console.WriteLine("MultiLattice.Elt.Dump({0})", msg);
        Element[] epl = this.elementPerLattice;
        if (epl != null) {
          foreach (Element/*!*/ e in epl) {
            Contract.Assert(e != null);
            e.Dump(msg);
          }
        }
      }

      [Pure]
      public override ICollection<IVariable/*!*/>/*!*/ FreeVariables() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<ICollection<IVariable>>()));
        List<IVariable/*!*/>/*!*/ list = new List<IVariable/*!*/>();
        for (int i = 0; i < this.Count; i++) {
          list.AddRange(cce.NonNull(this[i]).FreeVariables());
        }
        return cce.NonNull(list.AsReadOnly());
      }

      public static Elt/*!*/ Top(ArrayList/*<Lattice>*//*!*/ lattices) {
        Contract.Requires(lattices != null);
        Contract.Ensures(Contract.Result<Elt>() != null);
        Elt multiValue = new Elt(lattices.Count, false);
        for (int i = 0; i < lattices.Count; i++) {
          Lattice d = (Lattice/*!*/)cce.NonNull(lattices[i]);
          multiValue[d.Index] = d.Top;
        }
        Debug.Assert(multiValue.IsValid);
        return multiValue;
      }


      public static Elt/*!*/ Bottom(ArrayList/*<Lattice>*//*!*/ lattices) {
        Contract.Requires(lattices != null);
        Contract.Ensures(Contract.Result<Elt>() != null);
        Elt multiValue = new Elt(lattices.Count, true);
        for (int i = 0; i < lattices.Count; i++) {
          Lattice d = (Lattice/*!*/)cce.NonNull(lattices[i]);
          multiValue[d.Index] = d.Bottom;
        }
        Debug.Assert(multiValue.IsValid);
        return multiValue;
      }

      public bool IsValid {
        get {
          if (this.elementPerLattice == null) {
            return true; /*bottom*/
          }

          Element[] epl = this.elementPerLattice;
          for (int i = 0; i < epl.Length; i++) {
            if (epl[i] == null) {
              return false;
            }
          }
          return true;
        }
      }

      public int Count {
        get {
          return this.elementPerLattice == null ? 0 : this.elementPerLattice.Length;
        }
      }

      public bool Contains(int i) {
        return 0 <= i && i < this.Count;
      }

      public Element this[int i] // just syntactic sugar
      {
        get {
          Element[] epl = this.elementPerLattice;
          return epl == null ? null : epl[i];
        }
        set {
          Element[] epl = this.elementPerLattice;
          if (epl == null)
            return;
          epl[i] = value;
        }
      }

    } // class


    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(lattices != null);
      Contract.Invariant(propExprFactory != null);
    }

    ArrayList/*<Lattice>*//*!*/ lattices = new ArrayList();

    private readonly IPropExprFactory/*!*/ propExprFactory;


    public MultiLattice(IPropExprFactory/*!*/ propExprFactory, IValueExprFactory/*!*/ valueExprFactory)
      : base(valueExprFactory) {
      Contract.Requires(valueExprFactory != null);
      Contract.Requires(propExprFactory != null);
      this.propExprFactory = propExprFactory;
      // base(valueExprFactory);
    }



    public void AddLattice(Lattice lattice) {
      this.lattices.Add(lattice);
    }

    private Lattice/*!*/ SubLattice(int i) {
      Contract.Ensures(Contract.Result<Lattice>() != null);
      return (Lattice/*!*/)cce.NonNull(this.lattices[i]);
    }


    public override Element/*!*/ Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return Elt.Top(this.lattices);
      }
    }

    public override Element/*!*/ Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return Elt.Bottom(this.lattices);
      }
    }




    public override bool IsBottom(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      // The program is errorneous/nonterminating if any subdomain knows it is.
      //
      if (e.elementPerLattice == null) {
        return true;
      }
      for (int i = 0; i < e.Count; i++) {
        if (SubLattice(i).IsBottom(cce.NonNull(e[i]))) {
          return true;
        }
      }
      return false;
    }

    public override bool IsTop(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      if (e.elementPerLattice == null) {
        return false;
      }
      // The multidomain knows nothing about the program only if no subdomain
      // knows anything about it.
      //
      for (int i = 0; i < e.Count; i++) {
        if (!SubLattice(i).IsTop(cce.NonNull(e[i]))) {
          return false;
        }
      }
      return true;
    }

    protected override bool AtMost(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;

      for (int i = 0; i < a.Count; i++) {
        Element thisElement = cce.NonNull(a[i]);
        Element thatElement = cce.NonNull(b[i]);
        if (thisElement.GetType() != thatElement.GetType()) {
          throw new System.InvalidOperationException(
            "AtMost called on MultiDomain objects with different lattices"
            );
        }
        if (!SubLattice(i).LowerThan(thisElement, thatElement)) {
          return false;
        }
      }
      return true;
    }

    protected override bool AtMost(Element/*!*/ first, ICombineNameMap/*!*/ firstToResult, Element/*!*/ second, ICombineNameMap/*!*/ secondToResult) {
      //Contract.Requires(secondToResult != null);
      //Contract.Requires(second != null);
      //Contract.Requires(firstToResult != null);
      //Contract.Requires(first != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;

      for (int i = 0; i < a.Count; i++) {
        Element thisElement = cce.NonNull(a[i]);
        Element thatElement = cce.NonNull(b[i]);
        if (thisElement.GetType() != thatElement.GetType()) {
          throw new System.InvalidOperationException(
            "AtMost called on MultiDomain objects with different lattices"
            );
        }
        if (!SubLattice(i).LowerThan(thisElement, firstToResult, thatElement, secondToResult)) {
          return false;
        }
      }
      return true;
    }


    private enum CombineOp {
      Meet,
      Join,
      Widen
    }

    private Element/*!*/ Combine(Element/*!*/ first, ICombineNameMap/*?*/ firstToResult, Element/*!*/ second, ICombineNameMap/*?*/ secondToResult, CombineOp c) {
      Contract.Requires(second != null);
      Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;

      int unionCount = System.Math.Max(a.Count, b.Count);
      Elt combined = new Elt(unionCount, IsBottom(a) && IsBottom(b));
      for (int i = 0; i < unionCount; i++) {
        bool thisExists = a.Contains(i);
        bool thatExists = b.Contains(i);

        if (thisExists && thatExists) {
          Lattice.Element suba = a[i];
          Lattice.Element subb = b[i];
          Contract.Assert(suba != null && subb != null);

          switch (c) {
            case CombineOp.Meet:
              combined[i] = SubLattice(i).Meet(suba, subb);
              break;
            case CombineOp.Join:
              if (firstToResult != null && secondToResult != null)
                combined[i] = SubLattice(i).Join(suba, firstToResult, subb, secondToResult);
              else
                combined[i] = SubLattice(i).Join(suba, subb);
              break;
            case CombineOp.Widen:
              if (firstToResult != null && secondToResult != null)
                combined[i] = SubLattice(i).Widen(suba, firstToResult, subb, secondToResult);
              else
                combined[i] = SubLattice(i).Widen(suba, subb);
              break;
          }
        } else if (thisExists) {
          combined[i] = a[i];
        } else {
          combined[i] = b[i];
        }
      }
      Debug.Assert(combined.IsValid);
      return combined;
    }

    public override Element/*!*/ NontrivialJoin(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires((b != null));
      //Contract.Requires((a != null));
      Contract.Ensures(Contract.Result<Element>() != null);
      return this.Combine(a, null, b, null, CombineOp.Join);
    }

    public override Element/*!*/ NontrivialJoin(Element/*!*/ a, ICombineNameMap/*!*/ aToResult, Element/*!*/ b, ICombineNameMap/*!*/ bToResult) {
      //Contract.Requires((bToResult != null));
      //Contract.Requires((b != null));
      //Contract.Requires((aToResult != null));
      //Contract.Requires((a != null));
      Contract.Ensures(Contract.Result<Element>() != null);
      return this.Combine(a, aToResult, b, bToResult, CombineOp.Join);
    }

    public override Element/*!*/ NontrivialMeet(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires((b != null));
      //Contract.Requires((a != null));
      Contract.Ensures(Contract.Result<Element>() != null);
      return this.Combine(a, null, b, null, CombineOp.Meet);
    }

    public override Element/*!*/ Widen(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires((b != null));
      //Contract.Requires((a != null));
      Contract.Ensures(Contract.Result<Element>() != null);
      return this.Combine(a, null, b, null, CombineOp.Widen);
    }

    public override Element/*!*/ Widen(Element/*!*/ a, ICombineNameMap/*!*/ aToResult, Element/*!*/ b, ICombineNameMap/*!*/ bToResult) {
      //Contract.Requires((bToResult != null));
      //Contract.Requires((b != null));
      //Contract.Requires((aToResult != null));

      //Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return this.Combine(a, aToResult, b, bToResult, CombineOp.Widen);
    }

    public override Element/*!*/ Eliminate(Element/*!*/ element, IVariable/*!*/ variable) {
      //Contract.Requires(variable != null);
      //Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt e = (Elt)element;
      if (IsBottom(e)) {
        return e;
      }
      Elt newValue = new Elt(e.Count, false);
      for (int i = 0; i < this.lattices.Count; i++) {
        newValue[i] = SubLattice(i).Eliminate(cce.NonNull(e[i]), variable);
      }
      return newValue;
    }


    public override Element/*!*/ Constrain(Element/*!*/ element, IExpr/*!*/ expr) {
      //Contract.Requires(expr != null);
      //Contract.Requires(element != null);
      //Contract.Ensures(Contract.Result<Element>() != null);
      Elt e = (Elt)element;
      if (IsBottom(e)) {
        return e;
      }
      Elt newValue = new Elt(e.Count, false);
      for (int i = 0; i < this.lattices.Count; i++) {
        newValue[i] = SubLattice(i).Constrain(cce.NonNull(e[i]), expr);
      }
      return newValue;
    }


    public override Element/*!*/ Rename(Element/*!*/ element, IVariable/*!*/ oldName, IVariable/*!*/ newName) {
      //Contract.Requires(newName != null);
      //Contract.Requires(oldName != null);
      //Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt e = (Elt)element;
      if (IsBottom(e)) {
        return e;
      }
      Elt newValue = new Elt(e.Count, false);
      for (int i = 0; i < this.lattices.Count; i++) {
        newValue[i] = SubLattice(i).Rename(cce.NonNull(e[i]), oldName, newName);
      }
      return newValue;
    }


    public override bool Understands(IFunctionSymbol/*!*/ f, IList/*!*/ args) {
      //Contract.Requires(args != null);
      //Contract.Requires(f != null);
      bool result = false;

      for (int i = 0; i < this.lattices.Count; i++) {
        result = (result || SubLattice(i).Understands(f, args));
      }

      return result;
    }


    public override string/*!*/ ToString(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<string>() != null);
      Elt e = (Elt)element;
      return e.ToString();
    }


    public override IExpr/*!*/ ToPredicate(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      Elt e = (Elt)element;

      IExpr result = propExprFactory.True;
      for (int i = 0; i < e.Count; i++) {
        IExpr conjunct = SubLattice(i).ToPredicate(cce.NonNull(e[i]));
        Contract.Assert(conjunct != null);

        result = Prop.SimplifiedAnd(propExprFactory, conjunct, result);
      }
      return result;
    }

    /// <summary>
    ///  Return an expression that is equivalent to the given expression that does not
    ///  contain the given variable according to the lattice element and queryable.
    /// 
    ///  Simply asks each sublattice to try to generate an equivalent expression.  We
    ///  do not try to combine information to infer new equivalences here.
    /// </summary>
    /// <param name="e">The lattice element.</param>
    /// <param name="q">A queryable for asking addtional information.</param>
    /// <param name="expr">The expression to find an equivalent expression.</param>
    /// <param name="var">The variable to eliminate.</param>
    /// <returns>
    /// An equivalent expression to <paramref name="expr"/> without <paramref name="var"/>
    /// or null if not possible.
    /// </returns>
    public override IExpr/*?*/ EquivalentExpr(Element/*!*/ element, IQueryable/*!*/ q, IExpr/*!*/ expr, IVariable/*!*/ var, Set/*<IVariable!>*//*!*/ prohibitedVars) {
      //Contract.Requires(prohibitedVars != null);
      //Contract.Requires(var != null);
      //Contract.Requires(expr != null);
      //Contract.Requires(q != null);
      //Contract.Requires(element != null);
      Elt/*!*/ e = (Elt/*!*/)cce.NonNull(element);

      for (int i = 0; i < e.Count; i++) {
        IExpr equivexpr = SubLattice(i).EquivalentExpr(cce.NonNull(e[i]), q, expr, var, prohibitedVars);

        if (equivexpr != null)
          return equivexpr;
      }

      return null;
    }


    public override Answer CheckPredicate(Element/*!*/ element, IExpr/*!*/ pred) {
      //Contract.Requires(pred != null);
      //Contract.Requires(element != null);
      Elt/*!*/ e = (Elt/*!*/)cce.NonNull(element);

      for (int i = 0; i < e.Count; i++) {
        Answer ans = SubLattice(i).CheckPredicate(cce.NonNull(e[i]), pred);

        if (ans == Answer.Yes || ans == Answer.No)
          return ans;
      }

      return Answer.Maybe;
    }


    public override Answer CheckVariableDisequality(Element/*!*/ element, IVariable/*!*/ var1, IVariable/*!*/ var2) {
      //Contract.Requires(var2 != null);
      //Contract.Requires(var1 != null);
      //Contract.Requires(element != null);
      Elt/*!*/ e = (Elt/*!*/)cce.NonNull(element);

      for (int i = 0; i < e.Count; i++) {
        Answer ans = SubLattice(i).CheckVariableDisequality(cce.NonNull(e[i]), var1, var2);

        if (ans == Answer.Yes || ans == Answer.No)
          return ans;
      }

      return Answer.Maybe;
    }



    public override void Validate() {
      base.Validate();
      foreach (Lattice/*!*/ l in lattices) {
        Contract.Assert(l != null);
        l.Validate();
      }
    }

    /// <summary>
    ///  The enumeration over a MultiLattice is its sublattices.
    /// </summary>
    /// <returns>An enumerator over the sublattices.</returns>
    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    public IEnumerator/*<Lattice!>*//*!*/ GetEnumerator() {
      Contract.Ensures(Contract.Result<IEnumerator>() != null);
      return lattices.GetEnumerator();
    }

    /// <summary>
    ///  Return an enumerable over a mapping of sublattices to the their corresponding
    ///  lattice elements given a MultiLattice element.
    /// </summary>
    /// <param name="element">The MultiLattice element.</param>
    /// <returns>
    /// An enumerable that yields an IDictionaryEnumerator over the
    /// (Lattice, Lattice.Element) pairs.
    /// </returns>
    public IEnumerable/*!*/ Subelements(Element/*!*/ element) {
      Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<IEnumerable>() != null);
      return new SubelementsEnumerable(this, (Elt/*!*/)cce.NonNull(element));
    }

    /// <summary>
    ///  An enumerator over the sublattices and elements.
    /// </summary>
    private sealed class SubelementsEnumerable : IEnumerable {
      private sealed class SubelementsEnumerator : IDictionaryEnumerator {
        private readonly IEnumerator/*<Lattice!>*//*!*/ multiLatticeIter;
        private readonly IEnumerator/*<Lattice.Element!>*//*!*/ multiElementIter;
        [ContractInvariantMethod]
        void ObjectInvariant() {
          Contract.Invariant(multiElementIter != null);
          Contract.Invariant(multiLatticeIter != null);
        }


        public SubelementsEnumerator(MultiLattice/*!*/ multiLattice, Elt/*!*/ multiElement) {
          Contract.Requires(multiElement != null);
          Contract.Requires(multiLattice != null);
          Contract.Requires(multiElement.elementPerLattice != null);
          this.multiLatticeIter = multiLattice.lattices.GetEnumerator();
          this.multiElementIter = multiElement.elementPerLattice.GetEnumerator();
          // base();
        }

        public DictionaryEntry Entry {
          get {
            return new DictionaryEntry(cce.NonNull(multiLatticeIter.Current), multiElementIter.Current);
          }
        }

        public object Key {
          get {
            return multiLatticeIter.Current;
          }
        }

        public object Value {
          get {
            return multiElementIter.Current;
          }
        }

        public object Current {
          get {
            return this.Entry;
          }
        }

        public bool MoveNext() {
          return multiLatticeIter.MoveNext() && multiElementIter.MoveNext();
        }

        public void Reset() {
          multiLatticeIter.Reset();
          multiElementIter.Reset();
        }
      }

      private MultiLattice/*!*/ multiLattice;
      private Elt/*!*/ multiElement;

      public SubelementsEnumerable(MultiLattice/*!*/ multiLattice, Elt/*!*/ multiElement) {
        Contract.Requires(multiElement != null);
        Contract.Requires(multiLattice != null);
        this.multiLattice = multiLattice;
        this.multiElement = multiElement;
        // base();
      }

      [Pure]
      [GlobalAccess(false)]
      [Escapes(true, false)]
      public IEnumerator/*!*/ GetEnumerator() {
        Contract.Ensures(Contract.Result<IEnumerator>() != null);
        return new SubelementsEnumerator(multiLattice, multiElement);
      }
    }


  }
}
