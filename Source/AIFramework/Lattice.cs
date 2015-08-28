//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework {
  using System;
  using System.Diagnostics.Contracts;
  using System.Collections;
  using G = System.Collections.Generic;
  using System.Diagnostics;
  using Microsoft.AbstractInterpretationFramework.Collections;
  using Microsoft.Boogie;

  using ArraySet = Microsoft.Boogie.GSet<object>;
  using IMutableSet = Microsoft.Boogie.GSet<object>; 
  using HashSet = Microsoft.Boogie.GSet<object>;
  using ISet = Microsoft.Boogie.GSet<object>;
  using Set = Microsoft.Boogie.GSet<object>;


  /// <summary>
  ///  Specifies the operations (e.g., join) on a mathematical lattice that depend
  ///  only on the elements of the lattice.
  /// </summary>
  [ContractClass(typeof(MathematicalLatticeContracts))]
  public abstract class MathematicalLattice {
    #region Element
    /// <summary>
    ///  An element of the lattice.  This class should be derived from in any
    ///  implementation of MathematicalLattice.
    /// </summary>
    [ContractClass(typeof(ElementContracts))]
    public abstract class Element : System.ICloneable {
      /// <summary>
      /// Print out a debug-useful representation of the internal data structure of the lattice element.
      /// </summary>
      public virtual void Dump(string/*!*/ msg) {
        Contract.Requires(msg != null);
        System.Console.WriteLine("Dump({0}) = {1}", msg, this);
      }

      public abstract Element/*!*/ Clone();
      object/*!*/ System.ICloneable.Clone() {
        return this.Clone();
      }

      public abstract G.ICollection<IVariable/*!*/>/*!*/ FreeVariables();

    }
    [ContractClassFor(typeof(Element))]
    public abstract class ElementContracts : Element {
      public override Element Clone() {
        Contract.Ensures(Contract.Result<Element>() != null);
        throw new NotImplementedException();

      }

      public override System.Collections.Generic.ICollection<IVariable> FreeVariables() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<G.ICollection<IVariable>>()));
        Contract.Ensures(Contract.Result<System.Collections.Generic.ICollection<IVariable>>().IsReadOnly);
        throw new System.NotImplementedException();
      }
    }
    #endregion

    public abstract Element/*!*/ Top {
      get;
    }
    public abstract Element/*!*/ Bottom {
      get;
    }

    public abstract bool IsTop(Element/*!*/ e);
    public abstract bool IsBottom(Element/*!*/ e);

    /// <summary>
    /// Returns true if a &lt;= this.
    /// </summary>
    protected abstract bool AtMost(Element/*!*/ a, Element/*!*/ b);
    /* The following cases are handled elsewhere and need not be considered in subclass. */
    //  requires a.GetType() == b.GetType();
    //  requires ! a.IsTop;
    //  requires ! a.IsBottom;
    //  requires ! b.IsTop;
    //  requires ! b.IsBottom;


    protected Answer TrivialLowerThan(Element/*!*/ a, Element/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      if (a.GetType() != b.GetType()) {
        throw new System.InvalidOperationException(
          "operands to <= must be of same Element type"
          );
      }
      if (IsBottom(a)) {
        return Answer.Yes;
      }
      if (IsTop(b)) {
        return Answer.Yes;
      }
      if (IsTop(a)) {
        return Answer.No;
      }
      if (IsBottom(b)) {
        return Answer.No;
      }

      return Answer.Maybe;
    }

    // Is 'a' better information than 'b'?
    //
    public bool LowerThan(Element/*!*/ a, Element/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Answer ans = TrivialLowerThan(a, b);
      return ans != Answer.Maybe ? ans == Answer.Yes : AtMost(a, b);
    }

    // Is 'a' worse information than 'b'?
    //
    public bool HigherThan(Element/*!*/ a, Element/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      return LowerThan(b, a);
    }

    // Are 'a' and 'b' equivalent?
    //
    public bool Equivalent(Element/*!*/ a, Element/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      return LowerThan(a, b) && LowerThan(b, a);
    }

    public abstract Element/*!*/ NontrivialJoin(Element/*!*/ a, Element/*!*/ b);
    /* The following cases are handled elsewhere and need not be considered in subclass. */
    //  requires a.GetType() == b.GetType();
    //  requires ! a.IsTop;
    //  requires ! a.IsBottom;
    //  requires ! b.IsTop;
    //  requires ! b.IsBottom;


    protected Element/*?*/ TrivialJoin(Element/*!*/ a, Element/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      if (a.GetType() != b.GetType()) {
        throw new System.InvalidOperationException(
          "operands to Join must be of same Lattice.Element type"
          );
      }
      if (IsTop(a)) {
        return a;
      }
      if (IsTop(b)) {
        return b;
      }
      if (IsBottom(a)) {
        return b;
      }
      if (IsBottom(b)) {
        return a;
      }

      return null;
    }

    public Element/*!*/ Join(Element/*!*/ a, Element/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Element/*?*/ r = TrivialJoin(a, b);
      return r != null ? r : NontrivialJoin(a, b);
    }

    public abstract Element/*!*/ NontrivialMeet(Element/*!*/ a, Element/*!*/ b)
      /* The following cases are handled elsewhere and need not be considered in subclass. */
      //  requires a.GetType() == b.GetType();
      //  requires ! a.IsTop;
      //  requires ! a.IsBottom;
      //  requires ! b.IsTop;
      //  requires ! b.IsBottom;
    ;

    protected Element/*?*/ TrivialMeet(Element/*!*/ a, Element/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      if (a.GetType() != b.GetType()) {
        throw new System.InvalidOperationException(
          "operands to Meet must be of same Lattice.Element type"
          );
      }
      if (IsTop(a)) {
        return b;
      }
      if (IsTop(b)) {
        return a;
      }
      if (IsBottom(a)) {
        return a;
      }
      if (IsBottom(b)) {
        return b;
      }

      return null;
    }

    public Element/*!*/ Meet(Element/*!*/ a, Element/*!*/ b) {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Element/*?*/ r = TrivialMeet(a, b);
      return r != null ? r : NontrivialMeet(a, b);
    }

    public abstract Element/*!*/ Widen(Element/*!*/ a, Element/*!*/ b);

    public virtual void Validate() {
      Debug.Assert(IsTop(Top));
      Debug.Assert(IsBottom(Bottom));
      Debug.Assert(!IsBottom(Top));
      Debug.Assert(!IsTop(Bottom));

      Debug.Assert(LowerThan(Top, Top));
      Debug.Assert(LowerThan(Bottom, Top));
      Debug.Assert(LowerThan(Bottom, Bottom));

      Debug.Assert(IsTop(Join(Top, Top)));
      Debug.Assert(IsBottom(Join(Bottom, Bottom)));
    }
  }
  [ContractClassFor(typeof(MathematicalLattice))]
  public abstract class MathematicalLatticeContracts : MathematicalLattice {
    public override MathematicalLattice.Element Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        throw new NotImplementedException();
      }
    }

    public override MathematicalLattice.Element Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        throw new NotImplementedException();
      }
    }

    public override bool IsTop(MathematicalLattice.Element e) {
      Contract.Requires(e != null);
      throw new NotImplementedException();
    }

    public override bool IsBottom(MathematicalLattice.Element e) {
      Contract.Requires(e != null);
      throw new NotImplementedException();
    }

    protected override bool AtMost(MathematicalLattice.Element a, MathematicalLattice.Element b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      throw new NotImplementedException();
    }

    public override MathematicalLattice.Element NontrivialJoin(MathematicalLattice.Element a, MathematicalLattice.Element b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      throw new NotImplementedException();
    }

    public override MathematicalLattice.Element NontrivialMeet(MathematicalLattice.Element a, MathematicalLattice.Element b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      throw new NotImplementedException();
    }

    public override MathematicalLattice.Element Widen(MathematicalLattice.Element a, MathematicalLattice.Element b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      throw new NotImplementedException();
    }
  }


  /// <summary>
  ///  Provides an abstract interface for the operations of a lattice specific
  ///  to abstract interpretation (i.e., that deals with the expression language).
  /// </summary>
  [ContractClass(typeof(LatticeContracts))]
  public abstract class Lattice : MathematicalLattice {
    internal readonly IValueExprFactory/*!*/ valueExprFactory;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(valueExprFactory != null);
    }


    public Lattice(IValueExprFactory/*!*/ valueExprFactory) {
      Contract.Requires(valueExprFactory != null);
      this.valueExprFactory = valueExprFactory;
      // base();
    }

    #region Primitives that commands translate into

    public abstract Element/*!*/ Eliminate(Element/*!*/ e, IVariable/*!*/ variable);

    public abstract Element/*!*/ Rename(Element/*!*/ e, IVariable/*!*/ oldName, IVariable/*!*/ newName);

    public abstract Element/*!*/ Constrain(Element/*!*/ e, IExpr/*!*/ expr);

    #endregion


    //        TODO keep this?
    //        public Element! Eliminate(Element! e, VariableSeq! variables)
    //        {
    //            Lattice.Element result = e;
    //            foreach (IVariable var in variables)
    //            {
    //                result = this.Eliminate(result, var);
    //            }
    //            return result;
    //        }


    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // Note!
    // 
    // Concrete classes that implement Lattice must implement one of the AtMost
    // overloads.  We provide here a default implementation for one given a "real"
    // implementation of the other.  Otherwise, there will be an infinite loop!
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    protected override bool AtMost(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires(b != null);
      //Contract.Requires(a != null);
      return AtMost(a, IdentityCombineNameMap.Map, b, IdentityCombineNameMap.Map);
    }

    protected virtual bool AtMost(Element/*!*/ a, ICombineNameMap/*!*/ aToResult, Element/*!*/ b, ICombineNameMap/*!*/ bToResult) {
      Contract.Requires(bToResult != null);
      Contract.Requires(b != null);
      Contract.Requires(aToResult != null);
      Contract.Requires(a != null);
      return AtMost(ApplyCombineNameMap(a, aToResult), ApplyCombineNameMap(b, bToResult));
    }

    public bool LowerThan(Element/*!*/ a, ICombineNameMap/*!*/ aToResult, Element/*!*/ b, ICombineNameMap/*!*/ bToResult) {
      Contract.Requires(bToResult != null);
      Contract.Requires(b != null);
      Contract.Requires(aToResult != null);
      Contract.Requires(a != null);
      Answer ans = TrivialLowerThan(a, b);
      return ans != Answer.Maybe ? ans == Answer.Yes : AtMost(a, aToResult, b, bToResult);
    }

    public bool HigherThan(Element/*!*/ a, ICombineNameMap/*!*/ aToResult, Element/*!*/ b, ICombineNameMap/*!*/ bToResult) {
      Contract.Requires(bToResult != null);
      Contract.Requires(b != null);
      Contract.Requires(aToResult != null);
      Contract.Requires(a != null);
      return LowerThan(b, bToResult, a, aToResult);
    }


    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // Note!
    // 
    // Concrete classes that implement Lattice must implement one of the NontrivialJoin
    // overloads.  We provide here a default implementation for one given a "real"
    // implementation of the other.  Otherwise, there will be an infinite loop!
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    public override Element/*!*/ NontrivialJoin(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires(b != null);
      //Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return NontrivialJoin(a, IdentityCombineNameMap.Map, b, IdentityCombineNameMap.Map);
    }

    public virtual Element/*!*/ NontrivialJoin(Element/*!*/ a, ICombineNameMap/*!*/ aToResult, Element/*!*/ b, ICombineNameMap/*!*/ bToResult) {
      Contract.Requires(bToResult != null);
      Contract.Requires(b != null);
      Contract.Requires(aToResult != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return NontrivialJoin(ApplyCombineNameMap(a, aToResult), ApplyCombineNameMap(b, bToResult));
    }

    public Element/*!*/ Join(Element/*!*/ a, ICombineNameMap/*!*/ aToResult, Element/*!*/ b, ICombineNameMap/*!*/ bToResult) {
      Contract.Requires(bToResult != null);
      Contract.Requires(b != null);
      Contract.Requires(aToResult != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Element/*?*/ r = TrivialJoin(a, b);
      return r != null ? r : NontrivialJoin(a, aToResult, b, bToResult);
    }


    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // Note!
    // 
    // Concrete classes that implement Lattice must implement one of the Widen
    // overloads.  We provide here a default implementation for one given a "real"
    // implementation of the other.  Otherwise, there will be an infinite loop!
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    public override Element/*!*/ Widen(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires(b != null);
      //Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return Widen(a, IdentityCombineNameMap.Map, b, IdentityCombineNameMap.Map);
    }

    public virtual Element/*!*/ Widen(Element/*!*/ a, ICombineNameMap/*!*/ aToResult, Element/*!*/ b, ICombineNameMap/*!*/ bToResult) {
      Contract.Requires(bToResult != null);
      Contract.Requires(b != null);
      Contract.Requires(aToResult != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return Widen(ApplyCombineNameMap(a, aToResult), ApplyCombineNameMap(b, bToResult));
    }



    /// <summary>
    ///  A default implementation of the <see cref="CheckVariableDisequality"/> given
    ///  the appropriate expression factories by calling CheckPredicate.
    /// </summary>
    protected Answer DefaultCheckVariableDisequality(IPropExprFactory/*!*/ propExprFactory, IValueExprFactory/*!*/ valExprFactory, Element/*!*/ e, IVariable/*!*/ var1, IVariable/*!*/ var2) {
      Contract.Requires(propExprFactory != null);
      Contract.Requires(valExprFactory != null);
      Contract.Requires(e != null);
      Contract.Requires(var1 != null);
      Contract.Requires(var2 != null);
      return this.CheckPredicate(e, propExprFactory.Not(valExprFactory.Eq(var1, var2)));
    }

    private Element/*!*/ ApplyCombineNameMap(Element/*!*/ e, ICombineNameMap/*!*/ eToResult) {
      Contract.Requires(eToResult != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Element/*!*/ result = e;

      foreach (G.KeyValuePair<IVariable/*!*/, ISet/*<IVariable!>*//*!*/> entry in eToResult.GetSourceToResult()) {
        IVariable/*!*/ sourceName = entry.Key;
        Contract.Assert(sourceName != null);
        ISet/*<IVariable!*//*!*/ resultNames = entry.Value;
        Contract.Assert(resultNames != null);
        // Renaming s to r is okay if
        //       (1) s is not used in the result
        //   and (2) s has not been renamed already
        bool renameOkay = !resultNames.Contains(sourceName);
        IVariable/*!*/ representative = sourceName;
        Contract.Assert(representative != null);

        foreach (IVariable/*!*/ rname in resultNames) {
          Contract.Assert(rname != null);
          // skip if sourceName and rname are the same
          if (object.Equals(sourceName, rname)) {
            continue;
          }

          if (renameOkay) {
            result = this.Rename(result, sourceName, rname);
            representative = rname; // representative now rname
            renameOkay = false;  // no longer okay to rename
          } else {
            result = this.Constrain(result, valueExprFactory.Eq(representative, rname));
          }
        }
      }

      return result;
    }

    private sealed class IdentityCombineNameMap : ICombineNameMap {
      public static readonly IdentityCombineNameMap/*!*/ Map = new IdentityCombineNameMap();

      private static readonly G.Dictionary<IVariable/*!*/, ISet/*<IVariable!>*//*!*/>/*!*/ emptyDictionary1 = new G.Dictionary<IVariable/*!*/, ISet/*<IVariable!>*//*!*/>();
      private static readonly G.Dictionary<IVariable/*!*/, IVariable/*!*/>/*!*/ emptyDictionary2 = new G.Dictionary<IVariable/*!*/, IVariable/*!*/>();
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Map != null);
        Contract.Invariant(cce.NonNullDictionaryAndValues(emptyDictionary1) && Contract.ForAll(emptyDictionary1.Values, set =>/*cce.NonNullElements(set)*/set != null));
        Contract.Invariant(cce.NonNullDictionaryAndValues(emptyDictionary2));
        Contract.Invariant(indexMap != null);
        Contract.Invariant(reverseIndexMap != null);

      }


      public ISet/*<IVariable!>*//*?*/ GetResultNames(IVariable/*!*/ srcname) {
        //Contract.Requires(srcname != null);
        ArraySet a = new ArraySet();
        a.Add(srcname);
        return a;
      }

      public IVariable/*?*/ GetSourceName(IVariable/*!*/ resname) {
        //Contract.Requires(resname != null);
        return resname;
      }

      //TODO: uncomment when works in compiler
      //public G.IEnumerable<G.KeyValuePair<IVariable!,ISet/*<IVariable!>*/!>> GetSourceToResult()
      public IEnumerable/*!*/ GetSourceToResult() {
        Contract.Ensures(Contract.Result<IEnumerable>() != null);
        return emptyDictionary1;
      }

      //public G.IEnumerable<G.KeyValuePair<IVariable!,IVariable!>> GetResultToSource()
      public IEnumerable/*!*/ GetResultToSource() {
        Contract.Ensures(Contract.Result<IEnumerable>() != null);
        return emptyDictionary2;
      }

      private IdentityCombineNameMap() {
      }
    }

    #region Support for MultiLattice to uniquely number every subclass of Lattice


    private static Hashtable/*<System.Type,int>*//*!*/ indexMap = new Hashtable();
    private static Hashtable/*<int,Lattice>*//*!*/ reverseIndexMap = new Hashtable();
    private static int globalCount = 0;

    protected virtual object/*!*/ UniqueId {
      get {
        Contract.Ensures(Contract.Result<object>() != null);
        return cce.NonNull(this.GetType());
      }
    }

    public int Index {
      get {
        object unique = this.UniqueId;
        if (indexMap.ContainsKey(unique)) {
          object index = indexMap[unique];
          Contract.Assert(index != null); // this does nothing for nonnull analysis
          if (index != null) {
            return (int)index;
          }
          return 0;
        } else {
          int myIndex = globalCount++;
          indexMap[unique] = myIndex;
          reverseIndexMap[myIndex] = this;
          return myIndex;
        }
      }
    }

    public static Lattice GetGlobalLattice(int i) {
      return reverseIndexMap[i] as Lattice;
    }
    #endregion

    public static bool LogSwitch = false;
    /// <summary>
    ///  Returns the predicate that corresponds to the given lattice element.
    /// </summary>
    public abstract IExpr/*!*/ ToPredicate(Element/*!*/ e);

    /// <summary>
    ///  Allows the lattice to specify whether it understands a particular function symbol.
    /// 
    ///  The lattice is always allowed to return "true" even when it really can't do anything
    ///  with such functions; however, it is advantageous to say "false" when possible to
    ///  avoid being called to do certain things.
    /// 
    ///  The arguments to a function are provided for context so that the lattice can say
    ///  true or false for the same function symbol in different situations.  For example,
    ///  a lattice may understand the multiplication of a variable and a constant but not
    ///  of two variables.  The implementation of a lattice should not hold on to the
    ///  arguments.
    /// </summary>
    /// <param name="f">The function symbol.</param>
    /// <param name="args">The argument context.</param>
    /// <returns>True if it may understand f, false if it does not understand f.</returns>
    public abstract bool Understands(IFunctionSymbol/*!*/ f, IList/*<IExpr!>*//*!*/ args);

    /// <summary>
    ///  Return an expression that is equivalent to the given expression that does not
    ///  contain the given variable according to the lattice element and queryable.
    /// </summary>
    /// <param name="e">The lattice element.</param>
    /// <param name="q">A queryable for asking addtional information.</param>
    /// <param name="expr">The expression to find an equivalent expression.</param>
    /// <param name="var">The variable to eliminate.</param>
    /// <param name="prohibitedVars">The set of variables that can't be used in the resulting expression.</param>
    /// <returns>
    /// An equivalent expression to <paramref name="expr"/> without <paramref name="var"/>
    /// or null if not possible.
    /// </returns>
    public abstract IExpr/*?*/ EquivalentExpr(Element/*!*/ e, IQueryable/*!*/ q, IExpr/*!*/ expr, IVariable/*!*/ var, Set/*<IVariable!>*//*!*/ prohibitedVars);

    /// <summary>
    ///  Answers a query about whether the given predicate holds given the lattice element.
    /// </summary>
    /// <param name="e">The lattice element.</param>
    /// <param name="pred">The predicate.</param>
    /// <returns>Yes, No, or Maybe.</returns>
    public abstract Answer CheckPredicate(Element/*!*/ e, IExpr/*!*/ pred);

    /// <summary>
    ///  Answers a disequality about two variables.  The same information could be obtained
    ///  by asking CheckPredicate, but a different implementation may be simpler and more
    ///  efficient.
    /// </summary>
    /// <param name="e">The lattice element.</param>
    /// <param name="var1">The first variable.</param>
    /// <param name="var2">The second variable.</param>
    /// <returns>Yes, No, or Maybe.</returns>
    public abstract Answer CheckVariableDisequality(Element/*!*/ e, IVariable/*!*/ var1, IVariable/*!*/ var2);

    public abstract string/*!*/ ToString(Element/*!*/ e); // for debugging

  }
  [ContractClassFor(typeof(Lattice))]
  abstract class LatticeContracts : Lattice {
    public LatticeContracts()
      : base(null) {
    }
    public override IExpr ToPredicate(MathematicalLattice.Element e) {
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      throw new NotImplementedException();
    }
    public override bool Understands(IFunctionSymbol f, IList args) {
      Contract.Requires(f != null);
      Contract.Requires(args != null);
      throw new NotImplementedException();
    }
    public override IExpr EquivalentExpr(MathematicalLattice.Element e, IQueryable q, IExpr expr, IVariable var, Set prohibitedVars) {
      Contract.Requires(e != null);
      Contract.Requires(q != null);
      Contract.Requires(expr != null);
      Contract.Requires(var != null);
      Contract.Requires(prohibitedVars != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      throw new NotImplementedException();
    }
    public override Answer CheckPredicate(MathematicalLattice.Element e, IExpr pred) {
      Contract.Requires(e != null);
      Contract.Requires(pred != null);
      throw new NotImplementedException();
    }
    public override Answer CheckVariableDisequality(MathematicalLattice.Element e, IVariable var1, IVariable var2) {
      Contract.Requires(e != null);
      Contract.Requires(var1 != null);
      Contract.Requires(var2 != null);
      throw new NotImplementedException();
    }
    public override string ToString(Element e) {
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();
    }
    public override MathematicalLattice.Element Eliminate(MathematicalLattice.Element e, IVariable variable) {
      Contract.Requires(e != null);
      Contract.Requires(variable != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      throw new NotImplementedException();
    }
    public override MathematicalLattice.Element Rename(MathematicalLattice.Element e, IVariable oldName, IVariable newName) {
      Contract.Requires(e != null);
      Contract.Requires(oldName != null);
      Contract.Requires(newName != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      throw new NotImplementedException();
    }
    public override MathematicalLattice.Element Constrain(MathematicalLattice.Element e, IExpr expr) {
      Contract.Requires(e != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      throw new NotImplementedException();
    }
  }

  /// <summary>
  ///   Defines the relation between names used in the respective input lattice elements to the
  ///   various combination operators (Join,Widen,Meet,AtMost) and the names that should be used
  ///   in the resulting lattice element.
  /// </summary>
  [ContractClass(typeof(ICombineNameMapContracts))]
  public interface ICombineNameMap {
    ISet/*<IVariable!>*//*?*/ GetResultNames(IVariable/*!*/ srcname);
    IVariable/*?*/ GetSourceName(IVariable/*!*/ resname);

    //TODO: uncommet when works in compiler
    //G.IEnumerable<G.KeyValuePair<IVariable!,ISet/*<IVariable!>*/!>> GetSourceToResult();
    IEnumerable/*!*/ GetSourceToResult();
    //G.IEnumerable<G.KeyValuePair<IVariable!,IVariable!>> GetResultToSource();
    IEnumerable/*!*/ GetResultToSource();
  }
  [ContractClassFor(typeof(ICombineNameMap))]
  public abstract class ICombineNameMapContracts : ICombineNameMap {
    #region ICombineNameMap Members

    public Set GetResultNames(IVariable srcname) {
      Contract.Requires(srcname != null);
      throw new NotImplementedException();
    }

    public IVariable GetSourceName(IVariable resname) {
      Contract.Requires(resname != null);
      throw new NotImplementedException();
    }

    public IEnumerable GetSourceToResult() {
      Contract.Ensures(Contract.Result<IEnumerable>() != null);
      throw new NotImplementedException();
    }

    public IEnumerable GetResultToSource() {
      Contract.Ensures(Contract.Result<IEnumerable>() != null);
      throw new NotImplementedException();
    }

    #endregion
  }

  /// <summary>
  ///   Provides statistics on the number of times an operation is performed
  ///   and forwards the real operations to the given lattice in the constructor.
  /// </summary>
  public class StatisticsLattice : Lattice {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(lattice != null);
    }

    readonly Lattice/*!*/ lattice;
    int eliminateCount;
    int renameCount;
    int constrainCount;
    int toPredicateCount;
    int atMostCount;
    int topCount;
    int bottomCount;
    int isTopCount;
    int isBottomCount;
    int joinCount;
    int meetCount;
    int widenCount;
    int understandsCount;
    int equivalentExprCount;
    int checkPredicateCount;
    int checkVariableDisequalityCount;

    public StatisticsLattice(Lattice/*!*/ lattice)
      : base(lattice.valueExprFactory) {
      Contract.Requires(lattice != null);
      this.lattice = lattice;
      // base(lattice.valueExprFactory);
    }

    public override Element/*!*/ Eliminate(Element/*!*/ e, IVariable/*!*/ variable) {
      //Contract.Requires(variable != null);
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      eliminateCount++;
      return lattice.Eliminate(e, variable);
    }

    public override Element/*!*/ Rename(Element/*!*/ e, IVariable/*!*/ oldName, IVariable/*!*/ newName) {
      //Contract.Requires(newName != null);
      //Contract.Requires(oldName != null);
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      renameCount++;
      return lattice.Rename(e, oldName, newName);
    }

    public override Element/*!*/ Constrain(Element/*!*/ e, IExpr/*!*/ expr) {
      //Contract.Requires(expr != null);
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      constrainCount++;
      return lattice.Constrain(e, expr);
    }


    public override bool Understands(IFunctionSymbol/*!*/ f, IList/*!*/ args) {
      //Contract.Requires(args != null);
      //Contract.Requires(f != null);
      understandsCount++;
      return lattice.Understands(f, args);
    }


    public override IExpr/*?*/ EquivalentExpr(Element/*!*/ e, IQueryable/*!*/ q, IExpr/*!*/ expr, IVariable/*!*/ var, ISet/*<IVariable!>*//*!*/ prohibitedVars) {
      //Contract.Requires(prohibitedVars != null);
      //Contract.Requires(var != null);
      //Contract.Requires(expr != null);
      //Contract.Requires(q != null);
      //Contract.Requires(e != null);
      equivalentExprCount++;
      return lattice.EquivalentExpr(e, q, expr, var, prohibitedVars);
    }


    public override Answer CheckPredicate(Element/*!*/ e, IExpr/*!*/ pred) {
      //Contract.Requires(pred != null);
      //Contract.Requires(e != null);
      checkPredicateCount++;
      return lattice.CheckPredicate(e, pred);
    }


    public override Answer CheckVariableDisequality(Element/*!*/ e, IVariable/*!*/ var1, IVariable/*!*/ var2) {
      //Contract.Requires(var2 != null);
      //Contract.Requires(var1 != null);
      //Contract.Requires(e != null);
      checkVariableDisequalityCount++;
      return lattice.CheckVariableDisequality(e, var1, var2);
    }



    public override IExpr/*!*/ ToPredicate(Element/*!*/ e) {
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      toPredicateCount++;
      return lattice.ToPredicate(e);
    }

    public override string/*!*/ ToString(Element/*!*/ e) {
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<string>() != null);
      return lattice.ToString(e);
    }

    [Pure]
    public override string/*!*/ ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return string.Format(
        "StatisticsLattice: #Eliminate={0} #Rename={1} #Constrain={2} #ToPredicate={3} " +
        "#Understands={4} #EquivalentExpr={5} #CheckPredicate={6} #CheckVariableDisequality={7} " +
        "#AtMost={8} #Top={9} #Bottom={9} #IsTop={10} #IsBottom={11} " +
        "#NonTrivialJoin={12} #NonTrivialMeet={13} #Widen={14}",
        eliminateCount, renameCount, constrainCount, toPredicateCount,
        understandsCount, equivalentExprCount, checkPredicateCount, checkVariableDisequalityCount,
        atMostCount, topCount, bottomCount, isTopCount, isBottomCount,
        joinCount, meetCount, widenCount);
    }

    protected override bool AtMost(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires(b != null);
      //Contract.Requires(a != null);
      atMostCount++;
      return lattice.LowerThan(a, b);
    }

    public override Element/*!*/ Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        topCount++;
        return lattice.Top;
      }
    }
    public override Element/*!*/ Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        bottomCount++;
        return lattice.Bottom;
      }
    }

    public override bool IsTop(Element/*!*/ e) {
      //Contract.Requires(e != null);
      isTopCount++;
      return lattice.IsTop(e);
    }

    public override bool IsBottom(Element/*!*/ e) {
      //Contract.Requires(e != null);
      isBottomCount++;
      return lattice.IsBottom(e);
    }

    public override Element/*!*/ NontrivialJoin(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires(b != null);
      //Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      joinCount++;
      return lattice.NontrivialJoin(a, b);
    }

    public override Element/*!*/ NontrivialMeet(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires(b != null);
      //Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      meetCount++;
      return lattice.NontrivialMeet(a, b);
    }

    public override Element/*!*/ Widen(Element/*!*/ a, Element/*!*/ b) {
      //Contract.Requires(b != null);
      //Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      widenCount++;
      return lattice.Widen(a, b);
    }

    public override void Validate() {
      base.Validate();
      lattice.Validate();
    }

    protected override object/*!*/ UniqueId {
      get {
        Contract.Ensures(Contract.Result<object>() != null);
        // use the base id, not the underlying-lattice id (is that the right thing to do?)
        return base.UniqueId;
      }
    }
  }


  public sealed class LatticeQueryable : IQueryable {
    private Lattice/*!*/ lattice;
    private Lattice.Element/*!*/ element;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(lattice != null);
      Contract.Invariant(element != null);
    }


    public LatticeQueryable(Lattice/*!*/ lattice, Lattice.Element/*!*/ element) {
      Contract.Requires(element != null);
      Contract.Requires(lattice != null);
      this.lattice = lattice;
      this.element = element;
      // base();
    }

    public Answer CheckPredicate(IExpr/*!*/ pred) {
      //Contract.Requires(pred != null);
      return lattice.CheckPredicate(element, pred);
    }

    public Answer CheckVariableDisequality(IVariable/*!*/ var1, IVariable/*!*/ var2) {
      //Contract.Requires(var2 != null);
      //Contract.Requires(var1 != null);
      return lattice.CheckVariableDisequality(element, var1, var2);
    }
  }
}
