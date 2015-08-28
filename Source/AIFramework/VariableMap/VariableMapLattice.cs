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

  using Microsoft.AbstractInterpretationFramework;
  using Microsoft.AbstractInterpretationFramework.Collections;

  using Microsoft.Boogie;

  using IMutableSet = Microsoft.Boogie.GSet<object>;
  using ISet = Microsoft.Boogie.GSet<object>;
  using Set = Microsoft.Boogie.GSet<object>;
  using HashSet = Microsoft.Boogie.GSet<object>;

  /// <summary>
  ///  Creates a lattice that works for several variables given a MicroLattice.  Assumes
  ///  if one variable is bottom, then all variables are bottom.
  /// </summary>
  public class VariableMapLattice : Lattice {
    private class Elt : Element {
      /// <summary>
      /// IsBottom(e)  iff  e.constraints == null
      /// </summary>
      /*MayBeNull*/
      private IFunctionalMap constraints;  // of type IVariable -> LATTICE_ELEMENT
      public IFunctionalMap Constraints {
        get {
          return this.constraints;
        }
      }

      private Elt(bool top) {
        if (top) {
          this.constraints = FunctionalHashtable.Empty;
        } else {
          this.constraints = null;
        }
      }

      public override Element/*!*/ Clone() {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(this.constraints);
      }

      [Pure]
      public override string/*!*/ ToString() {
        Contract.Ensures(Contract.Result<string>() != null);
        if (constraints == null) {
          return "<bottom>";
        }
        string s = "[";
        string sep = "";
        foreach (IVariable/*!*/ v in cce.NonNull(constraints.Keys)) {
          Contract.Assert(v != null);
          Element m = (Element)constraints[v];
          s += sep + v.Name + " -> " + m;
          sep = ", ";
        }
        return s + "]";
      }

      public static readonly Elt/*!*/ Top = new Elt(true);
      public static readonly Elt/*!*/ Bottom = new Elt(false);


      public Elt(IFunctionalMap constraints) {
        this.constraints = constraints;
      }

      public bool IsBottom {
        get {
          return this.constraints == null;
        }
      }

      public int Count {
        get {
          return this.constraints == null ? 0 : this.constraints.Count;
        }
      }

      public IEnumerable/*<IVariable>*//*!*/ Variables {
        get {
          Contract.Requires(!this.IsBottom);
          Contract.Ensures(Contract.Result<IEnumerable>() != null);
          Contract.Assume(this.constraints != null);
          return cce.NonNull(this.constraints.Keys);
        }
      }

      public IEnumerable/*<IVariable>*//*!*/ SortedVariables(/*maybe null*/ IComparer variableComparer) {
        Contract.Ensures(Contract.Result<IEnumerable>() != null);
        if (variableComparer == null) {
          return Variables;
        } else {
          ArrayList /*IVariable*/ vars = new ArrayList /*IVariable*/ (Count);
          foreach (IVariable variable in Variables) {
            vars.Add(variable);
          }
          vars.Sort(variableComparer);
          return vars;
        }
      }

      public Element Lookup(IVariable v) {
        if ((v == null) || (this.constraints == null)) {
          return null;
        }
        return (Element)this.constraints[v];
      }

      public Element this[IVariable/*!*/ key] {
        get {
          Contract.Requires(!this.IsBottom);
          Contract.Requires(key != null);
          Contract.Assume(this.constraints != null);
          return (Element)constraints[key];
        }
      }

      /// <summary>
      /// Add a new entry in the functional map: var --> value.
      /// If the variable is already there, throws an exception
      /// </summary>
      public Elt/*!*/ Add(IVariable/*!*/ var, Element/*!*/ value, MicroLattice/*!*/ microLattice) {
        Contract.Requires(microLattice != null);
        Contract.Requires(value != null);
        Contract.Requires(var != null);
        Contract.Requires((!this.IsBottom));
        Contract.Ensures(Contract.Result<Elt>() != null);
        Contract.Assume(this.constraints != null);
        Contract.Assert(!this.constraints.Contains(var));

        if (microLattice.IsBottom(value)) {
          return Bottom;
        }
        if (microLattice.IsTop(value)) {
          return this.Remove(var, microLattice);
        }

        return new Elt(this.constraints.Add(var, value));
      }

      /// <summary>
      /// Set the value of the variable in the functional map
      /// If the variable is not already there, throws an exception
      /// </summary>
      public Elt/*!*/ Set(IVariable/*!*/ var, Element/*!*/ value, MicroLattice/*!*/ microLattice) {
        Contract.Requires(microLattice != null);
        Contract.Requires(value != null);
        Contract.Requires(var != null);
        Contract.Ensures(Contract.Result<Elt>() != null);
        if (microLattice.IsBottom(value)) {
          return Bottom;
        }
        if (microLattice.IsTop(value)) {
          return this.Remove(var, microLattice);
        }

        Contract.Assume(this.constraints != null);
        Contract.Assert(this.constraints.Contains(var));

        // this.constraints[var] = value;
        IFunctionalMap newMap = this.constraints.Set(var, value);

        return new Elt(newMap);
      }

      public Elt/*!*/ Remove(IVariable/*!*/ var, MicroLattice microLattice) {
        Contract.Requires(var != null);
        Contract.Ensures(Contract.Result<Elt>() != null);
        if (this.IsBottom) {
          return this;
        }
        Contract.Assume(this.constraints != null);
        return new Elt(this.constraints.Remove(var));
      }

      public Elt/*!*/ Rename(IVariable/*!*/ oldName, IVariable/*!*/ newName, MicroLattice/*!*/ microLattice) {
        Contract.Requires(microLattice != null);
        Contract.Requires(newName != null);
        Contract.Requires(oldName != null);
        Contract.Requires((!this.IsBottom));
        Contract.Ensures(Contract.Result<Elt>() != null);
        Element value = this[oldName];
        if (value == null) {
          return this;
        } // 'oldName' isn't in the map, so neither will be 'newName'
        Contract.Assume(this.constraints != null);
        IFunctionalMap newMap = this.constraints.Remove(oldName);
        newMap = newMap.Add(newName, value);
        return new Elt(newMap);
      }

      [Pure]
      public override ICollection<IVariable/*!*/>/*!*/ FreeVariables() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<ICollection<IVariable>>()));
        throw new System.NotImplementedException();
      }

    } // class

    private readonly MicroLattice/*!*/ microLattice;

    private readonly IPropExprFactory/*!*/ propExprFactory;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(microLattice != null);
      Contract.Invariant(propExprFactory != null);
    }


    private readonly /*maybe null*/IComparer variableComparer;

    public VariableMapLattice(IPropExprFactory/*!*/ propExprFactory, IValueExprFactory/*!*/ valueExprFactory, MicroLattice/*!*/ microLattice, /*maybe null*/IComparer variableComparer)
      : base(valueExprFactory) {
      Contract.Requires(microLattice != null);
      Contract.Requires(valueExprFactory != null);
      Contract.Requires(propExprFactory != null);
      this.propExprFactory = propExprFactory;
      this.microLattice = microLattice;
      this.variableComparer = variableComparer;
      // base(valueExprFactory);
    }

    protected override object/*!*/ UniqueId {
      get {
        Contract.Ensures(Contract.Result<object>() != null);
        return this.microLattice.GetType();
      }
    }

    public override Element/*!*/ Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return Elt.Top;
      }
    }

    public override Element Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return Elt.Bottom;
      }
    }

    public override bool IsTop(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      return !e.IsBottom && e.Count == 0;
    }

    public override bool IsBottom(Element/*!*/ element) {
      //Contract.Requires(element != null);
      return ((Elt)element).IsBottom;
    }

    protected override bool AtMost(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;

      // return true iff every constraint in "this" is no weaker than the corresponding
      // constraint in "that" and there are no additional constraints in "that"
      foreach (IVariable/*!*/ var in a.Variables) {
        Contract.Assert(var != null);
        Element thisValue = cce.NonNull(a[var]);

        Element thatValue = b[var];
        if (thatValue == null) {
          continue;
        } // it's okay for "a" to know something "b" doesn't

        if (this.microLattice.LowerThan(thisValue, thatValue)) {
          continue;
        } // constraint for "var" satisfies AtMost relation

        return false;
      }
      foreach (IVariable/*!*/ var in b.Variables) {
        Contract.Assert(var != null);
        if (a.Lookup(var) != null) {
          continue;
        } // we checked this case in the loop above

        Element thatValue = cce.NonNull(b[var]);
        if (this.microLattice.IsTop(thatValue)) {
          continue;
        } // this is a trivial constraint

        return false;
      }
      return true;
    }

    private Elt/*!*/ AddConstraint(Element/*!*/ element, IVariable/*!*/ var, /*MicroLattice*/Element/*!*/ newValue) {
      Contract.Requires((newValue != null));
      Contract.Requires((var != null));
      Contract.Requires((element != null));
      Contract.Ensures(Contract.Result<Elt>() != null);
      Elt e = (Elt)element;

      if (!e.IsBottom && !this.microLattice.IsBottom(newValue)) // if we're not at bottom
            {
        /*MicroLattice*/
        Element currentValue = e[var];

        if (currentValue == null) {
          // No information currently, so we just add the new info.
          return e.Add(var, newValue, this.microLattice);
        } else {
          // Otherwise, take the meet of the new and current info.
          //return e.Add(var, this.microLattice.Meet(currentValue, newValue), this.microLattice);
          return e.Set(var, this.microLattice.Meet(currentValue, newValue), this.microLattice);
        }
      }
      return e;
    }

    public override string/*!*/ ToString(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<string>() != null);
      Elt e = (Elt)element;

      if (IsTop(e)) {
        return "<top>";
      }
      if (IsBottom(e)) {
        return "<bottom>";
      }

      int k = 0;
      System.Text.StringBuilder buffer = new System.Text.StringBuilder();
      foreach (IVariable/*!*/ key in e.SortedVariables(variableComparer)) {
        Contract.Assert(key != null);
        if (k++ > 0) {
          buffer.Append("; ");
        }
        buffer.AppendFormat("{0} = {1}", key, e[key]);
      }
      return buffer.ToString();
    }

    public override Element/*!*/ NontrivialJoin(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;

      IFunctionalMap newMap = FunctionalHashtable.Empty;
      foreach (IVariable/*!*/ key in a.Variables) {
        Contract.Assert(key != null);
        Element aValue = a[key];
        Element bValue = b[key];

        if (aValue != null && bValue != null) {
          // Keep only the variables known to both elements.
          Element newValue = this.microLattice.Join(aValue, bValue);
          newMap = newMap.Add(key, newValue);
        }
      }
      Elt/*!*/ join = new Elt(newMap);
      Contract.Assert(join != null);

      // System.Console.WriteLine("{0} join {1} = {2} ", this.ToString(a), ToString(b), ToString(join));

      return join;
    }

    public override Element/*!*/ NontrivialMeet(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;

      IFunctionalMap newMap = FunctionalHashtable.Empty;
      foreach (IVariable/*!*/ key in a.Variables) {
        Contract.Assert(key != null);
        Element/*!*/ aValue = cce.NonNull(a[key]);
        Element bValue = b[key];

        Element newValue =
          bValue == null ? aValue :
          this.microLattice.Meet(aValue, bValue);

        newMap = newMap.Add(key, newValue);
      }
      foreach (IVariable/*!*/ key in b.Variables) {
        Contract.Assert(key != null);
        Element aValue = a[key];
        Element bValue = b[key];
        Debug.Assert(bValue != null);

        if (aValue == null) {
          // It's a variable we didn't cover in the last loop.
          newMap = newMap.Add(key, bValue);
        }
      }
      return new Elt(newMap);
    }

    /// <summary>
    /// Perform the pointwise widening of the elements in the map
    /// </summary>
    public override Element/*!*/ Widen(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires((second != null));
      //Contract.Requires((first != null));
      Contract.Ensures(Contract.Result<Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;

      // Note we have to add those cases as we do not have a "NonTrivialWiden" method
      if (a.IsBottom)
        return new Elt(b.Constraints);
      if (b.IsBottom)
        return new Elt(a.Constraints);

      IFunctionalMap newMap = FunctionalHashtable.Empty;
      foreach (IVariable/*!*/ key in a.Variables) {
        Contract.Assert(key != null);
        Element aValue = a[key];
        Element bValue = b[key];

        if (aValue != null && bValue != null) {
          // Keep only the variables known to both elements.
          Element newValue = this.microLattice.Widen(aValue, bValue);
          newMap = newMap.Add(key, newValue);
        }
      }
      Element/*!*/ widen = new Elt(newMap);
      Contract.Assert(widen != null);
      // System.Console.WriteLine("{0} widen {1} = {2} ", this.ToString(a), ToString(b), ToString(widen));

      return widen;
    }

    internal static ISet/*<IVariable!>*//*!*/ VariablesInExpression(IExpr/*!*/ e, ISet/*<IVariable!>*//*!*/ ignoreVars) {
      Contract.Requires(ignoreVars != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<ISet>() != null);
      HashSet s = new HashSet();

      IFunApp f = e as IFunApp;
      IFunction lambda = e as IFunction;

      if (e is IVariable) {
        if (!ignoreVars.Contains(e))
          s.Add(e);
      } else if (f != null) // e is IFunApp
            {
        foreach (IExpr/*!*/ arg in f.Arguments) {
          Contract.Assert(arg != null);
          s.AddAll(VariablesInExpression(arg, ignoreVars));
        }
      } else if (lambda != null) {
        IMutableSet x = new HashSet(1);
        x.Add(lambda.Param);

        // Ignore the bound variable
        s.AddAll(VariablesInExpression(lambda.Body, cce.NonNull(Set.Union(ignoreVars, x))));
      } else if (e is IUnknown) {
        // skip (actually, it would be appropriate to return the universal set of all variables)
      } else {
        Debug.Assert(false, "case not handled: " + e);
      }
      return s;
    }


    private static ArrayList/*<IExpr>*//*!*/ FindConjuncts(IExpr e) {
      Contract.Ensures(Contract.Result<ArrayList>() != null);
      ArrayList result = new ArrayList();

      IFunApp f = e as IFunApp;
      if (f != null) {
        if (f.FunctionSymbol.Equals(Prop.And)) {
          foreach (IExpr arg in f.Arguments) {
            result.AddRange(FindConjuncts(arg));
          }
        } else if (f.FunctionSymbol.Equals(Prop.Or)
                 || f.FunctionSymbol.Equals(Prop.Implies)) {
          // Do nothing.
        } else {
          result.Add(e);
        }
      } else {
        result.Add(e);
      }

      return result;
    }

    private static bool IsSimpleEquality(IExpr expr, out IVariable left, out IVariable right) {
      Contract.Ensures(!Contract.Result<bool>() || Contract.ValueAtReturn(out left) != null && Contract.ValueAtReturn(out right) != null);
      left = null;
      right = null;

      // See if we have an equality
      IFunApp nary = expr as IFunApp;
      if (nary == null || !nary.FunctionSymbol.Equals(Value.Eq)) {
        return false;
      }

      // See if it is an equality of two variables
      IVariable idLeft = nary.Arguments[0] as IVariable;
      IVariable idRight = nary.Arguments[1] as IVariable;
      if (idLeft == null || idRight == null) {
        return false;
      }

      left = idLeft;
      right = idRight;
      return true;
    }

    /// <summary>
    /// Returns true iff the expression is in the form var == arithmeticExpr
    /// </summary>
    private static bool IsArithmeticExpr(IExpr/*!*/ expr) {
      Contract.Requires(expr != null);
      // System.Console.WriteLine("\t\tIsArithmetic called with {0} of type {1}", expr, expr.GetType().ToString());

      if (expr is IVariable)   // expr is a variable
        return true;
      else if (expr is IFunApp)     // may be ==, +, -, /, % or an integer
        {
        IFunApp fun = (IFunApp)expr;

        if (fun.FunctionSymbol is IntSymbol)     // it is an integer
          return true;
        else if (fun.FunctionSymbol.Equals(Int.Negate))  // it is an unary minus
          return IsArithmeticExpr((IExpr/*!*/)cce.NonNull(fun.Arguments[0]));
        else if (fun.Arguments.Count != 2)       // A function of two or more operands is not arithmetic
          return false;
        else {
          IExpr/*!*/ left = (IExpr/*!*/)cce.NonNull(fun.Arguments[0]);
          IExpr/*!*/ right = (IExpr/*!*/)cce.NonNull(fun.Arguments[1]);

          if (!(left is IVariable || right is IVariable))    // At least one of the two operands must be a variable
            return false;

          if (fun.FunctionSymbol.Equals(Value.Eq)
              || fun.FunctionSymbol.Equals(Int.Add)
              || fun.FunctionSymbol.Equals(Int.Sub)
              || fun.FunctionSymbol.Equals(Int.Mul)
              || fun.FunctionSymbol.Equals(Int.Div)
              || fun.FunctionSymbol.Equals(Int.Mod))
            return IsArithmeticExpr(left) && IsArithmeticExpr(right);
          else
            return false;
        }
      } else {
        return false;
      }
    }

    public override IExpr/*!*/ ToPredicate(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      if (IsTop(element)) {
        return propExprFactory.True;
      }
      if (IsBottom(element)) {
        return propExprFactory.False;
      }

      Elt e = (Elt)element;
      IExpr truth = propExprFactory.True;
      IExpr result = truth;

      foreach (IVariable/*!*/ variable in e.SortedVariables(variableComparer)) {
        Contract.Assert(variable != null);
        Element value = (Element)e[variable];

        if (value == null || this.microLattice.IsTop(value)) {
          continue;
        } // Skip variables about which we know nothing.
        if (this.microLattice.IsBottom(value)) {
          return propExprFactory.False;
        }

        IExpr conjunct = this.microLattice.ToPredicate(variable, value);

        result = (result == truth) ? (IExpr)conjunct : (IExpr)propExprFactory.And(result, conjunct);
      }
      return result;
    }


    public override Element/*!*/ Eliminate(Element/*!*/ element, IVariable/*!*/ variable) {
      //Contract.Requires(variable != null);
      //Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return cce.NonNull((Elt)element).Remove(variable, this.microLattice);
    }

    private delegate IExpr/*!*/ OnUnableToInline(IVariable/*!*/ var);
    private IExpr/*!*/ IdentityVarToExpr(IVariable/*!*/ var) {
      //Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      return var;
    }

    /// <summary>
    /// Return a new expression in which each variable has been 
    /// replaced by an expression representing what is known about
    /// that variable.
    /// </summary>
    private IExpr/*!*/ InlineVariables(Elt/*!*/ element, IExpr/*!*/ expr, ISet/*<IVariable!>*//*!*/ notInlineable,
        OnUnableToInline/*!*/ unableToInline) {
      Contract.Requires(unableToInline != null);
      Contract.Requires(notInlineable != null);
      Contract.Requires(expr != null);
      Contract.Requires(element != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      IVariable var = expr as IVariable;
      if (var != null) {
        /*MicroLattice*/
        Element value = element[var];
        if (notInlineable.Contains(var) || value == null || this.microLattice.IsTop(value)) {
          return unableToInline(var); // We don't know anything about this variable.
        } else {
          // GetFoldExpr returns null when it can yield an expression that
          // can be substituted for the variable.
          IExpr valueExpr = this.microLattice.GetFoldExpr(value);
          return (valueExpr == null) ? var : valueExpr;
        }
      }

      // else

      IFunApp fun = expr as IFunApp;
      if (fun != null) {
        IList newargs = new ArrayList();
        foreach (IExpr/*!*/ arg in fun.Arguments) {
          Contract.Assert(arg != null);
          newargs.Add(InlineVariables(element, arg, notInlineable, unableToInline));
        }
        return fun.CloneWithArguments(newargs);
      }

      // else

      IFunction lambda = expr as IFunction;
      if (lambda != null) {
        IMutableSet x = new HashSet(1);
        x.Add(lambda.Param);

        // Don't inline the bound variable
        return lambda.CloneWithBody(
                   InlineVariables(element, lambda.Body,
                                    cce.NonNull(Set.Union(notInlineable, x)), unableToInline)
               );
      }

      // else

      if (expr is IUnknown) {
        return expr;
      } else {
        throw
          new System.NotImplementedException("cannot inline identifies in expression " + expr);
      }
    }


    public override Element/*!*/ Constrain(Element/*!*/ element, IExpr/*!*/ expr) {
      //Contract.Requires(expr != null);
      //Contract.Requires(element != null);
      //Contract.Ensures(Contract.Result<Element>() != null);
      Elt/*!*/ result = (Elt)element;
      Contract.Assert(result != null);

      if (IsBottom(element)) {
        return result; // == element 
      }

      expr = InlineVariables(result, expr, cce.NonNull(Set.Empty), new OnUnableToInline(IdentityVarToExpr));

      foreach (IExpr/*!*/ conjunct in FindConjuncts(expr)) {
        Contract.Assert(conjunct != null);
        IVariable left, right;

        if (IsSimpleEquality(conjunct, out left, out right)) {
          #region The conjunct is a simple equality


          Contract.Assert(left != null && right != null);

          Element leftValue = result[left], rightValue = result[right];
          if (leftValue == null) {
            leftValue = this.microLattice.Top;
          }
          if (rightValue == null) {
            rightValue = this.microLattice.Top;
          }
          Element newValue = this.microLattice.Meet(leftValue, rightValue);
          result = AddConstraint(result, left, newValue);
          result = AddConstraint(result, right, newValue);

          #endregion
        } else {
          ISet/*<IVariable>*/ variablesInvolved = VariablesInExpression(conjunct, Set.Empty);

          if (variablesInvolved.Count == 1) {
            #region We have just one variable

            IVariable var = null;
            foreach (IVariable/*!*/ v in variablesInvolved) {
              Contract.Assert(v != null);
              var = v;
            } // why is there no better way to get the elements?
            Contract.Assert(var != null);
            Element/*!*/ value = this.microLattice.EvaluatePredicate(conjunct);
            result = AddConstraint(result, var, value);

            #endregion
          } else if (IsArithmeticExpr(conjunct) && this.microLattice.UnderstandsBasicArithmetics) {
            #region We evalaute an arithmetic expression

            IFunApp fun = (IFunApp)conjunct;
            if (fun.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq)) // if it is a symbol of equality
                       {
              // get the variable to be assigned
              IExpr/*!*/ leftArg = (IExpr/*!*/)cce.NonNull(fun.Arguments[0]);
              IExpr/*!*/ rightArg = (IExpr/*!*/)cce.NonNull(fun.Arguments[1]);
              IExpr/*!*/ var = (leftArg is IVariable) ? leftArg : rightArg;

              Element/*!*/ value = this.microLattice.EvaluatePredicateWithState(conjunct, result.Constraints);
              Contract.Assert(value != null);
              result = AddConstraint(result, (IVariable/*!*/)cce.NonNull(var), value);
            }
            #endregion
          }
        }
      }
      return result;
    }


    public override Element/*!*/ Rename(Element/*!*/ element, IVariable/*!*/ oldName, IVariable/*!*/ newName) {
      //Contract.Requires(newName != null);
      //Contract.Requires(oldName != null);
      //Contract.Requires(element != null);
      //Contract.Ensures(Contract.Result<Element>() != null);
      if (IsBottom(element)) {
        return element;
      } else {
        return ((Elt)element).Rename(oldName, newName, this.microLattice);
      }
    }


    public override bool Understands(IFunctionSymbol/*!*/ f, IList/*!*/ args) {
      //Contract.Requires(args != null);
      //Contract.Requires(f != null);
      return f.Equals(Prop.And) ||
             f.Equals(Value.Eq) ||
             microLattice.Understands(f, args);
    }

    private sealed class EquivalentExprException : CheckedException {
    }
    private sealed class EquivalentExprInlineCallback {
      private readonly IVariable/*!*/ var;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(var != null);
      }

      public EquivalentExprInlineCallback(IVariable/*!*/ var) {
        Contract.Requires(var != null);
        this.var = var;
        // base();
      }

      public IExpr/*!*/ ThrowOnUnableToInline(IVariable/*!*/ othervar)
        //throws EquivalentExprException;
      {
        Contract.Requires(othervar != null);
        Contract.Ensures(Contract.Result<IExpr>() != null);
        Contract.EnsuresOnThrow<EquivalentExprException>(true);
        if (othervar.Equals(var))
          throw new EquivalentExprException();
        else
          return othervar;
      }
    }

    public override IExpr/*?*/ EquivalentExpr(Element/*!*/ e, IQueryable/*!*/ q, IExpr/*!*/ expr, IVariable/*!*/ var, ISet/*<IVariable!>*//*!*/ prohibitedVars) {
      //Contract.Requires(prohibitedVars != null);
      //Contract.Requires(var != null);
      //Contract.Requires(expr != null);
      //Contract.Requires(q != null);
      //Contract.Requires(e != null);
      try {
        EquivalentExprInlineCallback closure = new EquivalentExprInlineCallback(var);
        return InlineVariables((Elt)e, expr, cce.NonNull(Set.Empty),
                               new OnUnableToInline(closure.ThrowOnUnableToInline));
      } catch (EquivalentExprException) {
        return null;
      }
    }


    /// <summary>
    /// Check to see if the given predicate holds in the given lattice element.
    /// 
    /// TODO:  We leave this unimplemented for now and just return maybe.
    /// </summary>
    /// <param name="e">The lattice element.</param>
    /// <param name="pred">The predicate.</param>
    /// <returns>Yes, No, or Maybe</returns>
    public override Answer CheckPredicate(Element/*!*/ e, IExpr/*!*/ pred) {
      //Contract.Requires(pred != null);
      //Contract.Requires(e != null);
      return Answer.Maybe;
    }

    /// <summary>
    ///  Answers a disequality about two variables.  The same information could be obtained
    ///  by asking CheckPredicate, but a different implementation may be simpler and more
    ///  efficient.
    /// 
    ///  TODO: We leave this unimplemented for now and just return maybe.
    /// </summary>
    /// <param name="e">The lattice element.</param>
    /// <param name="var1">The first variable.</param>
    /// <param name="var2">The second variable.</param>
    /// <returns>Yes, No, or Maybe.</returns>
    public override Answer CheckVariableDisequality(Element/*!*/ e, IVariable/*!*/ var1, IVariable/*!*/ var2) {
      //Contract.Requires(var2 != null);
      //Contract.Requires(var1 != null);
      //Contract.Requires(e != null);
      return Answer.Maybe;
    }

    public override void Validate() {
      base.Validate();
      microLattice.Validate();
    }

  }
}
