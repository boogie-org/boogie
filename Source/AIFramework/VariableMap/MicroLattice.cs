//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework
{
    using System.Diagnostics.Contracts;
    using System.Collections;
    using System.Diagnostics;
    //using System.Compiler;
    using Microsoft.AbstractInterpretationFramework.Collections;

    /// <summary>
    ///  Interface for a lattice that works on a per-variable basis.
    /// </summary>
    /// 
  [ContractClass(typeof(MicroLatticeContracts))]
    public abstract class MicroLattice : MathematicalLattice
    {
        /// <summary>
        ///  Returns the predicate on the given variable for the given
        ///  lattice element.
        /// </summary>
        public abstract IExpr/*!*/ ToPredicate(IVariable/*!*/ v, Element/*!*/ e);
          /* requires !e.IsBottom && !e.IsTop; */

        /// <summary>
        ///  Allows the lattice to specify whether it understands a particular function symbol.
        /// 
        ///  The lattice is always allowed to "true" even when it really can't do anything with
        ///  such functions; however, it is advantageous to say "false" when possible to avoid
        ///  being called to do certain things.
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
        /// Set this property to true if the implemented MicroLattice can handle basic arithmetic.
        /// Stated otherwise this property is set to true if the MicroLattice provides a transfer function for a predicate in a given state
        /// </summary>
        public  virtual bool UnderstandsBasicArithmetics
        {
          get { return false; }
        }

        /// <summary>
        ///  Evaluate the predicate e and a yield the lattice element
        ///  that is implied by it.
        /// </summary>
        /// <param name="e">The predicate that is assumed to contain 1 variable.</param>
        /// <returns>The most precise lattice element that is implied by the predicate.</returns>
        public abstract Element/*!*/ EvaluatePredicate(IExpr/*!*/ e);

        /// <summary>
        /// Evaluate the predicate e and yield an overapproximation of the predicate under the state that is passed as a parameter
        /// Note that unless the subclass implement it, the default behavior is to evaluate the predicate stateless, that implies that it
        /// is evaluated in any possible context, i.e. it is an upper approximation
        /// </summary>
        public virtual Element/*!*/ EvaluatePredicateWithState(IExpr/*!*/ e, IFunctionalMap state){
Contract.Requires(e != null);
Contract.Ensures(Contract.Result<Element>() != null);
          return EvaluatePredicate(e);
        }

        /// <summary>
        ///  Give an expression (often a value) that can be used to substitute for
        ///  the variable.
        /// </summary>
        /// <param name="e">A lattice element.</param>
        /// <returns>The null value if no such expression can be given.</returns>
        public abstract IExpr GetFoldExpr(Element/*!*/ e);
    }
    [ContractClassFor(typeof(MicroLattice))]
    public abstract class MicroLatticeContracts : MicroLattice {
      public override IExpr ToPredicate(IVariable v, MathematicalLattice.Element e) {
        Contract.Requires(v != null);
        Contract.Requires(e != null);
        Contract.Ensures(Contract.Result<IExpr>() != null);
        throw new System.NotImplementedException();
      }
      public override bool Understands(IFunctionSymbol f, IList args) {
        Contract.Requires(f != null);
        Contract.Requires(args != null);
        throw new System.NotImplementedException();
      }
      public override Element EvaluatePredicate(IExpr e) {
        Contract.Requires(e != null);
        Contract.Ensures(Contract.Result<Element>() != null);
        throw new System.NotImplementedException();
      }
      public override IExpr GetFoldExpr(MathematicalLattice.Element e) {
        Contract.Requires(e != null);
        throw new System.NotImplementedException();
      }
    }
}