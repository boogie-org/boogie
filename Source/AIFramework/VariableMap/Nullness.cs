//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Diagnostics.Contracts;
namespace Microsoft.AbstractInterpretationFramework {
  using System.Collections;
  using System.Diagnostics;
  //using System.Compiler.Analysis;

  public class NullnessLattice : MicroLattice {
    readonly INullnessFactory/*!*/ factory;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(factory != null);
    }


    public NullnessLattice(INullnessFactory/*!*/ factory) {
      Contract.Requires(factory != null);
      this.factory = factory;
      // base();
    }

    enum Value {
      Bottom,
      NotNull,
      Null,
      MayBeNull
    }

    private class Elt : Element {
      public Value value;

      public Elt(Value v) {
        this.value = v;
      }

      [Pure]
      public override System.Collections.Generic.ICollection<IVariable/*!*/>/*!*/ FreeVariables() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<System.Collections.Generic.ICollection<IVariable>>()));
        return cce.NonNull(new System.Collections.Generic.List<IVariable/*!*/>()).AsReadOnly();
      }

      public override Element/*!*/ Clone() {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(this.value);
      }
    }


    public override Element/*!*/ Top {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(Value.MayBeNull);
      }
    }

    public override Element/*!*/ Bottom {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(Value.Bottom);
      }
    }

    public static Element/*!*/ Null {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(Value.Null);
      }
    }

    public static Element/*!*/ NotNull {
      get {
        Contract.Ensures(Contract.Result<Element>() != null);
        return new Elt(Value.NotNull);
      }
    }

    public override bool IsTop(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      return e.value == Value.MayBeNull;
    }

    public override bool IsBottom(Element/*!*/ element) {
      //Contract.Requires(element != null);
      Elt e = (Elt)element;
      return e.value == Value.Bottom;
    }

    public override Lattice.Element/*!*/ NontrivialJoin(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Lattice.Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;
      return (a.value == b.value) ? a : (Elt)Top;
    }

    public override Lattice.Element/*!*/ NontrivialMeet(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Lattice.Element>() != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;
      return (a.value == b.value) ? a : (Elt)Bottom;
    }

    public override Element/*!*/ Widen(Element/*!*/ first, Element/*!*/ second) {
      //Contract.Requires(second != null);
      //Contract.Requires(first != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      return Join(first, second);
    }

    protected override bool AtMost(Element/*!*/ first, Element/*!*/ second) // this <= that
    {
      //Contract.Requires(first != null);
      //Contract.Requires(second != null);
      Elt a = (Elt)first;
      Elt b = (Elt)second;
      return a.value == b.value;
    }

    public override IExpr/*!*/ ToPredicate(IVariable/*!*/ var, Element/*!*/ element) {
      //Contract.Requires(element != null);
      //Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<IExpr>() != null);
      Elt e = (Elt)element;

      if (e.value == Value.NotNull) {
        return factory.Neq(var, factory.Null);
      }
      if (e.value == Value.Null) {
        return factory.Eq(var, factory.Null);
      }
      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
      throw new System.Exception();
    }

    public override IExpr GetFoldExpr(Element/*!*/ e) {
      //Contract.Requires(e != null);
      Elt elt = (Elt)e;
      if (elt.value == Value.Null) {
        return factory.Null;
      } else {
        // can't fold into an expression
        return null;
      }
    }

    public override bool Understands(IFunctionSymbol/*!*/ f, IList/*<IExpr!>*//*!*/ args) {
      //Contract.Requires(args != null);
      //Contract.Requires(f != null);
      if (f.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq) ||
          f.Equals(Microsoft.AbstractInterpretationFramework.Value.Neq)) {

        Contract.Assert(args.Count == 2);
        IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(args[0]);
        IExpr/*!*/ arg1 = (IExpr/*!*/)cce.NonNull(args[1]);

        // Look for "x OP null" or "null OP x" where OP is "==" or "!=".
        if (arg0 is IVariable && arg1 is IFunApp && ((IFunApp)arg1).FunctionSymbol == Ref.Null) {
          return true;
        } else if (arg1 is IVariable && arg0 is IFunApp && ((IFunApp)arg0).FunctionSymbol == Ref.Null) {
          return true;
        }
      }
      return false;
    }

    public override Element/*!*/ EvaluatePredicate(IExpr/*!*/ e) {
      //Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Element>() != null);
      IFunApp nary = e as IFunApp;
      if (nary != null) {
        bool isEq = nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Eq);
        if (isEq || nary.FunctionSymbol.Equals(Microsoft.AbstractInterpretationFramework.Value.Neq)) {
          IList/*<IExpr!>*//*!*/ args = nary.Arguments;
          Contract.Assert(args != null);
          Contract.Assert(args.Count == 2);
          IExpr/*!*/ arg0 = (IExpr/*!*/)cce.NonNull(args[0]);
          IExpr/*!*/ arg1 = (IExpr/*!*/)cce.NonNull(args[1]);

          // Look for "x OP null" or "null OP x" where OP is "==" or "!=".
          IVariable var = null;
          if (arg0 is IVariable && arg1 is IFunApp && ((IFunApp)arg1).FunctionSymbol == Ref.Null) {
            var = (IVariable)arg0;
          } else if (arg1 is IVariable && arg0 is IFunApp && ((IFunApp)arg0).FunctionSymbol == Ref.Null) {
            var = (IVariable)arg1;
          }

          if (var != null) // found the pattern
                    {
            return isEq ? Null : NotNull;
          }
        }
      }
      return Top;
    }
  }

#if false

    public class NullnessMicroLattice : MicroLattice 
    {
        public override MicroLatticeElement Top { get { return NullnessLatticeElement.Top; } }
        public override MicroLatticeElement Bottom { get { return NullnessLatticeElement.Bottom; } }


        public override MicroLatticeElement EvaluateExpression (Expr e, LookupValue lookup)
        {
            if (e is LiteralExpr && ((LiteralExpr)e).Val == null)
            {
                return NullnessLatticeElement.Null;
            }
            return Top;
        }


        public override MicroLatticeElement EvaluatePredicate (Expr e, LookupValue lookup)
        {
            NAryExpr nary = e as NAryExpr;
            if (nary != null && 
                    (nary.Fun.FunctionName.Equals("==") || nary.Fun.FunctionName.Equals("!=")))
            {
                Debug.Assert(nary.Args.Length == 2);

                Expr arg0 = nary.Args[0], arg1 = nary.Args[1];
                Variable var = null;

                // Look for "x OP null" or "null OP x" where OP is "==" or "!=".
                if (arg0 is IdentifierExpr && arg1 is LiteralExpr && ((LiteralExpr)arg1).Val == null)
                {
                    var = ((IdentifierExpr)arg0).Decl;
                }
                else if (arg1 is IdentifierExpr && arg0 is LiteralExpr && ((LiteralExpr)arg0).Val == null)
                {
                    var = ((IdentifierExpr)arg1).Decl;
                }

                if (var != null) // found the pattern
                {
                    return nary.Fun.FunctionName.Equals("==") ? 
                        NullnessLatticeElement.Null : 
                        NullnessLatticeElement.NotNull;
                }
            }
            return Top;
        }
    }

#endif

}
