//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using Microsoft.Boogie;
using AI = Microsoft.AbstractInterpretationFramework;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;

namespace Microsoft.Boogie.AbstractInterpretation {

  public class BoogiePropFactory : BoogieFactory, AI.IQuantPropExprFactory {
    public AI.IFunApp False {
      get {
        Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

        return Expr.False;
      }
    }
    public AI.IFunApp True {
      get {
        Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

        return Expr.True;
      }
    }

    public AI.IFunApp Not(AI.IExpr p) {
      //Contract.Requires(p != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      return Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, IExpr2Expr(p));
    }

    public AI.IFunApp And(AI.IExpr p, AI.IExpr q) {
      //Contract.Requires(p != null);
      //Contract.Requires(q != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      return Expr.Binary(BinaryOperator.Opcode.And, IExpr2Expr(p), IExpr2Expr(q));
    }

    public AI.IFunApp Or(AI.IExpr p, AI.IExpr q) {
      //Contract.Requires(p != null);
      //Contract.Requires(q != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
      return Expr.Binary(BinaryOperator.Opcode.Or, IExpr2Expr(p), IExpr2Expr(q));
    }

    public AI.IFunApp Implies(AI.IExpr p, AI.IExpr q) {
      //Contract.Requires(p != null);
      //Contract.Requires(q != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
      return Expr.Binary(BinaryOperator.Opcode.Imp, IExpr2Expr(p), IExpr2Expr(q));
    }

    public AI.IFunApp Exists(AI.IFunction p) {
      //Contract.Requires(p != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      return (AI.IFunApp)(new ExistsExpr(Token.NoToken, new VariableSeq((Variable)p.Param), IExpr2Expr(p.Body))).IExpr;
    }
    public AI.IFunApp Exists(AI.AIType paramType, AI.FunctionBody bodygen) {
      //Contract.Requires(bodygen != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      // generate a fresh new variable
      Variable var = FreshBoundVariable(paramType);
      Contract.Assert(var != null);
      Expr expr = IExpr2Expr(bodygen(var));
      Contract.Assert(expr != null);
      return (AI.IFunApp)(new ExistsExpr(Token.NoToken, new VariableSeq(var), expr)).IExpr;
    }

    public AI.IFunApp Forall(AI.IFunction p) {
      //Contract.Requires(p != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      return (AI.IFunApp)(new ForallExpr(Token.NoToken, new VariableSeq((Variable)p.Param), IExpr2Expr(p.Body))).IExpr;
    }
    public AI.IFunApp Forall(AI.AIType paramType, AI.FunctionBody bodygen) {
      //Contract.Requires(bodygen != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      // generate a fresh new variable
      Variable var = FreshBoundVariable(paramType);
      Contract.Assert(var != null);
      Expr expr = IExpr2Expr(bodygen(var));
      Contract.Assert(expr != null);
      return (AI.IFunApp)(new ForallExpr(Token.NoToken, new VariableSeq(var), expr)).IExpr;
    }

    private static int freshVarNum = 0;
    private static Variable FreshBoundVariable(AI.AIType paramType) {
      Contract.Ensures(Contract.Result<Variable>() != null);

      // TODO: Should use the AI.AIType given in Exists and Forall to determine what Boogie type
      // to make this new variable?  For now, we use Type.Any.
      Type t = Type.Int;
      Contract.Assert(t != null);
      /*
        if (paramType is AI.Ref)
          t = Type.Ref;
        else if (paramType is AI.FieldName)
          t = Type.Name;
        else
          System.Console.WriteLine("*** unsupported type in AI {0}", paramType); */
      Contract.Assert(false);
      throw new cce.UnreachableException();
      TypedIdent id = new TypedIdent(Token.NoToken, "propfactory_freshvar" + freshVarNum, t);
      freshVarNum++;
      return new BoundVariable(Token.NoToken, id);
    }
  }

  public class BoogieValueFactory : BoogieFactory, AI.IValueExprFactory {
    public AI.IFunApp Eq(AI.IExpr e0, AI.IExpr e1) {
      //Contract.Requires(e0 != null);
      //Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      return Expr.Eq(IExpr2Expr(e0), IExpr2Expr(e1));
    }
    public AI.IFunApp Neq(AI.IExpr e0, AI.IExpr e1) {
      //Contract.Requires(e0 != null);
      //Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
      return Expr.Neq(IExpr2Expr(e0), IExpr2Expr(e1));
    }
  }

  public class BoogieNullnessFactory : BoogieFactory, AI.INullnessFactory {
    public AI.IFunApp Eq(AI.IExpr e0, AI.IExpr e1) {
      //Contract.Requires(e0 != null);
      //Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
      return Expr.Eq(IExpr2Expr(e0), IExpr2Expr(e1));
    }

    public AI.IFunApp Neq(AI.IExpr e0, AI.IExpr e1) {
      //Contract.Requires(e0 != null);
      //Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
      return Expr.Neq(IExpr2Expr(e0), IExpr2Expr(e1));
    }

    public AI.IFunApp Null {
      get {
        Contract.Assert(false);       // don't know where to get null from\
        throw new cce.UnreachableException();
      }
    }
  }

  public class BoogieIntFactory : BoogieValueFactory, AI.IIntExprFactory {
    public AI.IFunApp Const(BigNum i) {
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      return new LiteralExpr(Token.NoToken, i);
    }
  }

  public class BoogieLinearFactory : BoogieIntFactory, AI.ILinearExprFactory {
    public AI.IFunApp AtMost(AI.IExpr e0, AI.IExpr e1) {
      //Contract.Requires(e0 != null);
      //Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
      return Expr.Le(IExpr2Expr(e0), IExpr2Expr(e1));
    }
    public AI.IFunApp Add(AI.IExpr e0, AI.IExpr e1) {
      //Contract.Requires(e0 != null);
      //Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
      return Expr.Add(IExpr2Expr(e0), IExpr2Expr(e1));
    }
    public AI.IExpr Term(Rational r, AI.IVariable var) {
      Contract.Ensures(Contract.Result<AI.IExpr>() != null);

      if (var != null && r == Rational.ONE) {
        return var;
      } else {
        Expr product;
        if (r.IsIntegral) {
          product = Expr.Literal(r.AsBigNum);
        } else {
          product = Expr.Div(Expr.Literal(r.Numerator), Expr.Literal(r.Denominator));
        }
        if (var != null) {
          product = Expr.Mul(product, IExpr2Expr(var));
        }
        return product.IExpr;
      }
    }

    public AI.IFunApp False {
      get {
        Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

        return Expr.False;
      }
    }
    public AI.IFunApp True {
      get {
        Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

        return Expr.True;
      }
    }
    public AI.IFunApp And(AI.IExpr p, AI.IExpr q) {
      //Contract.Requires(p != null);
      //Contract.Requires(q != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      return Expr.Binary(BinaryOperator.Opcode.And, IExpr2Expr(p), IExpr2Expr(q));
    }
  }

  public class BoogieTypeFactory : BoogieFactory, AI.ITypeExprFactory {
    /// <summary>
    /// Returns an expression denoting the top of the type hierarchy.
    /// </summary>
    public AI.IExpr RootType {
      get {
        Contract.Assert(false);  // BUGBUG: TODO
        throw new System.NotImplementedException();
      }
    }

    /// <summary>
    /// Returns true iff "t" denotes a type constant.
    /// </summary>
    [Pure]
    public bool IsTypeConstant(AI.IExpr t) {
      //Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<bool>() == (t is Constant));
      return t is Constant;
    }

    /// <summary>
    /// Returns true iff t0 and t1 are types such that t0 and t1 are equal.
    /// </summary>
    [Pure]
    public bool IsTypeEqual(AI.IExpr t0, AI.IExpr t1) {
      //Contract.Requires(t0 != null);
      //Contract.Requires(t1 != null);
      Constant c0 = t0 as Constant;
      Constant c1 = t1 as Constant;
      return c0 != null && c1 != null && c0 == c1;
    }

    /// <summary>
    /// Returns true iff t0 and t1 are types such that t0 is a subtype of t1.
    /// </summary>
    [Pure]
    public bool IsSubType(AI.IExpr t0, AI.IExpr t1) {
      //Contract.Requires(t0 != null);
      //Contract.Requires(t1 != null);

      Contract.Assert(false);  // BUGBUG: TODO
      throw new cce.UnreachableException();
    }

    /// <summary>
    /// Returns the most derived supertype of both "t0" and "t1".  A precondition is
    /// that "t0" and "t1" both represent types.
    /// </summary>
    public AI.IExpr JoinTypes(AI.IExpr t0, AI.IExpr t1) {
      //Contract.Requires(t0 != null);
      //Contract.Requires(t1 != null);
      Contract.Ensures(Contract.Result<AI.IExpr>() != null);


      Contract.Assert(false);  // BUGBUG: TODO
      throw new cce.UnreachableException();
    }

    public AI.IFunApp IsExactlyA(AI.IExpr e, AI.IExpr type) {
      //PM: We need this assume because Boogie does not yet allow us to use the
      //PM: inherited precondition "requires IsTypeConstant(type)".
      //PM: Note that that precondition is currently commented out.
      //Contract.Requires(e != null);
      //Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);

      Contract.Assume(type is Constant);
      Constant theType = (Constant)type;
      Contract.Assert(false);
      throw new cce.UnreachableException();
      Expr typeofExpr = new NAryExpr(Token.NoToken,
          new FunctionCall(new IdentifierExpr(Token.NoToken, "$typeof", Type.Int // Name
                           )),
          new ExprSeq(IExpr2Expr(e)));
      return Expr.Eq(typeofExpr, Expr.Ident(theType));
    }

    public AI.IFunApp IsA(AI.IExpr e, AI.IExpr type) {
      //Contract.Requires(e != null);
      //Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<AI.IFunApp>() != null);
      //PM: We need this assume because Boogie does not yet allow us to use the
      //PM: inherited precondition "requires IsTypeConstant(type)".
      //PM: Note that that precondition is currently commented out.
      

      Contract.Assume(type is Constant);
      Contract.Assert(false);
      throw new cce.UnreachableException();
      Expr typeofExpr = new NAryExpr(Token.NoToken,
          new FunctionCall(new IdentifierExpr(Token.NoToken, "$typeof", Type.Int // Name
                           )),
          new ExprSeq(IExpr2Expr(e)));
      return new NAryExpr(Token.NoToken,
          new BinaryOperator(Token.NoToken, BinaryOperator.Opcode.Subtype),
          new ExprSeq(typeofExpr, IExpr2Expr(e)));
    }
  }
}
