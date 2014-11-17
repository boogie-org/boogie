using Microsoft.Boogie;
using Microsoft.Basetypes;
using NUnit.Framework;
using System.Collections.Generic;
using System;

namespace CoreTests
{
  [TestFixture()]
  public class ExprEquality {

    [Test()]
    public void LiteralBool() {
      var constant = new LiteralExpr(Token.NoToken, false);
      var constant2 = new LiteralExpr(Token.NoToken, false);

      Assert.AreNotSame(constant, constant2); // These are different references

      Assert.IsTrue(constant.Equals(constant2)); // These are "structurally equal"
      Assert.AreEqual(constant.GetHashCode(), constant2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void LiteralBV() {
      var constant = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8;
      var constant2 = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8;

      Assert.AreNotSame(constant, constant2); // These are different references

      Assert.IsTrue(constant.Equals(constant2)); // These are "structurally equal"
      Assert.AreEqual(constant.GetHashCode(), constant2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void LiteralInt() {
      var constant = new LiteralExpr(Token.NoToken, BigNum.FromInt(18)); // Integer
      var constant2 = new LiteralExpr(Token.NoToken, BigNum.FromInt(18)); // Integer

      Assert.AreNotSame(constant, constant2); // These are different references

      Assert.IsTrue(constant.Equals(constant2)); // These are "structurally equal"
      Assert.AreEqual(constant.GetHashCode(), constant2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void LiteralReal() {
      var constant = new LiteralExpr(Token.NoToken, BigDec.FromString("11.7")); // Real
      var constant2 = new LiteralExpr(Token.NoToken, BigDec.FromString("11.7")); // Real

      Assert.AreNotSame(constant, constant2); // These are different references

      Assert.IsTrue(constant.Equals(constant2)); // These are "structurally equal"
      Assert.AreEqual(constant.GetHashCode(), constant2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void SimpleAdd() {
      var constant = new LiteralExpr(Token.NoToken, BigNum.FromInt(18)); // Integer
      var constant2 = new LiteralExpr(Token.NoToken, BigNum.FromInt(19)); // Integer
      var add = Expr.Add(constant, constant2);

      var add2 = Expr.Add(constant, constant2);

      Assert.AreNotSame(constant, constant2); // These are different references
      Assert.AreNotSame(add, add2); // These are different references

      Assert.IsTrue(add.Equals(add2)); // These are "structurally equal"
      Assert.AreEqual(add.GetHashCode(), add2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void SimpleIdentifierExprs() {
      var variable = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.GetBvType(8)));
      var idVar = new IdentifierExpr(Token.NoToken, variable);
      var idVar2 = new IdentifierExpr(Token.NoToken, variable);

      Assert.AreNotSame(idVar, idVar2); // These are different references

      Assert.IsTrue(idVar.Equals(idVar2)); // These are "structurally equal"
      Assert.AreEqual(idVar.GetHashCode(), idVar2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void SimpleIdentifierVariables() {
      var variable = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.GetBvType(8)));
      var variable2 = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.GetBvType(8)));
      var idVar = new IdentifierExpr(Token.NoToken, variable);
      var idVar2 = new IdentifierExpr(Token.NoToken, variable2);

      Assert.AreNotSame(idVar, idVar2); // These are different references
      // These are not "structurally equal" because the Variable references are different (even though they have the same name and type)
      Assert.IsFalse(idVar.Equals(idVar2));
    }

    [Test()]
    public void SimpleBVConcat() {
      var variable = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.GetBvType(8)));
      var id = new IdentifierExpr(Token.NoToken, variable);
      var constant = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8;
      var concat = new BvConcatExpr(Token.NoToken, id, constant);

      // Don't trust the Boogie duplicator here. Do it ourselves
      var constant2 = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8;
      // We don't duplicate the variable because that is not an Expr and we require reference equality.
      var id2 = new IdentifierExpr(Token.NoToken, variable);
      var concat2 = new BvConcatExpr(Token.NoToken, id2, constant2);

      Assert.AreNotSame(concat, concat2); // These are different references

      Assert.IsTrue(concat.Equals(concat2)); // These are "structurally equal"
      Assert.AreEqual(concat.GetHashCode(), concat2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void SimpleBVExtract() {
      var variable = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.GetBvType(8)));
      var id = new IdentifierExpr(Token.NoToken, variable);

      var extract = new BvExtractExpr(Token.NoToken, id, 5, 0); // 4-bits

      var id2 = new IdentifierExpr(Token.NoToken, variable);
      var extract2 = new BvExtractExpr(Token.NoToken, id2, 5, 0);

      Assert.AreNotSame(extract, extract2);

      Assert.IsTrue(extract.Equals(extract2));
      Assert.AreEqual(extract.GetHashCode(), extract2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void SimpleForAll() {
      var boundVar = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken,"foo",Microsoft.Boogie.Type.Bool));
      var id = new IdentifierExpr(Token.NoToken, boundVar);
      var forall = new ForallExpr(Token.NoToken, new List<Variable>() { boundVar }, id);

      var id2 = new IdentifierExpr(Token.NoToken, boundVar);
      var forall2 = new ForallExpr(Token.NoToken, new List<Variable>() { boundVar }, id2);

      Assert.AreNotSame(forall, forall2); // These are different references

      Assert.IsTrue(forall.Equals(forall2)); // These are "structurally equal"
      Assert.AreEqual(forall.GetHashCode(), forall2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }


    [Test()]
    public void SimpleExists() {
      var boundVar = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken,"foo",Microsoft.Boogie.Type.Bool));
      var id = new IdentifierExpr(Token.NoToken, boundVar);
      var exists = new ExistsExpr(Token.NoToken, new List<Variable>() { boundVar }, id);

      var id2 = new IdentifierExpr(Token.NoToken, boundVar);
      var exists2 = new ExistsExpr(Token.NoToken, new List<Variable>() { boundVar }, id2);

      Assert.AreNotSame(exists, exists2); // These are different references

      Assert.IsTrue(exists.Equals(exists2)); // These are "structurally equal"
      Assert.AreEqual(exists.GetHashCode(), exists2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }

    [Test()]
    public void SimpleLambda() {
      var boundVar = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken,"foo",Microsoft.Boogie.Type.Bool));
      var id = new IdentifierExpr(Token.NoToken, boundVar);

      // This is basically an Identity Map
      var lambdaExpr = new LambdaExpr(Token.NoToken, new List<TypeVariable>() , new List<Variable>() { boundVar }, null, id);

      var id2 = new IdentifierExpr(Token.NoToken, boundVar);
      var lambdaExpr2 = new LambdaExpr(Token.NoToken, new List<TypeVariable>() , new List<Variable>() { boundVar }, null, id2);

      Assert.AreNotSame(lambdaExpr, lambdaExpr2); // These are different references

      Assert.IsTrue(lambdaExpr.Equals(lambdaExpr2)); // These are "structurally equal"
      Assert.AreEqual(lambdaExpr.GetHashCode(), lambdaExpr2.GetHashCode()); // If the .Equals() is true then hash codes must be the same
    }
  }
}

