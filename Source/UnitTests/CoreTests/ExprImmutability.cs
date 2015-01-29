using NUnit.Framework;
using System;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace CoreTests
{
    [TestFixture()]
    public class ExprImmutability : IErrorSink
    {

        public void Error(IToken tok, string msg)
        {
            Assert.Fail (msg);
        }

        [Test(), ExpectedException(typeof(InvalidOperationException))]
        public void IdentifierExprName()
        {
            var id = new IdentifierExpr(Token.NoToken, "foo", BasicType.Bool, /*immutable=*/true);
            Assert.IsTrue(id.Immutable);
            id.Name = "foo2";
        }

        [Test(), ExpectedException(typeof(InvalidOperationException))]
        public void IdentifierExprDecl()
        {
            var id = new IdentifierExpr(Token.NoToken, "foo", BasicType.Bool, /*immutable=*/true);
            Assert.IsTrue(id.Immutable);
            var typedIdent = new TypedIdent(Token.NoToken, "foo2", BasicType.Bool);
            id.Decl = new GlobalVariable(Token.NoToken, typedIdent);
        }

        private NAryExpr GetUnTypedImmutableNAry()
        {
            var id = new IdentifierExpr(Token.NoToken, "foo", BasicType.Bool, /*immutable=*/true);
            Assert.IsTrue(id.Immutable);
            Assert.IsTrue(id.Type.IsBool);
            var e = new NAryExpr(Token.NoToken, new BinaryOperator(Token.NoToken, BinaryOperator.Opcode.And), new List<Expr>() {
                id,
                id
            }, /*immutable=*/true);
            Assert.IsNull(e.Type);
            Assert.IsTrue(e.Immutable);
            return e;
        }

        [Test()]
        public void ProtectedExprType()
        {
            var e = GetUnTypedImmutableNAry();

            // Now Typecheck
            // Even though it's immutable we allow the TypeCheck field to be set if the Expr has never been type checked
            var TC = new TypecheckingContext(this);
            e.Typecheck(TC);
            Assert.IsNotNull(e.Type);
            Assert.IsTrue(e.Type.IsBool);
        }

        [Test(), ExpectedException(typeof(InvalidOperationException))]
        public void ProtectedExprChangeTypeFail()
        {
            var e = GetUnTypedImmutableNAry();

            // Now Typecheck
            // Even though it's immutable we allow the TypeCheck field to be set if the Expr has never been type checked
            var TC = new TypecheckingContext(this);
            e.Typecheck(TC);
            Assert.IsNotNull(e.Type);
            Assert.IsTrue(e.Type.IsBool);

            // Trying to modify the Type to a different Type now should fail
            e.Type = BasicType.Int;
        }

        [Test()]
        public void ProtectedExprTypeChangeTypeSucceed()
        {
            var e = GetUnTypedImmutableNAry();

            // Now Typecheck
            // Even though it's immutable we allow the TypeCheck field to be set if the Expr has never been type checked
            var TC = new TypecheckingContext(this);
            e.Typecheck(TC);
            Assert.IsNotNull(e.Type);
            Assert.IsTrue(e.Type.IsBool);

            // Trying to assign the same Type should succeed
            e.Type = BasicType.Bool;
        }
    }
}

