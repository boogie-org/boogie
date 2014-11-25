using Microsoft.Boogie;
using Microsoft.Basetypes;
using NUnit.Framework;
using System;
using System.Collections.Generic;
using System.Linq;

namespace CoreTests
{
    [TestFixture()]
    public class ExprTypeChecking : IErrorSink
    {
        [Test()]
        public void FunctionCall()
        {
            var fc = CreateFunctionCall("bv8slt", Microsoft.Boogie.Type.Bool, new List<Microsoft.Boogie.Type>() {
                BasicType.GetBvType(8),
                BasicType.GetBvType(8)
            });

            var constantBv = new LiteralExpr(Token.NoToken, BigNum.FromInt(0) , 8);
            var nary = new NAryExpr(Token.NoToken,fc, new List<Expr>() { constantBv, constantBv} );

            // Get shallow type (this was broken when this test was written)
            Assert.AreEqual(BasicType.Bool, nary.ShallowType);

            // Deep type check (this was not broken before writing this test)
            Assert.IsNull(nary.Type);

            var tc = new TypecheckingContext(this);
            nary.Typecheck(tc);

            Assert.AreEqual(BasicType.Bool, nary.Type);
        }

        [Test()]
        public void FunctionCallTypeResolved()
        {
            // This test case requires that function calls have been resolved
            // correctly and that the ShallowType is correct.
            // It's simpler to let the parser and resolver do all the work here
            // than try to build all the objects manually.
            var program = TestUtil.ProgramLoader.LoadProgramFrom(@"
                function {:bvbuiltin ""bvugt""} bv8ugt(bv8,bv8) returns(bool);

                procedure main(a:bv8)
                {
                    assert bv8ugt(a, 2bv8);
                }
            ", "file.bpl");

            var assertCmd = program.TopLevelDeclarations.OfType<Implementation>().First().Blocks.SelectMany(c => c.Cmds).OfType<AssertCmd>().First();
            Assert.AreEqual(BasicType.Bool, assertCmd.Expr.ShallowType);
        }

        public FunctionCall CreateFunctionCall(string Name, Microsoft.Boogie.Type returnType, IList<Microsoft.Boogie.Type> argTypes)
        {
            var returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", returnType), false);
            var vars = new List<Variable>();
            foreach (var T in argTypes)
            {
                vars.Add( new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "",T), true));
            }

            // Finally build the function and the function call
            var funcCall = new FunctionCall(new Function(Token.NoToken, Name, vars, returnVar));
            return funcCall;
        }

        public void Error(IToken tok, string msg)
        {
            Assert.Fail(msg);
        }

    }
}

