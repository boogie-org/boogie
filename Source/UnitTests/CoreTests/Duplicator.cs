using Microsoft.Boogie.TestUtil;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using NUnit.Framework;
using System;
using System.Linq;


namespace CoreTests
{
  [TestFixture ()]
  public class DuplicatorTests : BoogieTestBase, IErrorSink {
    Duplicator d;

    public void Error(IToken tok, string msg) {
      Assert.Fail(msg);
    }

    [SetUp]
    public void Init() {
      d = new Duplicator();
    }

    [Test()]
    public void BVConcatExpr() {
      var bv1_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 8);
      var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
      var A = new BvConcatExpr(Token.NoToken, bv1_8, bv2_8);
      var B = d.Visit(A);

      // The duplicator should ensure we get new BVConcatExprs
      Assert.AreNotSame(A, B);
    }

    [Test()]
    public void BvExtractExpr() {
      var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
      var A = new BvExtractExpr(Token.NoToken, bv2_8, 6,0);
      var B = d.Visit(A);

      // The duplicator should ensure we get new BVExtractExprs
      Assert.AreNotSame(A, B);
    }

    [Test()]
    public void NaryExpr() {
      var bv1_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 8);
      var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
      var A = NAryExpr.Eq (bv1_8, bv2_8);
      var B = d.Visit(A);

      Assert.AreNotSame(A, B);
    }

    [Test()]
    public void WholeProgram() {
      var p = new Program();
      var t = new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.Bool);
      var gv = new GlobalVariable(Token.NoToken, t);
      p.AddTopLevelDeclaration(gv);
      string metaDataString = "This is a test";
      p.SetMetadata(0, metaDataString);

      // Now try to clone
      var p2 = (Program) d.Visit(p);

      // Check global is a copy
      int counter = 0;
      GlobalVariable gv2 = null;
      foreach (var g in p2.TopLevelDeclarations)
      {
        ++counter;
        Assert.IsInstanceOf<GlobalVariable>(g);
        gv2 = g as GlobalVariable;
      }
      Assert.AreEqual(1, counter);
      Assert.AreNotSame(gv, gv2);
      Assert.AreEqual(metaDataString, p2.GetMetadata<string>(0));


      // Check Top level declarations list is duplicated properly
      var t2 = new TypedIdent(Token.NoToken, "bar", Microsoft.Boogie.Type.Bool);
      var gv3 = new GlobalVariable(Token.NoToken, t2);
      p2.AddTopLevelDeclaration(gv3);

      counter = 0;
      foreach (var g in p2.TopLevelDeclarations) {
        ++counter;
        Assert.IsInstanceOf<GlobalVariable>(g);
      }
      Assert.AreEqual(2, counter);

      // The original program should still only have one global variable
      counter = 0;
      foreach (var g in p.TopLevelDeclarations) {
        ++counter;
        Assert.IsInstanceOf<GlobalVariable>(g);
        Assert.AreSame(g, gv);
      }

      Assert.AreEqual(1, counter);

      // Change Metadata in p2, this shouldn't affect p
      string newMetaDataString = "Another test";
      p2.SetMetadata(0, newMetaDataString);

      Assert.AreNotEqual(p2.GetMetadata<string>(0), p.GetMetadata<string>(0));
    }

    [Test()]
    public void GotoTargets() {
      Program p = TestUtil.ProgramLoader.LoadProgramFrom(@"
        procedure main()
        {
            entry:
                assume true;
                goto thing1, thing2;

            thing1:
                assume true;
                assume true;
                goto entry, thing1;

            thing2:
                assume true;
                assume true;
                return;
        }
      ");

      var main = p.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "main").First();

      // Access blocks via their labels of gotocmds
      var oldEntryBlock =  ( main.Blocks[1].TransferCmd as GotoCmd ).labelTargets[0];
      Assert.AreEqual("entry", oldEntryBlock.Label);

      var oldThing1Block = ( main.Blocks[1].TransferCmd as GotoCmd ).labelTargets[1];
      Assert.AreEqual("thing1", oldThing1Block.Label);

      var oldThing2Block = ( main.Blocks[0].TransferCmd as GotoCmd ).labelTargets[1];
      Assert.AreEqual("thing2", oldThing2Block.Label);

      // Now duplicate
      var newProgram = (Program) d.Visit(p);

      // First lets check blocks have been duplicated
      var newMain= newProgram.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "main").First();
      var newEntryBlock = newMain.Blocks[0];
      Assert.AreEqual("entry", newEntryBlock.Label);
      Assert.AreNotSame(newEntryBlock, oldEntryBlock);

      var newThing1Block = newMain.Blocks[1];
      Assert.AreEqual("thing1", newThing1Block.Label);
      Assert.AreNotSame(newThing1Block, oldThing1Block);

      var newThing2Block = newMain.Blocks[2];
      Assert.AreEqual("thing2", newThing2Block.Label);
      Assert.AreNotSame(newThing2Block, oldThing2Block);

      // Now let's examine the gotos and make sure they point to the duplicated blocks.
      var newEntryGotoCmd = newEntryBlock.TransferCmd as GotoCmd;
      var newthing1GotoCmd = newThing1Block.TransferCmd as GotoCmd;

      Assert.AreNotSame(newEntryGotoCmd.labelTargets[0], oldThing1Block);
      Assert.AreSame(newEntryGotoCmd.labelTargets[0], newThing1Block);
      Assert.AreNotSame(newEntryGotoCmd.labelTargets[1], oldThing2Block);
      Assert.AreSame(newEntryGotoCmd.labelTargets[1], newThing2Block);

      Assert.AreNotSame(newthing1GotoCmd.labelTargets[0], oldEntryBlock);
      Assert.AreSame(newthing1GotoCmd.labelTargets[0], newEntryBlock);
      Assert.AreNotSame(newthing1GotoCmd.labelTargets[1], oldThing1Block);
      Assert.AreSame(newthing1GotoCmd.labelTargets[1], newThing1Block);

    }

    [Test()]
    public void ImplementationProcedureResolving() {
      Program p = TestUtil.ProgramLoader.LoadProgramFrom(@"
        procedure main(a:int) returns (r:int);
        requires a > 0;
        ensures  r > a;

        implementation main(a:int) returns (r:int)
        {
            r:= a + 1;
        }
      ");

      // Check resolved
      var oldMainImpl = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();
      var oldMainProc = p.TopLevelDeclarations.OfType<Procedure>().Where(i => i.Name == "main").First();
      Assert.AreSame(oldMainImpl.Proc, oldMainProc);

      // Now duplicate the program
      var newProgram = (Program) d.Visit(p);

      // Resolving doesn't seem to fix this.
      var rc = new ResolutionContext(this);
      newProgram.Resolve(rc);

      // Check resolved
      var newMainImpl = newProgram.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();
      var newMainProc = newProgram.TopLevelDeclarations.OfType<Procedure>().Where(i => i.Name == "main").First();
      Assert.AreSame(newMainImpl.Proc, newMainProc);
    }

    [Test()]
    public void CallCmdResolving() {
      Program p = TestUtil.ProgramLoader.LoadProgramFrom(@"
        procedure main()
        {
            var x:int;
            call x := foo();
            call x := bar();
        }

        procedure foo() returns(r:int)
        {
            r := 0;
        }

        procedure bar() returns(r:int);
        ensures r == 0;
      ");

    // Get hold of the procedures that will be used with the CallCmd
    var oldFoo = p.TopLevelDeclarations.OfType<Procedure>().Where(i => i.Name == "foo").First();
    var oldBar = p.TopLevelDeclarations.OfType<Procedure>().Where(i => i.Name == "bar").First();

    // Get the CallCmds to foo and bar
    var oldCmdsInMain = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").SelectMany(i => i.Blocks).SelectMany(b => b.Cmds);
    var oldCallToFoo = oldCmdsInMain.OfType<CallCmd>().Where(c => c.callee == "foo").First();
    var oldCallToBar = oldCmdsInMain.OfType<CallCmd>().Where(c => c.callee == "bar").First();

    // Check the Calls
    Assert.AreSame(oldCallToFoo.Proc, oldFoo);
    Assert.AreSame(oldCallToBar.Proc, oldBar);

    // Now duplicate the program and check that the calls are resolved correctly
    var newProgram = (Program) d.Visit(p);

    var foo = newProgram.TopLevelDeclarations.OfType<Procedure>().Where(i => i.Name == "foo").First();
    var bar = newProgram.TopLevelDeclarations.OfType<Procedure>().Where(i => i.Name == "bar").First();

    // Get the call to Foo
    var cmdsInMain = newProgram.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").SelectMany(i => i.Blocks).SelectMany(b => b.Cmds);
    var callToFoo = cmdsInMain.OfType<CallCmd>().Where(c => c.callee == "foo").First();
    var callToBar = cmdsInMain.OfType<CallCmd>().Where(c => c.callee == "bar").First();

    // Check the Calls
    Assert.AreNotSame(callToFoo.Proc, oldFoo);
    Assert.AreSame(callToFoo.Proc, foo);
    Assert.AreNotSame(callToBar.Proc, oldBar);
    Assert.AreSame(callToBar.Proc, bar);
    }
  }
}

