using Microsoft.Boogie;
using Microsoft.BaseTypes;
using NUnit.Framework;
using System.Collections.Generic;
using System.Linq;

namespace CoreTests
{
  [TestFixture()]
  public class TokenTest : IErrorSink
  {
    [Test()]
    public void TokensCanBorrowTrailingTrivia() {
      // Simulates a step of parsing " .... x *\n/*ok*/ y /*:)*/ + "
      //  The trivia " /*ok*/ " is attached to y, whereas 
      // whereas the trivia " /*:)*/ " that used to be attached to "y" has to be attached
      // to the expression x * y, by producing another token for that that "borrows" that trivia
      var filename = "thefile.bpl";
      var plusTopk = new Token(10, 40) {
        filename = filename,
        kind = 53,
        next = null,
        val = "+",
        pos = 157,
        leadingTrivia = "",
        trailingTrivia = " "
      };
      var yTok = new Token(10, 32) {
        filename = filename,
        kind = 47,
        next = plusTopk,
        val = "y",
        pos = 149,
        leadingTrivia = " /*ok*/ ",
        trailingTrivia = " /*:)*/ "
      };
      var endOfMultiplicationTok = yTok.BorrowTrivia(trailing: true);
      Assert.AreEqual(filename, yTok.filename);
      Assert.AreEqual(47, yTok.kind);
      Assert.AreEqual(plusTopk, yTok.next);
      Assert.AreEqual("y", yTok.val);
      Assert.AreEqual(149, yTok.pos);
      Assert.AreEqual(" /*ok*/ ", yTok.leadingTrivia);
      Assert.AreEqual(null, yTok.trailingTrivia);
      
      Assert.AreEqual(filename, endOfMultiplicationTok.filename);
      Assert.AreEqual(47, endOfMultiplicationTok.kind);
      Assert.AreEqual(null, endOfMultiplicationTok.next); // Detached token
      Assert.AreEqual("y", endOfMultiplicationTok.val);
      Assert.AreEqual(149, endOfMultiplicationTok.pos);
      Assert.AreEqual(null, endOfMultiplicationTok.leadingTrivia);
      Assert.AreEqual(" /*:)*/ ", endOfMultiplicationTok.trailingTrivia);
    }
    
    [Test()]
    public void TokensCanBorrowLeadingTrivia() {
      // Simulates a step of parsing " ....+\n /*:)*/ x /*ok*/ * y"
      //  The trivia " /*ok*/ " is attached to x, whereas 
      // whereas the trivia " /*:)*/ " that used to be attached to "x" has to be attached
      // to the expression x * y, by producing another token for that that "borrows" that trivia
      var filename = "thefile.bpl";
      var timesTok = new Token(10, 41) {
        filename = filename,
        kind = 53,
        next = null,
        val = "*",
        pos = 158,
        leadingTrivia = "",
        trailingTrivia = " "
      };
      var xTok = new Token(10, 32) {
        filename = filename,
        kind = 47,
        next = timesTok,
        val = "x",
        pos = 149,
        leadingTrivia = " /*:)*/ ",
        trailingTrivia = " /*ok*/ "
      };
      var startOfMultiplicationTok = xTok.BorrowTrivia(leading: true);
      Assert.AreEqual(filename, xTok.filename);
      Assert.AreEqual(47, xTok.kind);
      Assert.AreEqual(timesTok, xTok.next);
      Assert.AreEqual("x", xTok.val);
      Assert.AreEqual(149, xTok.pos);
      Assert.AreEqual(null, xTok.leadingTrivia);
      Assert.AreEqual(" /*ok*/ ", xTok.trailingTrivia);
      
      Assert.AreEqual(filename, startOfMultiplicationTok.filename);
      Assert.AreEqual(47, startOfMultiplicationTok.kind);
      Assert.AreEqual(null, startOfMultiplicationTok.next); // Detached token
      Assert.AreEqual("x", startOfMultiplicationTok.val);
      Assert.AreEqual(149, startOfMultiplicationTok.pos);
      Assert.AreEqual(" /*:)*/ ", startOfMultiplicationTok.leadingTrivia);
      Assert.AreEqual(null, startOfMultiplicationTok.trailingTrivia);
    }


    public void Error(IToken tok, string msg)
    {
      Assert.Fail(msg);
    }
  }
}