using System;
using System.IO;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using NUnit.Framework;

namespace ExecutionEngineTests;

[TestFixture]
public class ReduceLetTest
{
  private class ThrowingParser : SExpr.Parser
  {
    public ThrowingParser(StreamReader reader) : base(reader)
    {
    }

    public override void ParseError(string msg)
    {
      throw new FormatException(msg);
    }
  }

  private static SExpr Parse(string text)
  {
    using var reader = new StreamReader(new MemoryStream(Encoding.UTF8.GetBytes(text)));
    return new ThrowingParser(reader).ParseSExprs(true).Single();
  }

  private static bool ContainsLet(SExpr expr)
  {
    return expr.Name == "let" || expr.Arguments.Any(ContainsLet);
  }

  /// <summary>
  /// z3's reply to <c>(get-value (a))</c> for an <c>(Array Int Int)</c> with eight stores. It
  /// shares the inner store chain through a second, nested <c>let</c> whose binding names the
  /// first one's.
  /// </summary>
  [Test]
  public void ReducesNestedLets()
  {
    var reply = Parse(@"
(let ((a!1 (store (store (store ((as const (Array Int Int)) 11) 4 28100)
                         2
                         10450)
                  0
                  32285)))
(let ((a!2 (store (store (store (store a!1 3 30612) 1 11797) 6 1142) 7 281)))
  (store a!2 5 5853)))");

    var reduced = SMTLibProcessTheoremProver.ReduceLet(reply);

    Assert.IsFalse(ContainsLet(reduced), reduced.ToString());
    Assert.AreEqual(
      Parse(@"
(store (store (store (store (store (store (store (store
  ((as const (Array Int Int)) 11) 4 28100) 2 10450) 0 32285)
  3 30612) 1 11797) 6 1142) 7 281) 5 5853)").ToString(),
      reduced.ToString());
  }

  /// <summary>A <c>let</c> whose body is just one of its own names.</summary>
  [Test]
  public void ReducesALetWhoseBodyIsABoundName()
  {
    var reduced = SMTLibProcessTheoremProver.ReduceLet(
      Parse("(let ((a!1 (store ((as const (Array Int Int)) 0) 1 2))) a!1)"));

    Assert.AreEqual(Parse("(store ((as const (Array Int Int)) 0) 1 2)").ToString(), reduced.ToString());
  }

  [Test]
  public void ReducesASingleLet()
  {
    var reduced = SMTLibProcessTheoremProver.ReduceLet(
      Parse("(let ((a!1 ((as const (Array Int Int)) 0))) (store (store a!1 1 2) 3 4))"));

    Assert.AreEqual(
      Parse("(store (store ((as const (Array Int Int)) 0) 1 2) 3 4)").ToString(),
      reduced.ToString());
  }

  [Test]
  public void LeavesALetFreeTermAlone()
  {
    var term = Parse("(store ((as const (Array Int Int)) 0) 1 2)");

    Assert.AreEqual(term.ToString(), SMTLibProcessTheoremProver.ReduceLet(term).ToString());
  }

  [Test]
  public void ReducesALetInsideAnArgument()
  {
    var reduced = SMTLibProcessTheoremProver.ReduceLet(
      Parse("(store (let ((a!1 ((as const (Array Int Int)) 0))) (store a!1 1 2)) 3 4)"));

    Assert.AreEqual(
      Parse("(store (store ((as const (Array Int Int)) 0) 1 2) 3 4)").ToString(),
      reduced.ToString());
  }

  [Test]
  public void ReducesALetInsideABindingValue()
  {
    var reduced = SMTLibProcessTheoremProver.ReduceLet(
      Parse("(let ((a!2 (let ((a!1 ((as const (Array Int Int)) 0))) (store a!1 1 2)))) (store a!2 3 4))"));

    Assert.AreEqual(
      Parse("(store (store ((as const (Array Int Int)) 0) 1 2) 3 4)").ToString(),
      reduced.ToString());
  }

  [Test]
  public void ReducesALetInsideALambdaBody()
  {
    var reduced = SMTLibProcessTheoremProver.ReduceLet(
      Parse("(lambda ((x!1 Int)) (let ((a!1 (= x!1 3))) (ite a!1 7 0)))"));

    Assert.AreEqual(Parse("(lambda ((x!1 Int)) (ite (= x!1 3) 7 0))").ToString(), reduced.ToString());
  }

  /// <summary>
  /// A let's bindings are evaluated in the enclosing scope, all at once: in the inner let below,
  /// <c>y</c> is bound to the outer <c>x</c>, and the inner <c>x</c> shadows it in the body.
  /// </summary>
  [Test]
  public void BindsInParallelAndShadows()
  {
    var reduced = SMTLibProcessTheoremProver.ReduceLet(
      Parse("(let ((x 1)) (let ((x 2) (y x)) (f x y)))"));

    Assert.AreEqual(Parse("(f 2 1)").ToString(), reduced.ToString());
  }
}
