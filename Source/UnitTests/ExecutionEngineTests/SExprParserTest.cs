using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;
using SMTLib;

namespace ExecutionEngineTests;

[TestFixture]
public class SExprParserTest {

  private static Task<List<SExpr>> Parse(SExprParser parser) =>
    parser.ParseSExprs(true).ToListAsync().AsTask().WaitAsync(TimeSpan.FromSeconds(10));

  [Test]
  public async Task ReadsAfterTheEndOfTheInputDoNotWait() {
    var parser = new SExprParser();
    parser.AddLine("(model");
    parser.EndInput();

    Assert.AreEqual("model", (await Parse(parser)).Single().Name);
    Assert.AreEqual(0, (await Parse(parser)).Count);
    Assert.IsTrue(parser.EndOfInput);
  }

  [Test]
  public async Task AStrayClosingParenthesisIsReadOnlyOnce() {
    var parser = new SExprParser();
    parser.AddLine(") (pong)");

    Assert.AreEqual(0, (await Parse(parser)).Count);
    Assert.AreEqual("pong", (await Parse(parser)).Single().Name);
  }
}
