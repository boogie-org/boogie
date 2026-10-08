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

  [Test]
  public async Task ReadsAfterTheEndOfTheInputDoNotWait() {
    var parser = new SExprParser();
    parser.AddLine("(model");
    parser.AddLine(null);

    Task<List<SExpr>> Parse() => parser.ParseSExprs(true).WaitAsync(TimeSpan.FromSeconds(10));
    Assert.AreEqual("model", (await Parse()).Single().Name);
    Assert.AreEqual(0, (await Parse()).Count);
    Assert.IsTrue(parser.EndOfInput);
  }
}
