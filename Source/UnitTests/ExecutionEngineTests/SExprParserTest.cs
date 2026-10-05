using System;
using System.Linq;
using System.Threading.Tasks;
using NUnit.Framework;
using SMTLib;

namespace ExecutionEngineTests;

[TestFixture]
public class SExprParserTest {

  [Test]
  public async Task ReadsAfterTheEndOfTheInputDoNotWait() {
    var parser = new SExprParser();
    parser.AddLine("unsat");
    parser.AddLine(null);

    Assert.AreEqual(1, (await parser.ParseSExprs(true).ToListAsync()).Count);
    for (var i = 0; i < 3; i++) {
      var exprs = await parser.ParseSExprs(true).ToListAsync().AsTask().WaitAsync(TimeSpan.FromSeconds(10));
      Assert.AreEqual(0, exprs.Count);
    }
    Assert.IsTrue(parser.EndOfInput);
  }
}
