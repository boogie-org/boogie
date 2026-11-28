using System;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using NUnit.Framework;

namespace ExecutionEngineTests;

[TestFixture]
public class HardTimeoutTest {
  /// <summary>
  /// Covers Check's handling of a hard timeout, a case z3-exits-during-check.bpl can only reach through a real z3
  /// slow enough for its -T limit to fire. SendRequest's reading of z3's `timeout` answer is in SMTLibProcess,
  /// which this solver replaces, so the lit test stays the only cover for that line.
  /// </summary>
  [Test]
  public async Task AHardTimeoutIsATimeoutRatherThanASolverException() {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.CreateSolver = (_, _) => new HardTimeoutSolver();
    using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    Assert.AreEqual(0, Parser.Parse("procedure P(x: int) { assert x == x; }", "fakeFilename", out var program));

    var output = new StringWriter();
    await engine.ProcessProgram(output, program, "fakeFilename");

    Assert.That(output.ToString(), Does.Not.Contain("solver exception"));
    Assert.That(output.ToString(), Does.Contain("this assertion could not be proved"));
  }

  /// <summary>
  /// Reports its own hard time limit, as SMTLibProcess does once z3 answers `timeout`.
  /// </summary>
  private class HardTimeoutSolver : NoopSolver {
    public override Task<SExpr> SendRequest(string request, CancellationToken cancellationToken = default) {
      if (request == "(check-sat)") {
        throw new TimeoutException();
      }

      return base.SendRequest(request, cancellationToken);
    }
  }
}
