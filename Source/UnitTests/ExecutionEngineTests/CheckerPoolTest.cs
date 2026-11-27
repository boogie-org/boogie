using System;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using NUnit.Framework;
using VC;

namespace ExecutionEngineTests;

[TestFixture]
public class CheckerPoolTest {
  [Test]
  public async Task CheckerOfADisposedPoolIsClosedWhenItsSolverDoesNotAnswer() {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    var solver = new UnresponsiveSolver();
    options.CreateSolver = (_, _) => solver;
    var pool = new CheckerPool(options);
    var checker = await pool.FindCheckerFor(null, null, CancellationToken.None);
    pool.Dispose();
    await checker.GoBackToIdle();
    Assert.IsTrue(solver.Closed);
  }

  [Test]
  public async Task FindCheckerForFailsOnceThePoolIsDisposed() {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.VcsCores = 1;
    options.CreateSolver = (_, _) => new NoopSolver();
    var pool = new CheckerPool(options);
    var checker = await pool.FindCheckerFor(null, null, CancellationToken.None);
    var waiting = pool.FindCheckerFor(null, null, CancellationToken.None);
    pool.Dispose();
    Assert.ThrowsAsync<ObjectDisposedException>(() =>
      pool.FindCheckerFor(null, null, CancellationToken.None).WaitAsync(TimeSpan.FromSeconds(5)));
    await checker.GoBackToIdle();
    Assert.ThrowsAsync<ObjectDisposedException>(() => waiting.WaitAsync(TimeSpan.FromSeconds(5)));
  }

  private class UnresponsiveSolver : NoopSolver {
    public bool Closed { get; private set; }
    public override Task PingPong() => new TaskCompletionSource().Task;
    public override void Close() => Closed = true;
  }
}
