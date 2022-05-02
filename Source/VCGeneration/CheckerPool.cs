#nullable enable
using System;
using System.Collections.Concurrent;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace VC
{
  public class CheckerPool
  {
    private readonly ConcurrentBag<Checker> availableCheckers = new();
    private readonly SemaphoreSlim checkersSemaphore;
    private bool disposed;

    public VCGenOptions Options { get; }

    public CheckerPool(VCGenOptions options)
    {
      Options = options;
      checkersSemaphore = new(options.VcsCores);
    }

    public async Task<Checker> FindCheckerFor(ConditionGeneration vcgen, Split? split, CancellationToken cancellationToken)
    {
      if (disposed) {
        throw new Exception("CheckerPool was already disposed");
      }

      await checkersSemaphore.WaitAsync(cancellationToken);
      if (!availableCheckers.TryTake(out var checker)) {
        checker ??= CreateNewChecker();
      }

      PrepareChecker(vcgen.program, split, checker);
      return checker;
    }

    private int createdCheckers;
    private Checker CreateNewChecker()
    {
      var log = Options.ProverLogFilePath;
      var index = Interlocked.Increment(ref createdCheckers) - 1;
      if (log != null && !log.Contains("@PROC@") && index > 0) {
        log = log + "." + index;
      }

      return new Checker(this, log, Options.ProverLogFileAppend);
    }

    public void Dispose()
    {
      lock(availableCheckers)
      {
        disposed = true;
        foreach (var checker in availableCheckers.ToArray()) {
          checker.Close();
        }
      }
    }

    void PrepareChecker(Program program, Split? split, Checker checker)
    {
      if (checker.WillingToHandle(program) && (split == null || checker.SolverOptions.RandomSeed == split.RandomSeed && !Options.Prune))
      {
        checker.GetReady();
        return;
      }

      checker.Target(program, checker.TheoremProver.Context, split);
      checker.GetReady();
    }

    public void AddChecker(Checker checker)
    {
      if (checker.IsClosed) {
        throw new Exception();
      }

      lock (availableCheckers) {
        if (disposed) {
          checker.Close();
          return;
        }
        availableCheckers.Add(checker);
        checkersSemaphore.Release();
      }
    }

    public void CheckerDied()
    {
      checkersSemaphore.Release();
    }
  }
}