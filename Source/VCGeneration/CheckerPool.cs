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
    private readonly ConcurrentStack<Checker> availableCheckers = new();
    private readonly SemaphoreSlim checkersSemaphore;
    private bool disposed;

    public VCGenOptions Options { get; }

    public CheckerPool(VCGenOptions options)
    {
      Options = options;
      checkersSemaphore = new(options.VcsCores);
    }

    public async Task<Checker> FindCheckerFor(Program program, Split? split, CancellationToken cancellationToken)
    {
      await checkersSemaphore.WaitAsync(cancellationToken);
      try {
        if (!availableCheckers.TryPop(out var checker)) {
          checker ??= CreateNewChecker();
        }
        checker.Prepare(program, split);
        return checker;
      } catch (Exception) {
        checkersSemaphore.Release();
        throw;
      }
    }

    private int createdCheckers;
    private Checker CreateNewChecker()
    {
      if (disposed)
      {
        throw new ObjectDisposedException(nameof(CheckerPool));
      }
      
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
        checkersSemaphore.Dispose();
        while (availableCheckers.TryPop(out var checker)) {
          checker.Close();
        }
      }
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
        availableCheckers.Push(checker);
        checkersSemaphore.Release();
      }
    }

    public void CheckerDied()
    {
      checkersSemaphore.Release();
    }
  }
}