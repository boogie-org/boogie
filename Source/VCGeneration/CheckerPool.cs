using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace VC
{  
  public record CheckerWaiter(
    TaskCompletionSource<Checker> checkerSource,
    ConditionGeneration vcgen,
    Split split = null);
  
  public class CheckerPool
  {
    private readonly CommandLineOptions options;

    private readonly Stack<Checker> availableCheckers = new();
    private readonly Queue<CheckerWaiter> checkerWaiters = new();
    private int notCreatedCheckers;
    private bool disposed;
    
    public CheckerPool(CommandLineOptions options)
    {
      this.options = options;
      notCreatedCheckers = options.VcsCores;
    }

    public Task<Checker> FindCheckerFor(ConditionGeneration vcgen, Split split = null)
    {
      lock (this) {
        if (disposed) {
          return Task.FromException<Checker>(new Exception("CheckerPool was already disposed"));
        }
        
        if (availableCheckers.TryPop(out var result)) {
          PrepareChecker(vcgen.program, split, result);
          Contract.Assert(result != null);
          return Task.FromResult(result);
        }

        int afterDec = Interlocked.Decrement(ref notCreatedCheckers);
        if (afterDec >= 0) {
          var checker = CreateNewChecker(vcgen, split);
          Contract.Assert(checker != null);
          return Task.FromResult(checker);
        }

        Interlocked.Increment(ref notCreatedCheckers);
        var source = new TaskCompletionSource<Checker>();
        var checkerWaiter = new CheckerWaiter(source, vcgen, split);
        checkerWaiters.Enqueue(checkerWaiter);
        return source.Task;
      }
      
    }

    private Checker CreateNewChecker(ConditionGeneration vcgen, Split split)
    {
      var log = options.ProverLogFilePath;
      if (log != null && !log.Contains("@PROC@") && availableCheckers.Count > 0) {
        log = log + "." + availableCheckers.Count;
      }

      Checker ch = new Checker(this, vcgen, vcgen.program, options.ProverLogFilePath, options.ProverLogFileAppend, split);
      ch.GetReady();
      return ch;
    }

    public void Dispose()
    {
      lock (this) {
        foreach (var checker in availableCheckers)
        {
          Contract.Assert(checker != null);
          checker.Close();
        }
        availableCheckers.Clear();

        // Notify all checker waiters that they shouldn't wait anymore.
        foreach (var waiter in checkerWaiters) {
          waiter.checkerSource.TrySetException(new Exception("CheckerPool was disposed"));
        }
        disposed = true;
      }
    }

    void PrepareChecker(Program program, Split split, Checker checker)
    {
      if (checker.WillingToHandle(program) && (split == null || checker.SolverOptions.RandomSeed == split.RandomSeed && !options.Prune))
      {
        checker.GetReady();
        return;
      }

      checker.Retarget(program, checker.TheoremProver.Context, split);
      checker.GetReady();
    }

    public void AddChecker(Checker checker)
    {
      if (checker.IsClosed) {
        throw new Exception();
      }
      if (disposed) {
        checker.Close();
        return;
      }
      lock(this)
      {
        if (checkerWaiters.TryDequeue(out var waiter)) {
          PrepareChecker(waiter.vcgen.program, waiter.split, checker);
          if (waiter.checkerSource.TrySetResult(checker)) {
            return;
          }
        }

        availableCheckers.Push(checker);
      }
    }

    public void CheckerDied()
    {
      if (disposed) {
        return;
      }
      lock(this)
      {
        if (checkerWaiters.TryDequeue(out var waiter)) {
          var checker = CreateNewChecker(waiter.vcgen, waiter.split);
          if (waiter.checkerSource.TrySetResult(checker)) {
            return;
          }
        }

        Interlocked.Increment(ref notCreatedCheckers);
      }
    }
  }
}