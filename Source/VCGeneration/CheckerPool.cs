using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace VC
{
  public class CheckerPool
  {
    private readonly CommandLineOptions options;

    private readonly Stack<Checker> availableCheckers = new();
    private readonly Queue<TaskCompletionSource<Checker>> checkerWaiters = new();
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
        checkerWaiters.Enqueue(source);
        return source.Task.ContinueWith(t =>
        {
          PrepareChecker(vcgen.program, split, t.Result);
          Contract.Assert(t.Result != null);
          return t.Result;
        });
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
          if (waiter.TrySetResult(checker)) {
            return;
          }
        }

        availableCheckers.Push(checker);
      }
    }
  }
}