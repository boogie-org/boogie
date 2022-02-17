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
    private readonly Stack<Checker> availableCheckers = new();
    private readonly Queue<TaskCompletionSource<Checker>> checkerWaiters = new();
    private int notCreatedCheckers;
    private bool disposed;

    public VCGenOptions Options { get; }

    public CheckerPool(VCGenOptions options)
    {
      this.Options = options;
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

        if (notCreatedCheckers > 0) {
          notCreatedCheckers--;
          var checker = CreateNewChecker();
          PrepareChecker(vcgen.program, split, checker);
          Contract.Assert(checker != null);
          return Task.FromResult(checker);
        }

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

    private Checker CreateNewChecker()
    {
      var log = Options.ProverLogFilePath;
      if (log != null && !log.Contains("@PROC@") && availableCheckers.Count > 0) {
        log = log + "." + availableCheckers.Count;
      } 

      return new Checker(this, log, Options.ProverLogFileAppend);
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

    public void CheckerDied()
    {
      lock (this) {
        if (checkerWaiters.TryDequeue(out var waiter)) {
          waiter.SetResult(CreateNewChecker());
        } else {
          notCreatedCheckers++;
        }
      }
    }
  }
}