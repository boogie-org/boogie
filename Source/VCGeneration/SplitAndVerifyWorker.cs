using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using static VC.ConditionGeneration;

namespace VC
{
  class SplitAndVerifyWorker
  {
    private readonly VerifierCallback callback;
    private readonly ModelViewInfo mvInfo;
    private readonly Implementation implementation;
    private bool KeepGoing => maxKeepGoingSplits > 1;
    private readonly TaskCompletionSource<Outcome> tcs = new();
      
    private readonly int maxSplits;
    private readonly int maxKeepGoingSplits;
    private double maxVcCost;
      
    private bool DoSplitting => KeepGoing || maxSplits > 1;
      
    private Outcome outcome;
    private readonly Stack<Split> remainingWork;
    private int runningSplits;
    private double remainingCost;
    private double provenCost;
    private int total = 0;
    private int splitNumber;
    private bool proverFailed;
    private bool halted;
    private bool firstRound = true;

    public SplitAndVerifyWorker(VCGen vcGen, Implementation implementation,
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VerifierCallback callback, ModelViewInfo mvInfo,
      Outcome outcome)
    {
      this.callback = callback;
      this.mvInfo = mvInfo;
      this.implementation = implementation;
      this.outcome = outcome;
      
      maxSplits = CommandLineOptions.Clo.VcsMaxSplits;
      VCGen.CheckIntAttributeOnImpl(implementation, "vcs_max_splits", ref maxSplits);
      
      maxKeepGoingSplits = CommandLineOptions.Clo.VcsMaxKeepGoingSplits;
      VCGen.CheckIntAttributeOnImpl(implementation, "vcs_max_keep_going_splits", ref maxKeepGoingSplits);
      
      maxVcCost = CommandLineOptions.Clo.VcsMaxCost;
      var tmpMaxVcCost = -1;
      VCGen.CheckIntAttributeOnImpl(implementation, "vcs_max_cost", ref tmpMaxVcCost);
      if (tmpMaxVcCost >= 0) maxVcCost = tmpMaxVcCost;

      ResetPredecessors(implementation.Blocks);
      var manualSplits = Split.FocusAndSplit(implementation, gotoCmdOrigins, vcGen);
      remainingWork = new(manualSplits);

      splitNumber = maxSplits == 1 && !KeepGoing ? -1 : 0;

      if (DoSplitting) {
        if (remainingWork.TryPeek(out var split)) {
          remainingCost = split.Cost;
        }
      }
    }

    public Task<Outcome> WorkUntilDone()
    {
      while (TryDoWork()) {
      }
      CheckEnd();

      return tcs.Task;
    }

    private bool TryDoWork()
    {
      Split nextSplit;
      lock (this) {
        if (!remainingWork.TryPop(out nextSplit)) {
          return false;
        }

        runningSplits++;
      }

      // if (firstRound && maxSplits > 1)
      // {
      //   proverFailed = true;
      //   remainingCost -= nextSplit.Cost;
      // }
      
      var checker = nextSplit.parent.CheckerPool.FindCheckerFor(nextSplit.parent, false, nextSplit);
      if (checker == null) {
        lock (this) {
          remainingWork.Push(nextSplit);
          runningSplits--;
        }
        return false;
      }

      DoWork(nextSplit, checker).ContinueWith(_ => { });
      return true;
    }

    private void CheckEnd()
    {
      lock (this) {
        if (halted || (remainingWork.Count == 0 && runningSplits == 0))
        {
          tcs.TrySetResult(outcome);
        }
      }
    }

    async Task DoWork(Split nextSplit, Checker checker)
    {
      try {
        proverFailed = false;
        // if (firstRound && maxSplits > 1)
        // {
        //   proverFailed = true;
        //   remainingCost -= nextSplit.Cost;
        // }
        StartCheck(nextSplit, checker);
        await nextSplit.ProverTask;
        ProcessResult(nextSplit);
      }
      finally
      {
        nextSplit.Checker.GoBackToIdle();
        Interlocked.Decrement(ref runningSplits);
        CheckEnd();
        TryDoWork();
      }
    }

    private void StartCheck(Split nextSplit, Checker checker)
    {
      int currentSplitNumber = Interlocked.Increment(ref splitNumber) - 1;
      if (CommandLineOptions.Clo.Trace && splitNumber >= 0) {
        Console.WriteLine("    checking split {1}/{2}, {3:0.00}%, {0} ...",
          nextSplit.Stats, splitNumber + 1, total, 100 * provenCost / (provenCost + remainingCost));
      }

      callback.OnProgress("VCprove", splitNumber < 0 ? 0 : splitNumber, total,
        provenCost / (remainingCost + provenCost));

      var timeout = KeepGoing && nextSplit.LastChance ? CommandLineOptions.Clo.VcsFinalAssertTimeout :
        KeepGoing ? CommandLineOptions.Clo.VcsKeepGoingTimeout :
        implementation.TimeLimit;
      nextSplit.BeginCheck(checker, callback, mvInfo, currentSplitNumber, timeout, implementation.ResourceLimit);
    }

    private void ProcessResult(Split nextSplit)
    {
      if (DoSplitting) {
        remainingCost -= nextSplit.Cost;
      }

      lock (nextSplit.Checker) {
        nextSplit.ReadOutcome(ref outcome, out proverFailed);
      }

      if (DoSplitting) {
        if (proverFailed) {
          // even if the prover fails, we have learned something, i.e., it is
          // annoying to watch Boogie say Timeout, 0.00% a couple of times
          provenCost += nextSplit.Cost / 100;
        } else {
          provenCost += nextSplit.Cost;
        }
      }

      callback.OnProgress("VCprove", splitNumber < 0 ? 0 : splitNumber, total, provenCost / (remainingCost + provenCost));

      if (proverFailed && !firstRound && nextSplit.LastChance) {
        string msg = "some timeout";
        if (nextSplit.reporter is { resourceExceededMessage: { } }) {
          msg = nextSplit.reporter.resourceExceededMessage;
        }

        callback.OnCounterexample(nextSplit.ToCounterexample(nextSplit.Checker.TheoremProver.Context), msg);
        outcome = Outcome.Errors;
        halted = true;
        return;
      }
      
      if (proverFailed)
      {
        int splits = firstRound && maxSplits > 1 ? maxSplits : maxKeepGoingSplits;

        if (splits > 1)
        {
          List<Split> tmp = Split.DoSplit(nextSplit, maxVcCost, splits);
          Contract.Assert(tmp != null);
          maxVcCost = 1.0; // for future
          firstRound = false;
          //tmp.Sort(new Comparison<Split!>(Split.Compare));
          lock (this) {
            foreach (Split a in tmp)
            {
              Contract.Assert(a != null);
              remainingWork.Push(a);
              total++;
              remainingCost += a.Cost;
            }
            runningSplits--;
          }

          if (outcome != Outcome.Errors)
          {
            outcome = Outcome.Correct;
          }
        }
        else
        {
          Contract.Assert(outcome != Outcome.Correct);
          if (outcome == Outcome.TimedOut)
          {
            string msg = "some timeout";
            if (nextSplit.reporter is { resourceExceededMessage: { } })
            {
              msg = nextSplit.reporter.resourceExceededMessage;
            }

            callback.OnTimeout(msg);
          }
          else if (outcome == Outcome.OutOfMemory)
          {
            string msg = "out of memory";
            if (nextSplit.reporter != null && nextSplit.reporter.resourceExceededMessage != null)
            {
              msg = nextSplit.reporter.resourceExceededMessage;
            }

            callback.OnOutOfMemory(msg);
          }
          else if (outcome == Outcome.OutOfResource)
          {
            string msg = "out of resource";
            if (nextSplit.reporter != null && nextSplit.reporter.resourceExceededMessage != null)
            {
              msg = nextSplit.reporter.resourceExceededMessage;
            }

            callback.OnOutOfResource(msg);
          }

          halted = true;
        }
      }
    }
  }
}