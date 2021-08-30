using System;
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
      
    private bool DoSplitting => manualSplits.Count > 1 || KeepGoing || maxSplits > 1;
      
    private Outcome outcome;
    private int runningSplits;
    private double remainingCost;
    private double provenCost;
    private int total = 0;
    private int splitNumber;
    private bool proverFailed;
    private bool halted;
    private bool firstRound = true;
    private readonly List<Split> manualSplits;

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
      manualSplits = Split.FocusAndSplit(implementation, gotoCmdOrigins, vcGen);

      splitNumber = maxSplits == 1 && !KeepGoing ? -1 : 0;
    }

    public Task<Outcome> WorkUntilDone()
    {
      TrackSplitsCost(manualSplits);
      foreach (var manualSplit in manualSplits) {
        DoWork(manualSplit);
      }
      CheckEnd();

      return tcs.Task;
    }

    private void TrackSplitsCost(List<Split> splits)
    {
      foreach (var split in splits) {
        remainingCost += split.Cost;
        total++;
      }
    }

    private void CheckEnd()
    {
      lock (this) {
        if (halted || runningSplits == 0)
        {
          tcs.TrySetResult(outcome);
        }
      }
    }

    async void DoWork(Split split)
    {
      Interlocked.Increment(ref runningSplits);
      Checker checker;
      try {
        checker = await split.parent.CheckerPool.FindCheckerFor(split.parent, split);
      }
      catch (Exception e) {
        tcs.SetException(e);
        halted = true;
        return;
      }
      
      try {
        proverFailed = false;
        StartCheck(split, checker);
        await split.ProverTask;
        ProcessResult(split);
      }
      finally {
        split.ReleaseChecker();
        Interlocked.Decrement(ref runningSplits);
        CheckEnd();
      }
    }

    private void StartCheck(Split split, Checker checker)
    {
      int currentSplitNumber = DoSplitting ? Interlocked.Increment(ref splitNumber) : -1;
      if (CommandLineOptions.Clo.Trace && splitNumber >= 0) {
        Console.WriteLine("    checking split {1}/{2}, {3:0.00}%, {0} ...",
          split.Stats, splitNumber + 1, total, 100 * provenCost / (provenCost + remainingCost));
      }

      callback.OnProgress("VCprove", splitNumber < 0 ? 0 : splitNumber, total,
        provenCost / (remainingCost + provenCost));

      var timeout = KeepGoing && split.LastChance ? CommandLineOptions.Clo.VcsFinalAssertTimeout :
        KeepGoing ? CommandLineOptions.Clo.VcsKeepGoingTimeout :
        implementation.TimeLimit;
      split.BeginCheck(checker, callback, mvInfo, currentSplitNumber, timeout, implementation.ResourceLimit);
    }

    private void ProcessResult(Split split)
    {
      lock (this) {
        remainingCost -= split.Cost;
      }

      lock (split.Checker) {
        split.ReadOutcome(ref outcome, out proverFailed);
      }

      lock (this) {
        if (proverFailed) {
          // even if the prover fails, we have learned something, i.e., it is
          // annoying to watch Boogie say Timeout, 0.00% a couple of times
          provenCost += split.Cost / 100;
        } else {
          provenCost += split.Cost;
        }
      }

      callback.OnProgress("VCprove", splitNumber < 0 ? 0 : splitNumber, total, provenCost / (remainingCost + provenCost));

      if (proverFailed && !firstRound && split.LastChance) {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnCounterexample(split.ToCounterexample(split.Checker.TheoremProver.Context), msg);
        outcome = Outcome.Errors;
        halted = true;
        return;
      }
      
      if (proverFailed)
      {
        int currentMaxSplits = firstRound && maxSplits > 1 ? maxSplits : maxKeepGoingSplits;

        if (currentMaxSplits > 1)
        {
          var newSplits = Split.DoSplit(split, maxVcCost, currentMaxSplits);
          Contract.Assert(newSplits != null);
          maxVcCost = 1.0; // for future
          firstRound = false;
          TrackSplitsCost(newSplits);
          foreach (Split newSplit in newSplits)
          {
            Contract.Assert(newSplit != null);
            DoWork(newSplit);
          }
          Interlocked.Decrement(ref runningSplits);

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
            if (split.reporter is { resourceExceededMessage: { } })
            {
              msg = split.reporter.resourceExceededMessage;
            }

            callback.OnTimeout(msg);
          }
          else if (outcome == Outcome.OutOfMemory)
          {
            string msg = "out of memory";
            if (split.reporter is { resourceExceededMessage: { } })
            {
              msg = split.reporter.resourceExceededMessage;
            }

            callback.OnOutOfMemory(msg);
          }
          else if (outcome == Outcome.OutOfResource)
          {
            string msg = "out of resource";
            if (split.reporter is { resourceExceededMessage: { } })
            {
              msg = split.reporter.resourceExceededMessage;
            }

            callback.OnOutOfResource(msg);
          }

          halted = true;
        }
      }
    }
  }
}