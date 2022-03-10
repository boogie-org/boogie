using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using static VC.ConditionGeneration;

namespace VC
{
  class SplitAndVerifyWorker
  {
    private readonly VCGenOptions options;
    private readonly VerifierCallback callback;
    private readonly ModelViewInfo mvInfo;
    private readonly ImplementationRun run;
      
    private readonly int maxKeepGoingSplits;
    private readonly List<Split> manualSplits;
    private double maxVcCost;
    private readonly bool splitOnEveryAssert;
      
    private bool DoSplitting => manualSplits.Count > 1 || KeepGoing || splitOnEveryAssert;
    private bool TrackingProgress => DoSplitting && (callback.OnProgress != null || options.Trace); 
    private bool KeepGoing => maxKeepGoingSplits > 1;
      
    private Outcome outcome;
    private double remainingCost;
    private double provenCost;
    private int total;
    private int splitNumber;

    private int totalResourceCount;
    
    public SplitAndVerifyWorker(VCGenOptions options, VCGen vcGen, ImplementationRun run,
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VerifierCallback callback, ModelViewInfo mvInfo,
      Outcome outcome)
    {
      this.options = options;
      this.callback = callback;
      this.mvInfo = mvInfo;
      this.run = run;
      this.outcome = outcome;

      var maxSplits = options.VcsMaxSplits;
      VCGen.CheckIntAttributeOnImpl(Implementation, "vcs_max_splits", ref maxSplits);
      
      maxKeepGoingSplits = options.VcsMaxKeepGoingSplits;
      VCGen.CheckIntAttributeOnImpl(Implementation, "vcs_max_keep_going_splits", ref maxKeepGoingSplits);
      
      maxVcCost = options.VcsMaxCost;
      var tmpMaxVcCost = -1;
      VCGen.CheckIntAttributeOnImpl(Implementation, "vcs_max_cost", ref tmpMaxVcCost);
      if (tmpMaxVcCost >= 0)
      {
        maxVcCost = tmpMaxVcCost;
      }
      
      splitOnEveryAssert = options.VcsSplitOnEveryAssert;
      Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);

      ResetPredecessors(Implementation.Blocks);
      manualSplits = Split.FocusAndSplit(options, Implementation, gotoCmdOrigins, vcGen, splitOnEveryAssert);
      
      if (manualSplits.Count == 1 && maxSplits > 1) {
        manualSplits = Split.DoSplit(manualSplits[0], maxVcCost, maxSplits);
        maxVcCost = 1.0;
      }
      
      splitNumber = DoSplitting ? 0 : -1;
    }

    public async Task<Outcome> WorkUntilDone(CancellationToken cancellationToken)
    {
      TrackSplitsCost(manualSplits);
      await Task.WhenAll(manualSplits.Select(split => DoWork(split, cancellationToken)));

      return outcome;
    }

    public int ResourceCount => totalResourceCount;
    
    private void TrackSplitsCost(List<Split> splits)
    {
      if (!TrackingProgress)
      {
        return;
      }

      foreach (var split in splits) {
        remainingCost += split.Cost;
        total++;
      }
    }

    async Task DoWork(Split split, CancellationToken cancellationToken)
    {
      var checker = await split.parent.CheckerPool.FindCheckerFor(split.parent, split);

      try {
        cancellationToken.ThrowIfCancellationRequested();
        StartCheck(split, checker, cancellationToken);
        await split.ProverTask;
        await ProcessResult(split, cancellationToken);
      }
      finally {
        split.ReleaseChecker();
      }
    }

    private void StartCheck(Split split, Checker checker, CancellationToken cancellationToken)
    {
      int currentSplitNumber = DoSplitting ? Interlocked.Increment(ref splitNumber) - 1 : -1;
      if (options.Trace && DoSplitting) {
        Console.WriteLine("    checking split {1}/{2}, {3:0.00}%, {0} ...",
          split.Stats, currentSplitNumber + 1, total, 100 * provenCost / (provenCost + remainingCost));
      }

      callback.OnProgress?.Invoke("VCprove", currentSplitNumber, total,
        provenCost / (remainingCost + provenCost));

      var timeout = KeepGoing && split.LastChance ? options.VcsFinalAssertTimeout :
        KeepGoing ? options.VcsKeepGoingTimeout :
        run.Implementation.GetTimeLimit(options);
      split.BeginCheck(run.TraceWriter, checker, callback, mvInfo, currentSplitNumber, timeout, Implementation.GetResourceLimit(options), cancellationToken);
    }

    private Implementation Implementation => run.Implementation;

    private async Task ProcessResult(Split split, CancellationToken cancellationToken)
    {
      if (TrackingProgress) {
        lock (this) {
          remainingCost -= split.Cost;
        }
      }

      split.ReadOutcome(callback, ref outcome, out var proverFailed, ref totalResourceCount);

      if (TrackingProgress) {
        lock (this) {
          if (proverFailed) {
            // even if the prover fails, we have learned something, i.e., it is
            // annoying to watch Boogie say Timeout, 0.00% a couple of times
            provenCost += split.Cost / 100;
          } else {
            provenCost += split.Cost;
          }
        }
      }

      callback.OnProgress?.Invoke("VCprove", splitNumber < 0 ? 0 : splitNumber, total, provenCost / (remainingCost + provenCost));

      if (!proverFailed) {
        return;
      }

      await HandleProverFailure(split, cancellationToken);
    }

    private async Task HandleProverFailure(Split split, CancellationToken cancellationToken)
    {
      if (split.LastChance) {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnCounterexample(split.ToCounterexample(split.Checker.TheoremProver.Context), msg);
        outcome = Outcome.Errors;
        return;
      }

      if (maxKeepGoingSplits > 1) {
        var newSplits = Split.DoSplit(split, maxVcCost, maxKeepGoingSplits);
        Contract.Assert(newSplits != null);
        maxVcCost = 1.0; // for future
        TrackSplitsCost(newSplits);
        
        if (outcome != Outcome.Errors) {
          outcome = Outcome.Correct;
        }
        await Task.WhenAll(newSplits.Select(newSplit => DoWork(newSplit, cancellationToken)));
        return;
      }

      Contract.Assert(outcome != Outcome.Correct);
      if (outcome == Outcome.TimedOut) {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnTimeout(msg);
      } else if (outcome == Outcome.OutOfMemory) {
        string msg = "out of memory";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnOutOfMemory(msg);
      } else if (outcome == Outcome.OutOfResource) {
        string msg = "out of resource";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnOutOfResource(msg);
      }
    }
  }
}
