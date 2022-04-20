using System;
using System.Collections;
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

    private VCGen vcGen;
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
      this.vcGen = vcGen;
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
      await Task.WhenAll(manualSplits.Select(split => DoWorkForMultipleIterations(split, cancellationToken)));

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

    async Task DoWorkForMultipleIterations(Split split, CancellationToken cancellationToken)
    {
      int currentSplitNumber = DoSplitting ? Interlocked.Increment(ref splitNumber) - 1 : -1;
      split.SplitIndex = currentSplitNumber;
      var tasks = Enumerable.Range(0, options.RandomSeedIterations).Select(iteration =>
        DoWork(iteration, split, cancellationToken));
      await Task.WhenAll(tasks);
    }

    async Task DoWork(int iteration, Split split, CancellationToken cancellationToken)
    {
      var checker = await split.Parent.CheckerPool.FindCheckerFor(split.Parent, split, cancellationToken);

      try {
        cancellationToken.ThrowIfCancellationRequested();
        await StartCheck(iteration, split, checker, cancellationToken);
        await checker.ProverTask;
        await ProcessResult(iteration, split, checker, cancellationToken);
      }
      finally {
        await checker.GoBackToIdle();
      }
    }

    private async Task StartCheck(int iteration, Split split, Checker checker, CancellationToken cancellationToken)
    {
      if (options.Trace && DoSplitting) {
        var splitNum = split.SplitIndex + 1;
        var splitIdxStr = options.RandomSeedIterations > 1 ? $"{splitNum} (iteration {iteration})" : $"{splitNum}";
        Console.WriteLine("    checking split {1}/{2}, {3:0.00}%, {0} ...",
          split.Stats, splitIdxStr, total, 100 * provenCost / (provenCost + remainingCost));
      }

      callback.OnProgress?.Invoke("VCprove", split.SplitIndex, total,
        provenCost / (remainingCost + provenCost));

      var timeout = KeepGoing && split.LastChance ? options.VcsFinalAssertTimeout :
        KeepGoing ? options.VcsKeepGoingTimeout :
        run.Implementation.GetTimeLimit(options);
      await split.BeginCheck(run.TraceWriter, checker, callback, mvInfo, timeout, Implementation.GetResourceLimit(options), cancellationToken);
    }

    private Implementation Implementation => run.Implementation;

    private async Task ProcessResult(int iteration, Split split, Checker checker, CancellationToken cancellationToken)
    {
      if (TrackingProgress) {
        lock (this) {
          remainingCost -= split.Cost;
        }
      }

      var (newOutcome, result, newResourceCount) = await split.ReadOutcome(iteration, checker, callback);
      lock (this) {
        outcome = MergeOutcomes(outcome, newOutcome);
        totalResourceCount += newResourceCount;
      }
      var proverFailed = IsProverFailed(newOutcome);

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
        split.Finish(result);
        return;
      }

      await HandleProverFailure(split, checker, callback, result, cancellationToken);
    }

    private static bool IsProverFailed(ProverInterface.Outcome outcome)
    {
      switch (outcome)
      {
        case ProverInterface.Outcome.Valid:
        case ProverInterface.Outcome.Invalid:
        case ProverInterface.Outcome.Undetermined:
          return false;
        case ProverInterface.Outcome.OutOfMemory:
        case ProverInterface.Outcome.TimeOut:
        case ProverInterface.Outcome.OutOfResource:
          return true;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    private static Outcome MergeOutcomes(Outcome currentOutcome, ProverInterface.Outcome newOutcome)
    {
      switch (newOutcome)
      {
        case ProverInterface.Outcome.Valid:
          return currentOutcome;
        case ProverInterface.Outcome.Invalid:
          return Outcome.Errors;
        case ProverInterface.Outcome.OutOfMemory:
          if (currentOutcome != Outcome.Errors && currentOutcome != Outcome.Inconclusive)
          {
            return Outcome.OutOfMemory;
          }

          return currentOutcome;
        case ProverInterface.Outcome.TimeOut:
          if (currentOutcome != Outcome.Errors && currentOutcome != Outcome.Inconclusive)
          {
            return Outcome.TimedOut;
          }

          return currentOutcome;
        case ProverInterface.Outcome.OutOfResource:
          if (currentOutcome != Outcome.Errors && currentOutcome != Outcome.Inconclusive)
          {
            return Outcome.OutOfResource;
          }

          return currentOutcome;
        case ProverInterface.Outcome.Undetermined:
          if (currentOutcome != Outcome.Errors)
          {
            return Outcome.Inconclusive;
          }
          return currentOutcome;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    private async Task HandleProverFailure(Split split, Checker checker, VerifierCallback callback, VCResult vcResult, CancellationToken cancellationToken)
    {
      if (split.LastChance) {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        var cex = split.ToCounterexample(checker.TheoremProver.Context);
        callback.OnCounterexample(cex, msg);
        split.Counterexamples.Add(cex);
        // Update one last time the result with the dummy counter-example to indicate the position of the timeout
        var result = vcResult with {
          counterExamples = split.Counterexamples
        };
        split.Finish(result);
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
        await Task.WhenAll(newSplits.Select(newSplit => DoWorkForMultipleIterations(newSplit, cancellationToken)));
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
      split.Finish(vcResult);
    }
  }
}
