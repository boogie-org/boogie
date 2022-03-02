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
    private readonly Implementation implementation;
      
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
    
    public SplitAndVerifyWorker(VCGenOptions options, VCGen vcGen, Implementation implementation,
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VerifierCallback callback, ModelViewInfo mvInfo,
      Outcome outcome)
    {
      this.options = options;
      this.callback = callback;
      this.mvInfo = mvInfo;
      this.implementation = implementation;
      this.outcome = outcome;
      this.vcGen = vcGen;
      
      var maxSplits = options.VcsMaxSplits;
      VCGen.CheckIntAttributeOnImpl(implementation, "vcs_max_splits", ref maxSplits);
      
      maxKeepGoingSplits = options.VcsMaxKeepGoingSplits;
      VCGen.CheckIntAttributeOnImpl(implementation, "vcs_max_keep_going_splits", ref maxKeepGoingSplits);
      
      maxVcCost = options.VcsMaxCost;
      var tmpMaxVcCost = -1;
      VCGen.CheckIntAttributeOnImpl(implementation, "vcs_max_cost", ref tmpMaxVcCost);
      if (tmpMaxVcCost >= 0)
      {
        maxVcCost = tmpMaxVcCost;
      }
      
      splitOnEveryAssert = options.VcsSplitOnEveryAssert;
      implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);

      ResetPredecessors(implementation.Blocks);
      manualSplits = Split.FocusAndSplit(options, implementation, gotoCmdOrigins, vcGen, splitOnEveryAssert);
      
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
        implementation.GetTimeLimit(options);
      split.BeginCheck(checker, callback, mvInfo, currentSplitNumber, timeout, implementation.GetResourceLimit(options), cancellationToken);
    }

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
        if (callback is VerificationResultCollector collector) {
          List<AssertCmd> asserts = split.blocks.SelectMany(block => block.cmds.OfType<AssertCmd>()).ToList();
          Dictionary<AssertCmd, Outcome> perAssertOutcome = new();
          Dictionary<AssertCmd, Counterexample> perAssertCounterExamples = new();
          if (outcome == Outcome.Correct) {
            perAssertOutcome = asserts.ToDictionary(cmd => cmd, assertCmd => Outcome.Correct);
          } else {
            foreach (var counterExample in collector.examples) {
              // Only deal with the ocunter-examples that cover the asserts of this split.
              AssertCmd underlyingAssert;
              if (counterExample is AssertCounterexample assertCounterexample) {
                underlyingAssert = assertCounterexample.FailingAssert;
              } else if (counterExample is CallCounterexample callCounterexample) {
                underlyingAssert = callCounterexample.UnderlyingAssert;
              } else if (counterExample is ReturnCounterexample returnCounterexample) {
                underlyingAssert = returnCounterexample.UnderlyingAssert;
              } else {
                continue;
              }
              if (!asserts.Contains(underlyingAssert)) {
                continue;
              }
              perAssertOutcome.Add(underlyingAssert, Outcome.Errors);
              perAssertCounterExamples.Add(underlyingAssert, counterExample);
            }

            var remainingOutcome =
              outcome == Outcome.Errors && collector.examples.Count != split.Checker.Options.ErrorLimit
                ? Outcome.Correct
                : Outcome.Inconclusive;
            // Everything not listed is successful
            foreach (var assert in asserts)
            {
              perAssertOutcome.TryAdd(assert, remainingOutcome);
            }
          }
          split.parent.Logger?.ReportAssertionBatchResult(split, perAssertOutcome, perAssertCounterExamples);
        }
        return;
      }

      await HandleProverFailure(split, cancellationToken);
    }

    private async Task HandleProverFailure(Split split, CancellationToken cancellationToken)
    {
      Dictionary<AssertCmd, Outcome> perAssertOutcome;
      if (split.LastChance) {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }
        callback.OnCounterexample(split.ToCounterexample(split.Checker.TheoremProver.Context), msg);
        perAssertOutcome = split.blocks.SelectMany(block => block.cmds.OfType<AssertCmd>()).ToDictionary(assertCmd => assertCmd, assertCmd => outcome);
        split.parent.Logger?.ReportAssertionBatchResult(split, perAssertOutcome, new ());
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
      perAssertOutcome = split.blocks.SelectMany(block => block.cmds.OfType<AssertCmd>()).ToDictionary(assertCmd => assertCmd, assertCmd => outcome);
      split.parent.Logger?.ReportAssertionBatchResult(split, perAssertOutcome, new());
    }
  }
}