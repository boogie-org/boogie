using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Globalization;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using VCGeneration;
using static VC.ConditionGeneration;

namespace VC
{
  public class SplitAndVerifyWorker
  {

    private readonly VCGenOptions options;
    private readonly VerifierCallback callback;
    private readonly ModelViewInfo mvInfo;
    private readonly ImplementationRun run;

    private readonly int maxKeepGoingSplits;
    public List<Split> ManualSplits { get; }
    private double maxVcCost;

    private bool DoSplitting => ManualSplits.Count > 1 || KeepGoing;
    private bool TrackingProgress => DoSplitting && (callback.OnProgress != null || options.Trace);
    private bool KeepGoing => maxKeepGoingSplits > 1;

    private VcOutcome vcOutcome;
    private double remainingCost;
    private double provenCost;
    private int total;
    private int splitNumber;

    private int totalResourceCount;

    public SplitAndVerifyWorker(
      Program program,
      VCGenOptions options, 
      VerificationConditionGenerator verificationConditionGenerator,
      ImplementationRun run, 
      VerifierCallback callback, 
      ModelViewInfo mvInfo,
      VcOutcome vcOutcome)
    {
      this.options = options;
      this.callback = callback;
      this.mvInfo = mvInfo;
      this.run = run;
      this.vcOutcome = vcOutcome;
      var maxSplits = options.VcsMaxSplits;
      VerificationConditionGenerator.CheckIntAttributeOnImpl(run, "vcs_max_splits", ref maxSplits);

      maxKeepGoingSplits = options.VcsMaxKeepGoingSplits;
      VerificationConditionGenerator.CheckIntAttributeOnImpl(run, "vcs_max_keep_going_splits", ref maxKeepGoingSplits);

      maxVcCost = options.VcsMaxCost;
      var tmpMaxVcCost = -1;
      VerificationConditionGenerator.CheckIntAttributeOnImpl(run, "vcs_max_cost", ref tmpMaxVcCost);
      if (tmpMaxVcCost >= 0)
      {
        maxVcCost = tmpMaxVcCost;
      }


      ResetPredecessors(Implementation.Blocks);
      ManualSplits = ManualSplitFinder.GetParts(options, run,  
        (token, blocks) => new ManualSplit(options, () => blocks, verificationConditionGenerator, run, token)).ToList<Split>();

      if (ManualSplits.Count == 1 && maxSplits > 1)
      {
        ManualSplits = Split.DoSplit(ManualSplits[0], maxVcCost, maxSplits);
        maxVcCost = 1.0;
      }

      splitNumber = DoSplitting ? 0 : -1;
    }

    public async Task<VcOutcome> WorkUntilDone(CancellationToken cancellationToken)
    {
      TrackSplitsCost(ManualSplits);
      await Task.WhenAll(ManualSplits.Select(split => DoWorkForMultipleIterations(split, cancellationToken)));

      return vcOutcome;
    }

    public int ResourceCount => totalResourceCount;

    /// <summary>
    /// The cumulative time spent processing SMT queries.  When running with
    /// `vcsCores > 1`, this may also include time spent restarting the prover.
    /// </summary>
    public TimeSpan TotalProverElapsedTime { get; private set; }

    private void TrackSplitsCost(List<Split> splits)
    {
      if (!TrackingProgress)
      {
        return;
      }

      foreach (var split in splits)
      {
        remainingCost += split.Cost;
        total++;
      }
    }

    async Task DoWorkForMultipleIterations(Split split, CancellationToken cancellationToken)
    {
      int currentSplitNumber = DoSplitting ? Interlocked.Increment(ref splitNumber) - 1 : -1;
      split.SplitIndex = currentSplitNumber;
      var tasks = Enumerable.Range(0, options.RandomizeVcIterations).Select(iteration =>
        DoWork(iteration, split, cancellationToken));
      await Task.WhenAll(tasks);
    }

    async Task DoWork(int iteration, Split split, CancellationToken cancellationToken)
    {
      var checker = await split.parent.CheckerPool.FindCheckerFor(split.parent.program, split, cancellationToken);

      Task beginCheckTask = null;
      // Further splits are verified after the checker is given back, so a failure in them must not give it back again.
      var released = false;
      Task ReleaseChecker()
      {
        if (released)
        {
          return Task.CompletedTask;
        }
        released = true;
        return checker.GoBackToIdle(beginCheckTask);
      }

      try
      {
        cancellationToken.ThrowIfCancellationRequested();
        var timeout = KeepGoing && split.LastChance ? options.VcsFinalAssertTimeout :
          KeepGoing ? options.VcsKeepGoingTimeout :
          run.Implementation.GetTimeLimit(options);
        beginCheckTask = await StartCheck(iteration, split, checker, timeout, cancellationToken);
        var result = await split.WaitForBeginCheck(beginCheckTask, iteration, timeout, callback, cancellationToken);
        if (result == null)
        {
          await checker.ProverTask;
          result = split.ReadOutcome(iteration, checker, callback);
          TotalProverElapsedTime += result.RunTime;
        }
        await ProcessResultAndReleaseChecker(split, checker, result, ReleaseChecker, cancellationToken);
      }
      catch
      {
        await ReleaseChecker();
        throw;
      }
    }

    /// <summary>
    /// Returns the task of the check it begins.
    /// </summary>
    private async Task<Task> StartCheck(int iteration, Split split, Checker checker, uint timeout, CancellationToken cancellationToken)
    {
      if (options.Trace && DoSplitting)
      {
        var splitNum = split.SplitIndex + 1;
        var splitIdxStr = options.RandomizeVcIterations > 1 ? $"{splitNum} (iteration {iteration})" : $"{splitNum}";
        await run.OutputWriter.WriteLineAsync(string.Format(CultureInfo.InvariantCulture, 
            "    checking split {1}/{2}{3}, {4:0.00}%, {0} ...",
            split.Stats, splitIdxStr, total,
            split is ManualSplit manualSplit ? $" (line {manualSplit.Token.line})" : "", 
            100 * provenCost / (provenCost + remainingCost)));
      }

      callback.OnProgress?.Invoke("VCprove", split.SplitIndex, total,
        provenCost / (remainingCost + provenCost));

      return split.BeginCheck(run.OutputWriter, checker, callback, mvInfo, timeout,
        Implementation.GetResourceLimit(options), cancellationToken);
    }

    private Implementation Implementation => run.Implementation;

    private async Task ProcessResultAndReleaseChecker(Split split, Checker checker, VerificationRunResult result,
      Func<Task> releaseChecker, CancellationToken cancellationToken)
    {
      if (TrackingProgress)
      {
        lock (this)
        {
          remainingCost -= split.Cost;
        }
      }

      lock (this)
      {
        vcOutcome = MergeOutcomes(vcOutcome, result.Outcome);
        totalResourceCount += result.ResourceCount;
      }

      var proverFailed = IsProverFailed(result.Outcome);

      if (TrackingProgress)
      {
        lock (this)
        {
          if (proverFailed)
          {
            // even if the prover fails, we have learned something, i.e., it is
            // annoying to watch Boogie say Timeout, 0.00% a couple of times
            provenCost += split.Cost / 100;
          }
          else
          {
            provenCost += split.Cost;
          }
        }
      }

      callback.OnProgress?.Invoke("VCprove", splitNumber < 0 ? 0 : splitNumber, total,
        provenCost / (remainingCost + provenCost));

      if (proverFailed)
      {
        await HandleProverFailure(split, checker, callback, result, releaseChecker, cancellationToken);
      }
      else
      {
        await releaseChecker();
      }
    }

    public static bool IsProverFailed(SolverOutcome outcome)
    {
      switch (outcome)
      {
        case SolverOutcome.Valid:
        case SolverOutcome.Invalid:
        case SolverOutcome.Undetermined:
          return false;
        case SolverOutcome.OutOfMemory:
        case SolverOutcome.TimeOut:
        case SolverOutcome.OutOfResource:
          return true;
        default:
          Contract.Assert(false);
          throw new Cce.UnreachableException();
      }
    }

    private static VcOutcome MergeOutcomes(VcOutcome currentVcOutcome, SolverOutcome newOutcome)
    {
      switch (newOutcome)
      {
        case SolverOutcome.Valid:
          return currentVcOutcome;
        case SolverOutcome.Invalid:
          return VcOutcome.Errors;
        case SolverOutcome.OutOfMemory:
          if (currentVcOutcome != VcOutcome.Errors && currentVcOutcome != VcOutcome.Inconclusive)
          {
            return VcOutcome.OutOfMemory;
          }

          return currentVcOutcome;
        case SolverOutcome.TimeOut:
          if (currentVcOutcome != VcOutcome.Errors && currentVcOutcome != VcOutcome.Inconclusive)
          {
            return VcOutcome.TimedOut;
          }

          return currentVcOutcome;
        case SolverOutcome.OutOfResource:
          if (currentVcOutcome != VcOutcome.Errors && currentVcOutcome != VcOutcome.Inconclusive)
          {
            return VcOutcome.OutOfResource;
          }

          return currentVcOutcome;
        case SolverOutcome.Undetermined:
          if (currentVcOutcome != VcOutcome.Errors)
          {
            return VcOutcome.Inconclusive;
          }

          return currentVcOutcome;
        default:
          Contract.Assert(false);
          throw new Cce.UnreachableException();
      }
    }

    private async Task HandleProverFailure(Split split, Checker checker, VerifierCallback callback,
      VerificationRunResult verificationRunResult, Func<Task> releaseChecker, CancellationToken cancellationToken)
    {
      if (split.LastChance)
      {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } })
        {
          msg = split.reporter.resourceExceededMessage;
        }

        var cex = split.ToCounterexample(checker.TheoremProver.Context);
        callback.OnCounterexample(cex, msg);
        split.Counterexamples.Add(cex);
        // Update one last time the result with the dummy counter-example to indicate the position of the timeout
        var result = verificationRunResult with
        {
          CounterExamples = split.Counterexamples
        };
        vcOutcome = VcOutcome.Errors;
        await releaseChecker();
        return;
      }

      await releaseChecker();

      if (maxKeepGoingSplits > 1)
      {
        var newSplits = Split.DoSplit(split, maxVcCost, maxKeepGoingSplits);
        if (options.Trace)
        {
          await run.OutputWriter.WriteLineAsync($"split {split.SplitIndex + 1} was split into {newSplits.Count} parts");
        }

        Contract.Assert(newSplits != null);
        maxVcCost = 1.0; // for future
        TrackSplitsCost(newSplits);

        if (vcOutcome != VcOutcome.Errors)
        {
          vcOutcome = VcOutcome.Correct;
        }

        await Task.WhenAll(newSplits.Select(newSplit => DoWorkForMultipleIterations(newSplit, cancellationToken)));
        return;
      }

      Contract.Assert(vcOutcome != VcOutcome.Correct);
      if (vcOutcome == VcOutcome.TimedOut)
      {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } })
        {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnTimeout(msg);
      }
      else if (vcOutcome == VcOutcome.OutOfMemory)
      {
        string msg = "out of memory";
        if (split.reporter is { resourceExceededMessage: { } })
        {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnOutOfMemory(msg);
      }
      else if (vcOutcome == VcOutcome.OutOfResource)
      {
        string msg = "out of resource";
        if (split.reporter is { resourceExceededMessage: { } })
        {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnOutOfResource(msg);
      }
    }
  }
}