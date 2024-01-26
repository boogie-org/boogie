#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Runtime.CompilerServices;
using System.Threading;
using VC;

namespace Microsoft.Boogie;

public interface IVerificationStatus {}

/// <summary>
/// Results are available
/// </summary>
public record Completed(VerificationRunResult Result) : IVerificationStatus;

/// <summary>
/// Scheduled to be run but waiting for resources
/// </summary>
public record Queued : IVerificationStatus;

/// <summary>
/// Not scheduled to be run
/// </summary>
public record Stale : IVerificationStatus;

/// <summary>
/// Currently being run
/// </summary>
public record Running : IVerificationStatus;

public record BatchCompleted(Split Split, VerificationRunResult VerificationRunResult) : IVerificationStatus;

public interface IVerificationTask {
  IVerificationStatus CacheStatus { get; }

  ProcessedProgram ProcessedProgram { get; }
  Split Split { get; }

  /// <summary>
  /// If not running, start running.
  /// If already running and not cancelled, return null.
  /// If already running but being cancelled, queue a new run and return its observable.
  /// If already running but being cancelled, and a new run is queued, return null.
  /// </summary>
  IObservable<IVerificationStatus>? TryRun();
  bool IsIdle { get; }
  void Cancel();
}

public class VerificationTask : IVerificationTask {
  private readonly ExecutionEngine engine;
  private readonly ModelViewInfo modelViewInfo;
  private readonly object mayAccessCancellationSource = new();

  public IVerificationStatus CacheStatus { get; private set; }

  public ProcessedProgram ProcessedProgram { get; }

  public Split Split { get; }
  
  public VerificationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Split split,
    ModelViewInfo modelViewInfo) 
  {
    this.engine = engine;
    this.modelViewInfo = modelViewInfo;
    ProcessedProgram = processedProgram;
    Split = split;
    
    var cachedVerificationResult = engine.GetCachedVerificationResult(split.Implementation, TextWriter.Null);
    if (cachedVerificationResult != null) {
      CacheStatus = new Completed(cachedVerificationResult.RunResults[Split.SplitIndex]);
    } else {
      CacheStatus = new Stale();
    }
  }

  private CancellationTokenSource? cancellationSource;
  private ReplaySubject<IVerificationStatus>? status;

  public void Cancel() {
    cancellationSource?.Cancel();
  }

  public bool IsIdle => cancellationSource == null;

  public IObservable<IVerificationStatus>? TryRun()
  {
    lock (mayAccessCancellationSource) {
      if (cancellationSource == null) {
        return StartRunIfNeeded();
      }

      if (cancellationSource.IsCancellationRequested) {
        // Another thread is running but was cancelled,
        // so we may immediately start a new run after the cancellation completes.
        return QueueRun();
      }

      // Another thread is running and is not cancelled, so this run fails.
      return null;
    }
  }

  private IObservable<IVerificationStatus>? StartRunIfNeeded()
  {
    // No other thread is running or can start, so we can safely access CacheStatus
    if (CacheStatus is Completed) {
      return null;
    }

    // We claim the right to run.
    cancellationSource = new();

    status = new ReplaySubject<IVerificationStatus>();

    StartRun(cancellationSource.Token).ToObservable().
      Catch<IVerificationStatus, OperationCanceledException>(_ => Observable.Return(new Stale())).
      Subscribe(next =>
    {
      status.OnNext(next);
    }, e =>
    {
      // Lock so we may do operations after clearing cancellationSource,
      // which releases our control over the field status.
      lock (mayAccessCancellationSource)
      {
        // Clear cancellationSource before calling status.OnError, so ImplementationTask.IsIdle returns true
        cancellationSource = null;
        status.OnError(e);
      }
    }, () =>
    {
      // Lock so we may do operations after clearing cancellationSource,
      // which releases our control over the field status.
      lock (mayAccessCancellationSource)
      {
        // Clear cancellationSource before calling status.OnCompleted, so ImplementationTask.IsIdle returns true
        cancellationSource = null;

        status.OnCompleted();
      }
    });

    return status;
  }

  private async IAsyncEnumerable<IVerificationStatus> StartRun([EnumeratorCancellation] CancellationToken cancellationToken)
  {
    var timeout = Split.Run.Implementation.GetTimeLimit(Split.Options);
    
    var checkerTask = engine.CheckerPool.FindCheckerFor(ProcessedProgram.Program, Split, CancellationToken.None);
    if (!checkerTask.IsCompleted)
    {
      yield return new Queued();
    }
    var checker = await checkerTask;
    try
    {
      yield return new Running();

      var verifierCallback = new VerifierCallback(CoreOptions.ProverWarnings.None);
      await Split.BeginCheck(Split.Run.OutputWriter, checker, verifierCallback,
        modelViewInfo, timeout, Split.Run.Implementation.GetResourceLimit(Split.Options), cancellationToken);

      await checker.ProverTask;
      var result = Split.ReadOutcome(0, checker, verifierCallback);

      if (SplitAndVerifyWorker.IsProverFailed(result.Outcome))
      {
        // Update one last time the result with the dummy counter-example to indicate the position of the failure
        var cex = Split.ToCounterexample(checker.TheoremProver.Context);
        Split.Counterexamples.Add(cex);
        result = result with
        {
          CounterExamples = Split.Counterexamples
        };
      }
      CacheStatus = new Completed(result);
      yield return CacheStatus;
    }
    finally
    {
      await checker.GoBackToIdle();
    }
  }

  private IObservable<IVerificationStatus> QueueRun()
  {
    // We claim the right to run.
    cancellationSource = new();
    var myCancellationSource = cancellationSource;

    // After the current run cancellation completes, call TryRun, assume it succeeds,
    // and forward the observations to result.
    var result = new ReplaySubject<IVerificationStatus>();
    status!.Subscribe(next => { }, () =>
    {
      if (myCancellationSource.IsCancellationRequested) {
        // Queued run was cancelled before it started.
        result.OnNext(CacheStatus);
        result.OnCompleted();
      } else {
        // The running thread has just cleared cancellationSource, so TryRun will return a non-null value.
        var recursiveStatus = TryRun();
        recursiveStatus!.Subscribe(result);
        // Forward cancellation requests that happened between our
        // myCancellationSource.IsCancellationRequested check and TryRun call
        myCancellationSource.Token.Register(() => cancellationSource.Cancel());
      }
    });
    return result;
  }
}
