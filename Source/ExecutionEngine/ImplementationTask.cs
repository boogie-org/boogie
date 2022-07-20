#nullable enable
using System;
using System.IO;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

public interface IVerificationStatus {}

/// <summary>
/// Results are available
/// </summary>
public record Completed(VerificationResult Result) : IVerificationStatus;

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

public interface IImplementationTask {
  IVerificationStatus CacheStatus { get; }

  ProcessedProgram ProcessedProgram { get; }
  Implementation Implementation { get; }

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

public class ImplementationTask : IImplementationTask {
  private readonly ExecutionEngine engine;
  private readonly object myLock = new();

  public IVerificationStatus CacheStatus { get; private set; }

  public ProcessedProgram ProcessedProgram { get; }

  public Implementation Implementation { get; }
  
  public ImplementationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Implementation implementation) {
    this.engine = engine;
    ProcessedProgram = processedProgram;
    Implementation = implementation;
    
    var cachedVerificationResult = engine.GetCachedVerificationResult(Implementation, TextWriter.Null);
    if (cachedVerificationResult != null) {
      CacheStatus = new Completed(cachedVerificationResult);
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
    // Lock to prevent conflicts from concurrent calls to TryRun
    lock (myLock) {
      if (cancellationSource == null) {
        // No other thread was running, we claim the right to run.
        cancellationSource = new();
      } else if (!cancellationSource.IsCancellationRequested) {
        // Another thread is running and is not cancelled, so this run fails.
        return null;
      } else {
        // Another thread is running but was cancelled,
        // so we may immediately start a new run after the cancellation completes.

        // We claim the right to run.
        cancellationSource = new();

        // After the current run cancellation completes, call TryRun, assume it succeeds, and forward the observations
        // to result.
        var result = new ReplaySubject<IVerificationStatus>();
        status!.Subscribe(next => { }, () => {
          var recursiveStatus = TryRun();
          if (recursiveStatus == null) {
            throw new InvalidOperationException("Should not be possible.");
          }

          recursiveStatus.Subscribe(result);
        });
        return result;
      }

      if (cancellationSource?.IsCancellationRequested == true) {
      }
      cancellationSource = new();
    }

    // We claimed the right to run. No other thread is running nor can they get to this point,
    // so from this point we can read and write from and to the fields CacheStatus and status as if we're the only thread.

    if (CacheStatus is Completed) {
      cancellationSource = null;
      return null;
    }

    var cancellationToken = cancellationSource.Token;

    status = new ReplaySubject<IVerificationStatus>();
    cancellationToken.Register(() => {
      status.OnNext(new Stale());
    });
    var task = RunInternal(cancellationToken, status.OnNext);
    task.ContinueWith(r =>
    {
      // Lock so we may do operations after clearing cancellationSource,
      // which releases our control over the field status.
      lock (myLock) {
        // Clear cancellationSource before calling status.OnCompleted, so ImplementationTask.IsIdle return false
        cancellationSource = null;
        if (r.Exception != null) {
          status.OnError(r.Exception);
        } else {
          status.OnCompleted();
        }
      }
    }, TaskScheduler.Current);
    return status;
  }

  private async Task<VerificationResult> RunInternal(CancellationToken cancellationToken, Action<IVerificationStatus> notifyStatusChange) {

    var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(),
      null, null, Implementation, cancellationToken, TextWriter.Null);

    var afterEnqueueStatus = enqueueTask.IsCompleted ? (IVerificationStatus)new Running() : new Queued();
    notifyStatusChange(afterEnqueueStatus);

    var verifyTask = await enqueueTask;
    if (afterEnqueueStatus is not Running) {
      notifyStatusChange(new Running());
    }

    var result = await verifyTask;
    CacheStatus = new Completed(result);
    notifyStatusChange(CacheStatus);
    return result;
  }
}