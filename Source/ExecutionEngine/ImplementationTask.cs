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
  private ReplaySubject<IVerificationStatus> status;

  public void Cancel() {
    cancellationSource?.Cancel();
  }

  public bool IsIdle => cancellationSource == null;

  /// <summary>
  /// If already running and not cancelled, return null.
  /// If already running but being cancelled, queue a new run and return its observable.
  /// If already running but being cancelled, and a new run is queued, return null;
  /// </summary>
  public IObservable<IVerificationStatus>? TryRun()
  {
    if (CacheStatus is Completed) {
      return null;
    }

    lock (myLock) {
      if (cancellationSource?.IsCancellationRequested == false) {
        return null;
      }

      if (cancellationSource?.IsCancellationRequested == true) {
        cancellationSource = new();
        var result = new Subject<IVerificationStatus>();
        status.Subscribe(next =>
        {

        }, () =>
        {
          var recursiveStatus = TryRun();
          if (recursiveStatus == null) {
            result.OnNext(CacheStatus);
            result.OnCompleted();
          } else {
            recursiveStatus.Subscribe(result);
          }
        });
        return result;
      }
      cancellationSource = new();
    }

    var cancellationToken = cancellationSource.Token;

    status = new ReplaySubject<IVerificationStatus>();
    cancellationToken.Register(() => {
      status.OnNext(new Stale());
    });
    var task = RunInternal(cancellationToken, status.OnNext);
    task.ContinueWith(r =>
    {
      cancellationSource = null;
      if (r.Exception != null) {
        status.OnError(r.Exception);
      } else {
        status.OnCompleted();
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