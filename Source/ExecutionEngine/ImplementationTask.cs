#nullable enable
using System;
using System.IO;
using System.Reactive.Subjects;
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
  void Cancel();
}

public class ImplementationTask : IImplementationTask {
  private readonly ExecutionEngine engine;

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

  public void Cancel() {
    cancellationSource?.Cancel();
    cancellationSource = null;
  }

  public IObservable<IVerificationStatus>? TryRun()
  {
    if (CacheStatus is Completed) {
      return null;
    }

    var alreadyRunning = cancellationSource != null;
    if (alreadyRunning) {
      return null;
    }
    cancellationSource = new();
    var cancellationToken = cancellationSource.Token;

    var observableStatus = new ReplaySubject<IVerificationStatus>();
    cancellationToken.Register(() => {
      observableStatus.OnNext(new Stale());
      observableStatus.OnCompleted();
    });
    var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(),
      null, null, Implementation, cancellationToken, TextWriter.Null);
    var task = RunInternal(enqueueTask, observableStatus.OnNext);
    task.ContinueWith(r =>
    {
      if (r.Exception != null) {
        observableStatus.OnError(r.Exception);
      } else {
        observableStatus.OnCompleted();
      }
    }, TaskScheduler.Current);
    return observableStatus;
  }

  private async Task<VerificationResult> RunInternal(
    Task<Task<VerificationResult>> enqueueTask,
    Action<IVerificationStatus> notifyStatusChange) {

    var afterEnqueueStatus = enqueueTask.IsCompleted ? (IVerificationStatus)new Running() : new Queued();
    if (enqueueTask.IsCompleted) {
      Console.WriteLine("sending running for " + Implementation.Name);
    }
    notifyStatusChange(afterEnqueueStatus);

    var verifyTask = await enqueueTask;
    if (afterEnqueueStatus is not Running) {
      Console.WriteLine("sending running for " + Implementation.Name);
      notifyStatusChange(new Running());
    }

    var result = await verifyTask;
    CacheStatus = new Completed(result);
    cancellationSource = null;
    notifyStatusChange(CacheStatus);
    return result;
  }
}