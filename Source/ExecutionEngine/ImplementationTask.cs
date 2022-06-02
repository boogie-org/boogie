using System;
using System.IO;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

public enum VerificationStatus {
  Stale,      // Not scheduled to be run
  Queued,     // Scheduled to be run but waiting for resources
  Running,    // Currently running
  Completed,  // Results are available
}

public interface IImplementationTask {
  VerificationStatus CacheStatus { get; }
  ProcessedProgram ProcessedProgram { get; }
  Implementation Implementation { get; }
  (Task<VerificationResult>, IObservable<VerificationStatus>) Run(CancellationToken cancellationToken);
}

public class ImplementationTask : IImplementationTask {
  private readonly ExecutionEngine engine;

  public VerificationStatus CacheStatus { get; }

  public ProcessedProgram ProcessedProgram { get; }

  public Implementation Implementation { get; }
  private VerificationResult cachedResult;
  
  public ImplementationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Implementation implementation) {
    this.engine = engine;
    ProcessedProgram = processedProgram;
    Implementation = implementation;
    
    var cachedVerificationResult = engine.GetCachedVerificationResult(Implementation, TextWriter.Null);
    if (cachedVerificationResult != null) {
      cachedResult = cachedVerificationResult;
      CacheStatus = VerificationStatus.Completed;
    } else {
      CacheStatus = VerificationStatus.Stale;
    }
  }

  public (Task<VerificationResult>, IObservable<VerificationStatus>) Run(CancellationToken cancellationToken)
  {
    var observableStatus = new Subject<VerificationStatus>();
    var task = RunInternal(cancellationToken, observableStatus.OnNext);
    task.ContinueWith(r =>
    {
      if (r.Exception != null) {
        observableStatus.OnError(r.Exception);
      } else {
        observableStatus.OnCompleted();
      }
    }, TaskScheduler.Current);
    return (task, observableStatus);
  }

  private async Task<VerificationResult> RunInternal(CancellationToken cancellationToken, Action<VerificationStatus> notifyStatusChange) {

    var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(),
      null, null, Implementation, cancellationToken, TextWriter.Null);

    var afterEnqueueStatus = enqueueTask.IsCompleted ? VerificationStatus.Running : VerificationStatus.Queued;
    notifyStatusChange(afterEnqueueStatus);

    var verifyTask = await enqueueTask;
    if (afterEnqueueStatus != VerificationStatus.Running) {
      notifyStatusChange(VerificationStatus.Running);
    }

    var result = await verifyTask;
    notifyStatusChange(VerificationStatus.Completed);
    return result;
  }
}