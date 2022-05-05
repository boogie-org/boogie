using System;
using System.IO;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using VC;

namespace Microsoft.Boogie;

public interface IImplementationTask {
  IObservable<VerificationStatus> ObservableStatus { get; }
  VerificationStatus CurrentStatus { get; }
  ProcessedProgram ProcessedProgram { get; }
  Implementation Implementation { get; }
  Task<VerificationResult> ActualTask { get; }
  void Run();
}

public class ImplementationTask : IImplementationTask {
  private readonly CancellationTokenSource taskCancellationSource;

  private readonly Subject<VerificationStatus> observableStatus = new();
  
  private VerificationStatus currentStatus;
  public IObservable<VerificationStatus> ObservableStatus => observableStatus;

  public VerificationStatus CurrentStatus {
    get => currentStatus;
    private set {
      currentStatus = value;
      observableStatus.OnNext(value);
    }
  }
  public ProcessedProgram ProcessedProgram { get; }

  public Task<VerificationResult> ActualTask { get; }
  public Implementation Implementation { get; }

  private readonly TaskCompletionSource runSource = new();
  
  public ImplementationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Implementation implementation) {
    ProcessedProgram = processedProgram;
    Implementation = implementation;
    taskCancellationSource = new CancellationTokenSource();
    
    var cachedVerificationResult = engine.GetCachedVerificationResult(Implementation, TextWriter.Null);
    if (cachedVerificationResult != null) {
      ActualTask = Task.FromResult(cachedVerificationResult);
      CurrentStatus = VerificationStatus.Completed;
    } else {
      CurrentStatus = VerificationStatus.Stale;
      ActualTask = runSource.Task.ContinueWith(
        _ => VerifyImplementationWithStatusTracking(engine),
        TaskContinuationOptions.ExecuteSynchronously).Unwrap();
    }
  }

  private Task<VerificationResult> VerifyImplementationWithStatusTracking(ExecutionEngine engine)
  {
    var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(), null, null,
      Implementation, taskCancellationSource, TextWriter.Null);

    if (enqueueTask.IsCompleted) {
      CurrentStatus = VerificationStatus.Running;
    } else {
      CurrentStatus = VerificationStatus.Queued;
      enqueueTask.ContinueWith(_ => { CurrentStatus = VerificationStatus.Running; });
    }

    var result = enqueueTask.Unwrap();
    result.ContinueWith(task =>
    {
      CurrentStatus = VerificationStatus.Completed;
      observableStatus.OnCompleted();
    });
    return result;
  }

  public void Run() {
    runSource.SetResult();
  }

  public void Cancel() {
    taskCancellationSource.Cancel();
  }
}

public enum VerificationStatus {
  Stale,      // Not scheduled to be run
  Queued,     // Scheduled to be run but waiting for resources
  Running,    // Currently running
  Completed,  // Results are available
}