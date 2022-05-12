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
  void Cancel();
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

  private readonly TaskCompletionSource runWasCalled = new();
  
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
      ActualTask = VerifyImplementationWithStatusTracking(engine);
    }
  }

  private async Task<VerificationResult> VerifyImplementationWithStatusTracking(ExecutionEngine engine) {
    await runWasCalled.Task;

    var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(),
      null, null, Implementation, taskCancellationSource, TextWriter.Null);

    CurrentStatus = enqueueTask.IsCompleted ? VerificationStatus.Running : VerificationStatus.Queued;

    var verifyTask = await enqueueTask;
    if (CurrentStatus != VerificationStatus.Running) {
      CurrentStatus = VerificationStatus.Running;
    }

    var result = await verifyTask;
    CurrentStatus = VerificationStatus.Completed;
    observableStatus.OnCompleted();
    return result;
  }

  public void Run() {
    runWasCalled.SetResult();
  }

  public void Cancel() {
    taskCancellationSource.Cancel();
    runWasCalled.TrySetCanceled(taskCancellationSource.Token);
  }
}

public enum VerificationStatus {
  Stale,      // Not scheduled to be run
  Queued,     // Scheduled to be run but waiting for resources
  Running,    // Currently running
  Completed,  // Results are available
}