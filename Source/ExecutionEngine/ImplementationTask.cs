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
    
    VerificationResult verificationResult = engine.GetCachedVerificationResult(Implementation, TextWriter.Null);
    if (verificationResult != null) {
      ActualTask = Task.FromResult(verificationResult);
      CurrentStatus = StatusFromVerificationResult(verificationResult);
    } else {
      CurrentStatus = VerificationStatus.Stale;
      ActualTask = runSource.Task.ContinueWith(t => {

        var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(), null, null,
          Implementation, taskCancellationSource, TextWriter.Null);

        if (!enqueueTask.IsCompleted) {
          CurrentStatus = VerificationStatus.Queued;
        }

        enqueueTask.ContinueWith(_ => {
          CurrentStatus = VerificationStatus.Verifying;
        });

        var result = enqueueTask.Unwrap();
        result.ContinueWith(task => {
          CurrentStatus = StatusFromVerificationResult(task.Result);
          observableStatus.OnCompleted();
        });
        return result;
      }, TaskContinuationOptions.ExecuteSynchronously).Unwrap();
    }
    
  }

  private static VerificationStatus StatusFromVerificationResult(VerificationResult verificationResult)
  {
    return verificationResult.Outcome == ConditionGeneration.Outcome.Correct
      ? VerificationStatus.Correct
      : VerificationStatus.Error;
  }

  public void Run() {
    runSource.SetResult();
  }

  public void Cancel() {
    taskCancellationSource.Cancel();
  }
}

public enum VerificationStatus {
  Stale,
  Queued,
  Verifying,
  Correct,
  Error
}