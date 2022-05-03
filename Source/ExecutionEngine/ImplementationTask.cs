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
  void InitialiseStatus();
}

public class ImplementationTask : IImplementationTask {
  private readonly CancellationTokenSource taskCancellationSource;

  private readonly ReplaySubject<VerificationStatus> observableStatus = new();
  
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
        CurrentStatus = task.Result.Outcome == ConditionGeneration.Outcome.Correct
          ? VerificationStatus.Correct
          : VerificationStatus.Error;
        observableStatus.OnCompleted();
      });
      return result;
    }, TaskContinuationOptions.ExecuteSynchronously).Unwrap();
  }

  public void InitialiseStatus() {
    CurrentStatus = VerificationStatus.Stale; // TODO use caching to determine if it's really stale.
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