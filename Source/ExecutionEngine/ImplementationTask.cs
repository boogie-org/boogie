using System;
using System.IO;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using VC;

namespace Microsoft.Boogie;

public interface IImplementationTask {
  
  IObservable<VerificationStatus> ObservableStatus { get; }
  VerificationStatus CurrentStatus { get; }
  
  public ProcessedProgram ProcessedProgram { get; }
  public Implementation Implementation { get; }
  public Task<VerificationResult> ActualTask { get; }
  void Run();
  void InitialiseStatus();
}

public class ImplementationTask : IImplementationTask {
  private readonly CancellationTokenSource source;

  private readonly ReplaySubject<VerificationStatus> observableStatus = new();
  
  private VerificationStatus currentStatus;
  public IObservable<VerificationStatus> ObservableStatus => observableStatus;

  public VerificationStatus CurrentStatus {
    get => currentStatus;
    set {
      currentStatus = value;
      observableStatus.OnNext(value);
    }
  }

  public ProcessedProgram ProcessedProgram { get; }

  public Task<VerificationResult> ActualTask { get; private set; } // TODO can we figure out how to immediately get this in the created state?
  public Implementation Implementation { get; }

  private readonly TaskCompletionSource runSource = new();
  
  public ImplementationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Implementation implementation) {
    ProcessedProgram = processedProgram;
    Implementation = implementation;
    source = new CancellationTokenSource();

    ActualTask = runSource.Task.ContinueWith(t => {

      var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(), null, null,
        Implementation, source, TextWriter.Null);

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
    }).Unwrap();
  }

  public void InitialiseStatus() {
    CurrentStatus = VerificationStatus.Stale; // TODO use caching to determine if it's really stale.
  }

  public void Run() {
    runSource.SetResult();
  }

  public void Cancel() {
    source.Cancel();
  }
}

public enum VerificationStatus {
  Stale,
  Queued,
  Verifying,
  Correct,
  Error
}