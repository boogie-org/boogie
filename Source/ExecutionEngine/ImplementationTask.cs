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
  
  public ProcessedProgram ProcessedProgram { get; }
  public Implementation Implementation { get; }
  public Task<VerificationResult> ActualTask { get; }
  void Run();
}

public class ImplementationTask : IImplementationTask {
  private CancellationTokenSource source;
  private readonly ExecutionEngine engine;

  private readonly Subject<VerificationStatus> observableStatus = new();
  
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

  public Task<VerificationResult> ActualTask { get; private set; }
  public Implementation Implementation { get; }

  public ImplementationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Implementation implementation) {
    this.engine = engine;
    ProcessedProgram = processedProgram;
    Implementation = implementation;
    currentStatus = VerificationStatus.Stale; // TODO use caching to determine if it's really stale.
  }

  public void Run() {
    CurrentStatus = VerificationStatus.Queued;
    
    source = new CancellationTokenSource();
    var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(), null, null,
      Implementation, source, TextWriter.Null);

    enqueueTask.ContinueWith(t => {
      CurrentStatus = VerificationStatus.Verifying;
    });
    
    ActualTask = enqueueTask.Unwrap();

    ActualTask.ContinueWith(t => {
      CurrentStatus = t.Result.Outcome == ConditionGeneration.Outcome.Correct
        ? VerificationStatus.Correct
        : VerificationStatus.Error;
      observableStatus.OnCompleted();
    });
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