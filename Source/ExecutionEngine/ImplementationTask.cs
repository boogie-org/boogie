using System;
using System.IO;
using System.Reactive.Subjects;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

public interface IVerificationStatus {}

public record Completed(VerificationResult Result) : IVerificationStatus; // Results are available

public record Queued : IVerificationStatus; // Scheduled to be run but waiting for resources

public record Stale : IVerificationStatus; // Not scheduled to be run

public record Running : IVerificationStatus; // Currently running

public interface IImplementationTask {
  IVerificationStatus CacheStatus { get; }

  ProcessedProgram ProcessedProgram { get; }
  Implementation Implementation { get; }

  IObservable<IVerificationStatus> RunAndAllowCancel();
  void Cancel();
}

public class ImplementationTask : IImplementationTask {
  private readonly ExecutionEngine engine;

  public IVerificationStatus CacheStatus { get; }

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

  private CancellationTokenSource cancellationSource;

  public IObservable<IVerificationStatus> RunAndAllowCancel() {
    if (cancellationSource != null) {
      throw new InvalidOperationException();
    }

    cancellationSource = new();
    return Run(cancellationSource.Token);
  }

  public void Cancel() {
    if (cancellationSource == null) {
      throw new InvalidOperationException();
    }

    cancellationSource.Cancel();
    cancellationSource = null;
  }

  public IObservable<IVerificationStatus> Run(CancellationToken cancellationToken)
  {
    var observableStatus = new ReplaySubject<IVerificationStatus>();
    cancellationToken.Register(() => {
      observableStatus.OnNext(new Stale());
      observableStatus.OnCompleted();
    });
    var task = RunInternal(cancellationToken, observableStatus.OnNext);
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
    notifyStatusChange(new Completed(result));
    return result;
  }
}