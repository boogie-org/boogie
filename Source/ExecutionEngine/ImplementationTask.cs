using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

public interface IImplementationTask {
  public Task<VerificationResult> ActualTask { get; }
  void Run();
}

public class ImplementationTask : IImplementationTask {
  private CancellationTokenSource source;
  private readonly ExecutionEngine engine;
  private readonly Program program;

  public ImplementationTask(ExecutionEngine engine, Program program, Implementation implementation) {
    this.engine = engine;
    this.program = program;
    Implementation = implementation;
  }

  public Task<VerificationResult> ActualTask { get; private set; }

  public Implementation Implementation { get; }

  public void Run() {
    source = new CancellationTokenSource();
    ActualTask = engine.VerifyImplementationWithLargeStackScheduler(program, new PipelineStatistics(), null, null,
      Implementation, source, TextWriter.Null).ContinueWith(t => {

      foreach (var counterExample in t.Result.Errors) {
        // TODO, figure out why these counterExamples are not already in a usable state.
        counterExample.InitializeStates();
      }
      return t.Result;
    });
  }

  public void Cancel() {
    source.Cancel();
  }
}