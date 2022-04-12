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
    ActualTask = VerifyImplementationWithInitialisedCounterExamples();
  }

  private async Task<VerificationResult> VerifyImplementationWithInitialisedCounterExamples() {
    var result = await engine.VerifyImplementationWithLargeStackScheduler(program, new PipelineStatistics(), null, null,
      Implementation, source, TextWriter.Null);

    if (engine.Options.ExpectingModel) {
      foreach (var counterExample in result.Errors) {
        // TODO, figure out why these counterExamples are not already in a usable state.
        counterExample.InitializeStates();
      }
    }
    return result;
  }

  public void Cancel() {
    source.Cancel();
  }
}