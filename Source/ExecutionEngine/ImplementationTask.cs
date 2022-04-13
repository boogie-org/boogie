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
  private readonly ProcessedProgram program;

  public Task<VerificationResult> ActualTask { get; private set; }
  public Implementation Implementation { get; }

  public ImplementationTask(ExecutionEngine engine, ProcessedProgram program, Implementation implementation) {
    this.engine = engine;
    this.program = program;
    Implementation = implementation;
  }

  public void Run() {
    source = new CancellationTokenSource();
    ActualTask = engine.VerifyImplementationWithLargeStackScheduler(program, new PipelineStatistics(), null, null,
      Implementation, source, TextWriter.Null);
  }

  public void Cancel() {
    source.Cancel();
  }
}