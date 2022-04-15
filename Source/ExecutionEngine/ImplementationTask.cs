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
  private readonly ProcessedProgram processedProgram;

  public Task<VerificationResult> ActualTask { get; private set; }
  public Implementation Implementation { get; }

  public ImplementationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Implementation implementation) {
    this.engine = engine;
    this.processedProgram = processedProgram;
    Implementation = implementation;
  }

  public void Run() {
    source = new CancellationTokenSource();
    ActualTask = engine.VerifyImplementationWithLargeStackScheduler(processedProgram, new PipelineStatistics(), null, null,
      Implementation, source, TextWriter.Null);
  }

  public void Cancel() {
    source.Cancel();
  }
}