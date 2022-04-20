using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

public interface IImplementationTask {
  public ProcessedProgram ProcessedProgram { get; }
  public Implementation Implementation { get; }
  public Task<VerificationResult> ActualTask { get; }
  void Run();
}

public class ImplementationTask : IImplementationTask {
  private CancellationTokenSource source;
  private readonly ExecutionEngine engine;
  public ProcessedProgram ProcessedProgram { get; }

  public Task<VerificationResult> ActualTask { get; private set; }
  public Implementation Implementation { get; }

  public ImplementationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Implementation implementation) {
    this.engine = engine;
    this.ProcessedProgram = processedProgram;
    Implementation = implementation;
  }

  public void Run() {
    source = new CancellationTokenSource();
    ActualTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(), null, null,
      Implementation, source, TextWriter.Null);
  }

  public void Cancel() {
    source.Cancel();
  }
}