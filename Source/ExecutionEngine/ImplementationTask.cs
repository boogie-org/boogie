using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

public class ImplementationTask {
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
      Implementation, source, TextWriter.Null);
  }

  public void Cancel() {
    source.Cancel();
  }
}