using System;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib;

public class UnsatSolver : NoopSolver {
  private readonly SemaphoreSlim semaphore;

  public UnsatSolver() : this(new SemaphoreSlim(int.MaxValue)) {
  }

  public UnsatSolver(SemaphoreSlim semaphore) {
    this.semaphore = semaphore;
  }

  public override void Send(string request)
  {
    if (request == "(check-sat)")
    {
      responses.Enqueue(new SExpr("unsat"));
      return;
    }
    base.Send(request);
  }


  protected override async Task<SExpr> GetProverResponse() {
    if (responses.Peek().Name == "unsat") {
      await semaphore.WaitAsync();
    }
    return await base.GetProverResponse();
  }
}