using System;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib;

public class UnsatSolver : NoopSolver {
  private readonly TimeSpan delay;

  public UnsatSolver() : this(TimeSpan.Zero) {
  }

  public UnsatSolver(TimeSpan delay) {
    this.delay = delay;
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
      await Task.Delay(delay);
    }
    return await base.GetProverResponse();
  }
}