namespace Microsoft.Boogie.SMTLib;

public class UnsatSolver : NoopSolver
{
  public override void Send(string request)
  {
    if (request == "(check-sat)")
    {
      responses.Enqueue(new SExpr("unsat"));
      return;
    }
    base.Send(request);
  }
}