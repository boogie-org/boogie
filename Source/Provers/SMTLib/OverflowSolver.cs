namespace Microsoft.Boogie.SMTLib;

public class OverflowSolver : NoopSolver
{
  public override void Send(string request)
  {
    if (request == "(get-info :reason-unknown)")
    {
      responses.Enqueue(new SExpr(":reason-unknown", 
        new SExpr("Overflow encountered when expanding old_vector")));
      return;
    }
    base.Send(request);
  }
}