using System;

namespace Microsoft.Boogie.SMTLib;

class NoopSolver : SMTLibSolver
{
#pragma warning disable CS0067
  public override event Action<string> ErrorHandler;
#pragma warning restore CS0067

  public override void Close()
  {
  }

  private SExpr response;

  public override void Send(string cmd)
  {
    if (cmd.StartsWith("(get-value")) {
      response = null;
    } 
    else
    {
      response = cmd switch
      {
        "(get-model)" => null,
        "(get-info :name)" => new SExpr(":name"),
        "(get-info :rlimit)" => new SExpr(":rlimit", new SExpr("0")),
        "(check-sat)" => new SExpr("unknown"),
        "(get-info :reason-unknown)" => new SExpr("incomplete"),
        "(get-unsat-core)" => new SExpr(""),
        _ => null
      };
    }
  }

  public override SExpr GetProverResponse()
  {
    var result = response;
    response = null;
    return result;
  }

  public override void NewProblem(string descriptiveName)
  {
  }

  protected override void HandleError(string msg)
  {
    throw new NotSupportedException();
  }
}