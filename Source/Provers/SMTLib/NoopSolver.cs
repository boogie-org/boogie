using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib;

class NoopSolver : SMTLibSolver
{
#pragma warning disable CS0067
  public override event Action<string> ErrorHandler;
#pragma warning restore CS0067

  public override void Close()
  {
  }

  private Queue<SExpr> responses = new();

  public override void Send(string cmd)
  {
    if (cmd.StartsWith("(get-value")) {
      return;
    }

    var response = cmd switch
    {
      "(get-model)" => new SExpr("error", new SExpr("model is not available")),
      "(get-info :name)" => new SExpr(":name"),
      "(get-info :rlimit)" => new SExpr(":rlimit", new SExpr("0")),
      "(check-sat)" => new SExpr("unknown"),
      "(get-info :reason-unknown)" => new SExpr(":reason-unknown", new SExpr("incomplete")),
      "(get-unsat-core)" => new SExpr(""),
      _ => null
    };

    if (response is not null) { responses.Enqueue(response); }
  }

  public override Task<SExpr> GetProverResponse()
  {
    return Task.FromResult(responses.Count > 0 ? responses.Dequeue() : null);
  }

  public override void IndicateEndOfInput()
  {
  }

  public override void NewProblem(string descriptiveName)
  {
  }

  protected override void HandleError(string msg)
  {
    throw new NotSupportedException();
  }
}