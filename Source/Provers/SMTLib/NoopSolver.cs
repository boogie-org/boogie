using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib;

public class NoopSolver : SMTLibSolver
{
#pragma warning disable CS0067
  public override event Action<string> ErrorHandler;
#pragma warning restore CS0067

  public override void Close()
  {
  }

  protected readonly Queue<SExpr> responses = new();

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

  public override Task<SExpr> SendRequest(string request, CancellationToken cancellationToken = default) {
    Send(request);
    return GetProverResponse();
  }

  public override async Task<IReadOnlyList<SExpr>> SendRequestsAndCloseInput(IReadOnlyList<string> requests, CancellationToken cancellationToken = default) {

    foreach (var request in requests) {
      Send(request);
    }
    var result = new List<SExpr>();
    foreach (var request in requests) {
      result.Add(await GetProverResponse());
    }

    return result;
  }

  protected virtual Task<SExpr> GetProverResponse()
  {
    return Task.FromResult(responses.Count > 0 ? responses.Dequeue() : null);
  }

  public override void NewProblem(string descriptiveName)
  {
  }

  public override Task PingPong() {
    return Task.CompletedTask;
  }

  public override void AddErrorHandler(Action<string> handler)
  {
  }
}