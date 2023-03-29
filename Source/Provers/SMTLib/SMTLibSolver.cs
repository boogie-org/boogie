using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib;

public abstract class SMTLibSolver
{
  public const string PingRequest = "(get-info :name)";
  public abstract event Action<string> ErrorHandler;
  public abstract void Close();
  public abstract void Send(string cmd);
  public abstract Task<SExpr> SendRequest(string request,
    CancellationToken cancellationToken = default);

  public abstract Task<IReadOnlyList<SExpr>> SendRequestsAndCloseInput(IReadOnlyList<string> requests,
    CancellationToken cancellationToken = default);

  public abstract void NewProblem(string descriptiveName);

  public abstract Task PingPong();

  public abstract void AddErrorHandler(Action<string> handler);

  public static bool IsPong(SExpr response)
  {
    return response is { Name: ":name" };
  }

  public async Task<ProverDiedException> GetExceptionIfProverDied()
  {
    try
    {
      await PingPong();
      return null;
    }
    catch (ProverDiedException e)
    {
      return e;
    }
  }
}