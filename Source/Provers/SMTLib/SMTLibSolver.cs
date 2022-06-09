using System;
using System.Collections.Generic;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib;

public abstract class SMTLibSolver
{
  public abstract event Action<string> ErrorHandler;
  public abstract void Close();
  public abstract void Send(string cmd);
  public abstract Task<SExpr> SendRequest(string request);

  public abstract Task<IReadOnlyList<SExpr>> SendRequestsAndClose(IReadOnlyList<string> requests);

  public abstract void NewProblem(string descriptiveName);

  protected abstract void HandleError(string msg);

  public async Task PingPong() {
    var response = await SendRequest("(get-info :name)");
    if (response == null)
    {
      throw new ProverDiedException();
    }

    if (response is { Name: ":name" })
    {
      return;
    }

    HandleError("Invalid PING response from the prover: " + response.ToString());
    await PingPong();
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