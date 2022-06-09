using System;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib;

public abstract class SMTLibSolver
{
  public abstract event Action<string> ErrorHandler;
  public abstract void Close();
  public abstract void Send(string cmd);
  public abstract Task<SExpr> SendRequest(string cmd);
  
  public abstract Task<SExpr> GetProverResponse();
  public abstract void NewProblem(string descriptiveName);

  public abstract void IndicateEndOfInput();

  protected abstract void HandleError(string msg);

  public void Ping()
  {
    Send("(get-info :name)");
  }

  public async Task PingPong()
  {
    Ping();
    while (true)
    {
      var sx = await GetProverResponse();
      if (sx == null)
      {
        throw new ProverDiedException();
      }

      if (IsPong(sx))
      {
        return;
      }
      else
      {
        HandleError("Invalid PING response from the prover: " + sx.ToString());
      }
    }
  }

  public bool IsPong(SExpr sx)
  {
    return sx is { Name: ":name" };
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