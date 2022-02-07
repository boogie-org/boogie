using System;
using System.Threading;

namespace Microsoft.Boogie.SMTLib;

public abstract class SMTLibSolver
{
  public abstract event Action<string> ErrorHandler;
  public abstract void Close();
  public abstract void Send(string cmd);
  public abstract SExpr GetProverResponse(CancellationToken cancellationToken);
  public abstract void NewProblem(string descriptiveName);

  protected abstract void HandleError(string msg);

  public void Ping()
  {
    Send("(get-info :name)");
  }

  public void PingPong(CancellationToken cancellationToken)
  {
    Ping();
    while (true)
    {
      var sx = GetProverResponse(cancellationToken);
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

  public ProverDiedException GetExceptionIfProverDied(CancellationToken cancellationToken)
  {
    try
    {
      PingPong(cancellationToken);
    }
    catch (ProverDiedException e)
    {
      return e;
    }

    return null;
  }
}