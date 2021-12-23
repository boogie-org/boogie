using System;

namespace Microsoft.Boogie.SMTLib;

public abstract class SMTLibSolver
{
  public abstract event Action<string> ErrorHandler;
  public abstract void Close();
  public abstract void Send(string cmd);
  public abstract SExpr GetProverResponse();
  public abstract void NewProblem(string descriptiveName);

  protected abstract void HandleError(string msg);

  public void Ping()
  {
    Send("(get-info :name)");
  }

  public void PingPong()
  {
    Ping();
    while (true)
    {
      var sx = GetProverResponse();
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

  public ProverDiedException GetExceptionIfProverDied()
  {
    try
    {
      PingPong();
    }
    catch (ProverDiedException e)
    {
      return e;
    }

    return null;
  }
}