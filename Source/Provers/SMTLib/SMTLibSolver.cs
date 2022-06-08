using System;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib;

public abstract class SMTLibSolver
{
  public abstract event Action<string> ErrorHandler;
  public abstract void Close();
  public abstract void Send(string cmd);
  public abstract Task<SExpr> GetProverResponse();
  public abstract void NewProblem(string descriptiveName);

  public abstract void IndicateEndOfInput();

  protected abstract void HandleError(string msg);

  public void Ping()
  {
    Send("(get-info :name)");
  }

  /// <summary>
  /// Throws an ProverDiedException if the prover does not answer after msBeforeAssumingProverDied
  /// </summary>
  public async Task PingPong(int msBeforeAssumingProverDied)
  {
    Ping();
    while (true) {
      SExpr sx;
      try {
        sx = await GetProverResponse().WaitAsync(TimeSpan.FromMilliseconds(msBeforeAssumingProverDied));
      } catch (TimeoutException) {
        sx = null;
      }

      if (sx == null)
      {
        throw new ProverDiedException();
      }
        
      if (IsPong(sx))
      {
        return;
      }
    }
  }

  public bool IsPong(SExpr sx)
  {
    return sx is { Name: ":name" };
  }

  public async Task<ProverDiedException> GetExceptionIfProverDied(int msBeforeAssumingProverDied)
  {
    try
    {
      await PingPong(msBeforeAssumingProverDied);
      return null;
    }
    catch (ProverDiedException e)
    {
      return e;
    }
  }
}