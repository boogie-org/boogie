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

  private int pingpongCounter = 0;

  /// <summary>
  /// Sends a ping command and returns the a predicate that checks if an SExpr is a matching pong
  /// </summary>
  /// <param name="value"></param>
  /// <returns></returns>
  public Func<SExpr, bool> Ping(string value)
  {
    Send($"(echo \"({value})\")");
    return sx => sx is { Name: var obtainedName } && obtainedName == value;
  }

  /// <summary>
  /// Throws an ProverDiedException if the prover does not answer after msBeforeAssumingProverDied
  /// </summary>
  public async Task PingPong(int msBeforeAssumingProverDied) {
    var isPong = Ping($"PingPong{pingpongCounter++}");
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
      
      if (isPong(sx))
      {
        break;
      }
    }
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