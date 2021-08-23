using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Threading;
using Microsoft.Boogie;

namespace VC
{
  public class CheckerPool
  {
    private readonly Program program;
    private readonly CommandLineOptions options;

    private readonly List<Checker> /*!>!*/ checkers = new();
    protected internal object CheckerCommonState;
    
    public CheckerPool(Program program, CommandLineOptions options)
    {
      this.program = program;
      this.options = options;
    }

    public Checker FindCheckerFor(Implementation impl, bool isBlocking = true, int waitTimeinMs = 50, int maxRetries = 3)
    {
      Contract.Requires(0 <= waitTimeinMs && 0 <= maxRetries);
      Contract.Ensures(!isBlocking || Contract.Result<Checker>() != null);
      
      lock (checkers)
      {
        retry:
        // Look for existing checker.
        for (int i = 0; i < checkers.Count; i++)
        {
          var c = checkers[i];
          if (Monitor.TryEnter(c))
          {
            try
            {
              if (c.WillingToHandle(program) && !options.PruneFunctionsAndAxioms)
              {
                c.GetReady();
                return c;
              }
              else if (c.IsIdle || c.IsClosed)
              {
                if (c.IsIdle)
                {
                  c.Retarget(program, c.TheoremProver.Context, impl);
                  c.GetReady();
                  return c;
                }
                else
                {
                  checkers.RemoveAt(i);
                  i--;
                }
              }
            }
            finally
            {
              Monitor.Exit(c);
            }
          }
        }

        if (options.VcsCores <= checkers.Count) {
          if (isBlocking || 0 < maxRetries)
          {
            if (0 < waitTimeinMs)
            {
              Monitor.Wait(checkers, waitTimeinMs);
            }

            maxRetries--;
            goto retry;
          }

          return null;
        }

        return CreateNewChecker(impl);
      }
    }

    private Checker CreateNewChecker(Implementation impl)
    {
      var log = options.ProverLogFilePath;
      if (log != null && !log.Contains("@PROC@") && checkers.Count > 0) {
        log = log + "." + checkers.Count;
      }

      Checker ch = new Checker(this, program, options.ProverLogFilePath, options.ProverLogFileAppend, impl);
      ch.GetReady();
      checkers.Add(ch);
      return ch;
    }

    public void Dispose()
    {
      foreach (Checker checker in checkers)
      {
        Contract.Assert(checker != null);
        checker.Close();
      }
    }
  }
}