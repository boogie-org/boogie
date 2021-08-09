using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Threading;
using Microsoft.Boogie;

namespace VC
{
  public class CheckerPool
  {
    private readonly int size;
    private readonly string logFilePath;
    private readonly bool appendLogFile;

    private readonly List<Checker> /*!>!*/ checkers = new();

    public static CheckerPool FromOptions()
    {
      return new CheckerPool(
        CommandLineOptions.Clo.VcsCores,
        CommandLineOptions.Clo.ProverLogFilePath,
        CommandLineOptions.Clo.ProverLogFileAppend);
    }
    
    public CheckerPool(int size, string logFilePath, bool appendLogFile)
    {
      this.size = size;
      this.logFilePath = logFilePath;
      this.appendLogFile = appendLogFile;
    }

    public Checker FindCheckerFor(ConditionGeneration vcgen, Implementation impl, bool isBlocking = true, int waitTimeinMs = 50, int maxRetries = 3)
    {
      Contract.Requires(0 <= waitTimeinMs && 0 <= maxRetries);
      Contract.Ensures(!isBlocking || Contract.Result<Checker>() != null);

      var program = vcgen.program;
      
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
              if (c.WillingToHandle(program) && !CommandLineOptions.Clo.PruneFunctionsAndAxioms)
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

        if (size <= checkers.Count) {
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

        return CreateNewChecker(vcgen, impl);
      }
    }

    private Checker CreateNewChecker(ConditionGeneration vcgen, Implementation impl)
    {
      var log = logFilePath;
      if (log != null && !log.Contains("@PROC@") && checkers.Count > 0) {
        log = log + "." + checkers.Count;
      }

      Checker ch = new Checker(vcgen, vcgen.program, logFilePath, appendLogFile, impl);
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