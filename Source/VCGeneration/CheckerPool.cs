#nullable enable
using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace VC
{
  public class CheckerPool
  {
    // Holds both created and not yet created checkers.
    private readonly AsyncQueue<Checker?> checkerLine = new();
    private bool disposed;

    public VCGenOptions Options { get; }

    public CheckerPool(VCGenOptions options)
    {
      Options = options;
      for (var index = 0; index < options.VcsCores; index++) {
        checkerLine.AddItem(null);
      }
    }

    public async Task<Checker> FindCheckerFor(ConditionGeneration vcgen, Split? split, CancellationToken cancellationToken)
    {
      if (disposed) {
        throw new Exception("CheckerPool was already disposed");
      }

      var checker = await checkerLine.GetItem(cancellationToken) ?? CreateNewChecker();

      PrepareChecker(vcgen.program, split, checker);
      return checker;
    }

    private int createdCheckers;
    private Checker CreateNewChecker()
    {
      var log = Options.ProverLogFilePath;
      var index = Interlocked.Increment(ref createdCheckers) - 1;
      if (log != null && !log.Contains("@PROC@") && index > 0) {
        log = log + "." + index;
      } 

      return new Checker(this, log, Options.ProverLogFileAppend);
    }

    public void Dispose()
    {
      disposed = true;
      foreach (var checker in checkerLine.ClearItems()) {
        checker?.Close();
      }
    }

    void PrepareChecker(Program program, Split? split, Checker checker)
    {
      if (checker.WillingToHandle(program) && (split == null || checker.SolverOptions.RandomSeed == split.RandomSeed && !Options.Prune))
      {
        checker.GetReady();
        return;
      }

      checker.Target(program, checker.TheoremProver.Context, split);
      checker.GetReady();
    }

    public void AddChecker(Checker checker)
    {
      if (checker.IsClosed) {
        throw new Exception();
      }
      if (disposed) {
        checker.Close();
        return;
      }
      checkerLine.AddItem(checker);
    }

    public void CheckerDied()
    {
      checkerLine.AddItem(null);
    }
  }
}