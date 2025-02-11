using System;
using System.Diagnostics.Contracts;
using VC;

namespace Microsoft.Boogie;

public class VerifierCallback
{
  private CoreOptions.ProverWarnings printProverWarnings;

  public VerifierCallback(CoreOptions.ProverWarnings printProverWarnings)
  {
    this.printProverWarnings = printProverWarnings;
  }

  // reason == null means this is genuine counterexample returned by the prover
  // other reason means it's time out/memory out/crash
  public virtual void OnCounterexample(Counterexample ce, string /*?*/ reason)
  {
    Contract.Requires(ce != null);
  }

  // called in case resource is exceeded and we don't have counterexample
  public virtual void OnTimeout(string reason)
  {
    Contract.Requires(reason != null);
  }

  public virtual void OnOutOfMemory(string reason)
  {
    Contract.Requires(reason != null);
  }

  public virtual void OnOutOfResource(string reason)
  {
    Contract.Requires(reason != null);
  }

  public delegate void ProgressDelegate(string phase, int step, int totalSteps, double progressEstimate);
    
  public virtual ProgressDelegate OnProgress => null;

  public virtual void OnUnreachableCode(ImplementationRun run)
  {
    Contract.Requires(run != null);
  }

  public virtual void OnWarning(CoreOptions options, string msg)
  {
    Contract.Requires(msg != null);
    switch (printProverWarnings)
    {
      case CoreOptions.ProverWarnings.None:
        break;
      case CoreOptions.ProverWarnings.Stdout:
        options.OutputWriter.WriteLine("Prover warning: " + msg);
        break;
      case CoreOptions.ProverWarnings.Stderr:
        Console.Error.WriteLine("Prover warning: " + msg);
        break;
      default:
        Contract.Assume(false);
        throw new Cce.UnreachableException(); // unexpected case
    }
  }

  public virtual void OnVCResult(VerificationRunResult result)
  {
    Contract.Requires(result != null);
  }
}