using System;
using System.IO;
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.SMTLib
{
  internal class Inspector
  {
    [Rep] protected readonly Process inspector;
    [Rep] readonly TextReader fromInspector;
    [Rep] readonly TextWriter toInspector;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(inspector != null);
      Contract.Invariant(fromInspector != null);
      Contract.Invariant(toInspector != null);
    }


    public Inspector(SMTLibProverOptions opts)
    {
      Contract.Requires(opts != null);
      ProcessStartInfo psi = new ProcessStartInfo(opts.Inspector);
      Contract.Assert(psi != null);
      psi.CreateNoWindow = true;
      psi.UseShellExecute = false;
      psi.RedirectStandardInput = true;
      psi.RedirectStandardOutput = true;
      psi.RedirectStandardError = false;

      try
      {
        Process inspector = Process.Start(psi);
        this.inspector = inspector;
        fromInspector = inspector.StandardOutput;
        toInspector = inspector.StandardInput;
      }
      catch (System.ComponentModel.Win32Exception e)
      {
        throw new Exception(string.Format("Unable to start the inspector process {0}: {1}", opts.Inspector, e.Message));
      }
    }

    public void NewProblem(string descriptiveName)
    {
      Contract.Requires(descriptiveName != null);
      toInspector.WriteLine("PROBLEM " + descriptiveName);
    }

    public void StatsLine(string line)
    {
      Contract.Requires(line != null);
      toInspector.WriteLine(line);
      toInspector.Flush();
    }
  }
}