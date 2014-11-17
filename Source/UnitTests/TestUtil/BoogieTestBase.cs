using NUnit.Framework;
using System;
using System.Diagnostics;
using Microsoft.Boogie;

namespace Microsoft.Boogie
{
  namespace TestUtil
  {
    public class BoogieTestBase {

      public BoogieTestBase() {
        // Debug log output goes to standard error.
        // Failing System.Diagnostics failures trigger NUnit assertion failures
        Debug.Listeners.Add(new AssertionTextWriterTraceListener(Console.Error));

        // FIXME: THIS IS A HACK. Boogie's methods
        // depend on its command line parser being set!
        CommandLineOptions.Install(new Microsoft.Boogie.CommandLineOptions());
      }
    }
  }
}

