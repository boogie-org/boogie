using System;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  // TODO move to SMTLib
  public interface SMTLibOptions : CommandLineOptions
  {
    ProverFactory TheProverFactory { get; }

    bool ExpectingModel { get; }
    bool ProduceModel { get; }
    bool ProduceUnsatCores { get; }
    bool ImmediatelyAcceptCommands { get; }
    bool RunningBoogieFromCommandLine { get; }
    bool PrintNecessaryAssumes { get; }
    string ProverPreamble { get; }
    bool TraceDiagnosticsOnTimeout { get; }
    uint TimeLimitPerAssertionInPercent { get; }
    bool SIBoolControlVC { get; }
    bool RestartProverPerVC { get; }
    bool EmitDebugInformation { get; }
    
    /**
     * Setting this to true will rename all identifiers in the Boogie program to a generated name that does not depend on the original name.
     * Discarding the original names is useful to prevent the solver input from changing when identifiers are renamed in the
     * Boogie program, which prevents unexpected changes in solver output.
     */
    bool NormalizeNames { get; }
  }
}