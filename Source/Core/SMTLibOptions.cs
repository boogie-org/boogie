using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public interface SMTLibOptions
  {
    bool ExpectingModel { get; }
    bool ProduceModel { get; }
    bool ProduceUnsatCores { get; }
    bool ImmediatelyAcceptCommands { get; }
    bool RunningBoogieFromCommandLine { get; }
    CommandLineOptions.TypeEncoding TypeEncodingMethod { get; }
    bool UseArrayTheory { get; }
    bool PrintNecessaryAssumes { get; }
    string ProverPreamble { get; }
    int ErrorLimit { get; }
    bool RunDiagnosticsOnTimeout { get; }
    bool TraceDiagnosticsOnTimeout { get; }
    uint TimeLimitPerAssertionInPercent { get; }
    bool SIBoolControlVC { get; }
    bool RestartProverPerVC { get; }
    bool Trace { get; }
    bool KeepOriginalName { get; }
  }
}