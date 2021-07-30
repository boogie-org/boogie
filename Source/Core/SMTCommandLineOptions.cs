using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public interface SMTCommandLineOptions
  {
    bool RunningBoogieFromCommandLine { get; }
    CommandLineOptions.TypeEncoding TypeEncodingMethod { get; }
    int StratifiedInlining { get; }
    bool ContractInfer { get; }
    bool UseArrayTheory { get; }
    bool PrintNecessaryAssumes { get; }
    bool ExplainHoudini { get; }
    int EnableUnSatCoreExtract { get; }
    bool UseUnsatCoreForContractInfer { get; }
    bool RunDiagnosticsOnTimeout { get; }
    string ProverPreamble { get; }
    bool ConcurrentHoudini { get; }
    int ErrorLimit { get; }
    List<CommandLineOptions.ConcurrentHoudiniOptions> Cho { get; }
    bool TraceDiagnosticsOnTimeout { get; }
    uint TimeLimitPerAssertionInPercent { get; }
    bool SIBoolControlVC { get; }
    bool RestartProverPerVC { get; }
    bool Trace { get; }
    bool UseProverEvaluate { get; }
    int PrintErrorModel { get; }
    int EnhancedErrorMessages { get; }
    string ModelViewFile { get; }
    bool StratifiedInliningWithoutModels { get; }
  }
}