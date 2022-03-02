namespace Microsoft.Boogie;

public interface HoudiniOptions : VCGenOptions
{
  bool HoudiniUseCrossDependencies { get; }
  bool ReverseHoudiniWorklist { get; }
  bool ExplainHoudini { get; }
  bool UseUnsatCoreForContractInfer { get; }
  bool StagedHoudiniReachabilityAnalysis { get; }
  bool StagedHoudiniMergeIgnoredAnnotations { get; }
  int StagedHoudiniThreads { get; }
  bool DebugConcurrentHoudini { get; }
  string StagedHoudini { get; }
  XmlSink XmlRefuted { get; }
}