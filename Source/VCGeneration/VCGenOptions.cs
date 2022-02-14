namespace Microsoft.Boogie;

public interface VCGenOptions : SMTLibOptions
{
  ProverFactory TheProverFactory { get; }
  int KInductionDepth { get; }
  bool AlwaysAssumeFreeLoopInvariants { get; }
  int LiveVariableAnalysis { get; }
  bool RemoveEmptyBlocks { get; }
}