using VC;

namespace Microsoft.Boogie;

public interface VCGenOptions : SMTLibOptions
{
  int KInductionDepth { get; }
  bool AlwaysAssumeFreeLoopInvariants { get; }
  int LiveVariableAnalysis { get; }
  bool RemoveEmptyBlocks { get; }
}