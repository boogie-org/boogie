namespace Microsoft.Boogie;

public enum PipelineOutcome
{
  Done,
  ResolutionError,
  TypeCheckingError,
  ResolvedAndTypeChecked,
  FatalError,
  Cancelled,
  VerificationCompleted
}