namespace Microsoft.Boogie;

public interface ConcurrencyOptions : CoreOptions
{
  bool TrustMoverTypes { get; }
  int TrustLayersDownto { get; }
  int TrustLayersUpto { get; }
  bool TrustNoninterference { get; }
  bool TrustRefinement { get; }
  bool TrustInvariants { get; }
  bool WarnNotEliminatedVars { get; }
}