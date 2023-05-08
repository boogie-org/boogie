namespace Microsoft.Boogie;

public interface ConcurrencyOptions : CoreOptions
{
  bool TrustMoverTypes { get; }
  bool TrustSequentialization { get; }
  int TrustLayersDownto { get; }
  int TrustLayersUpto { get; }
  bool TrustNoninterference { get; }
  bool TrustRefinement { get; }
  bool WarnNotEliminatedVars { get; }
}