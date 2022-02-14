namespace Microsoft.Boogie;

public interface ConcurrencyOptions : CommandLineOptions
{
  bool TrustMoverTypes { get; }
  bool TrustInductiveSequentialization { get; }
  int TrustLayersDownto { get; }
  int TrustLayersUpto { get; }
  bool TrustNoninterference { get; }
  bool WarnNotEliminatedVars { get; }
    
}