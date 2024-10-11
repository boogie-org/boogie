#nullable enable
using System.Runtime.Caching;

namespace Microsoft.Boogie;

public class EmptyVerificationResultCache : IVerificationResultCache {
  public Program? CachedProgram(string programId) {
    return null;
  }

  public void SetProgram(string programId, Program program, CacheItemPolicy policy) {
  }

  public int VerificationPriority(Implementation implementation, bool runDiagnosticsOnTimeout) {
    Lookup(implementation, runDiagnosticsOnTimeout, out var priority);
    return priority;
  }

  public ImplementationRunResult? Lookup(Implementation impl, bool runDiagnosticsOnTimeout, out int priority) {
    priority = Priority.HIGH;
    return null;
  }

  public void Insert(Implementation implementation, ImplementationRunResult result) {
  }
}