#nullable enable
using System.Runtime.Caching;

namespace Microsoft.Boogie;

public interface IVerificationResultCache {
  Program? CachedProgram(string programId);
  void SetProgram(string programId, Program program, CacheItemPolicy policy);
  int VerificationPriority(Implementation implementation, bool runDiagnosticsOnTimeout);
  ImplementationRunResult? Lookup(Implementation impl, bool runDiagnosticsOnTimeout, out int priority);
  void Insert(Implementation implementation, ImplementationRunResult result);
}