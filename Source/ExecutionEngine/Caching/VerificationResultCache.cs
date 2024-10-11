#nullable enable
using System;
using System.Diagnostics.Contracts;
using System.Runtime.Caching;
using System.Text.RegularExpressions;
using VC;

namespace Microsoft.Boogie
{
  public sealed class VerificationResultCache : IVerificationResultCache
  {
    private readonly MemoryCache programCache = new("ProgramCache");
    private readonly MemoryCache Cache = new("VerificationResultCache");

    public Program? CachedProgram(string programId) {
      return programCache.Get(programId) as Program;
    }

    private readonly CacheItemPolicy Policy = new CacheItemPolicy
      {SlidingExpiration = new TimeSpan(0, 10, 0), Priority = CacheItemPriority.Default};

    public void Insert(Implementation impl, ImplementationRunResult result)
    {
      Contract.Requires(result != null);
      Cache.Set(impl.Id, result, Policy);
    }


    public ImplementationRunResult? Lookup(Implementation impl, bool runDiagnosticsOnTimeout, out int priority)
    {
      var result = Cache.Get(impl.Id) as ImplementationRunResult;
      if (result == null)
      {
        priority = Priority.HIGH;
      }
      else if (result.Checksum != impl.Checksum)
      {
        priority = Priority.MEDIUM;
      }
      else if (impl.DependencyChecksum == null || result.DependenciesChecksum != impl.DependencyChecksum)
      {
        priority = Priority.LOW;
      }
      else if (result.VcOutcome == VcOutcome.TimedOut && runDiagnosticsOnTimeout)
      {
        priority = Priority.MEDIUM;
      }
      else
      {
        priority = Priority.SKIP;
      }

      return result;
    }


    public void Clear()
    {
      Cache.Trim(100);
    }


    public void RemoveMatchingKeys(Regex keyRegexp)
    {
      foreach (var kv in Cache)
      {
        if (keyRegexp.IsMatch(kv.Key))
        {
          Cache.Remove(kv.Key);
        }
      }
    }


    public int VerificationPriority(Implementation impl, bool runDiagnosticsOnTimeout)
    {
      Lookup(impl, runDiagnosticsOnTimeout, out var priority);
      return priority;
    }

    public void SetProgram(string programId, Program program, CacheItemPolicy policy)
    {
      programCache.Set(programId, program, policy);
    }
  }
}