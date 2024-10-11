using System;

namespace Microsoft.Boogie;

struct CachedVerificationResultInjectorRun
{
  public DateTime Start { get; internal set; }

  public DateTime End { get; internal set; }

  public int TransformedImplementationCount { get; internal set; }

  public int ImplementationCount { get; internal set; }

  public int SkippedImplementationCount { get; set; }

  public int LowPriorityImplementationCount { get; set; }

  public int MediumPriorityImplementationCount { get; set; }

  public int HighPriorityImplementationCount { get; set; }

  public long[] CachingActionCounts { get; set; }
}