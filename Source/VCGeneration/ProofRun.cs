using System.Collections.Concurrent;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace VC;

public interface ProofRun {
  string Description { get; }
  
  List<Counterexample> Counterexamples { get; }

  ConcurrentBag<TrackedNodeComponent> CoveredElements { get;  }
}