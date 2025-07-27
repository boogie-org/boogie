using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class CalleeCounterexampleInfo
{
  public readonly Counterexample Counterexample;

  public readonly List<object> /*!>!*/ Args;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Cce.NonNullElements(Args));
  }

  public CalleeCounterexampleInfo(Counterexample cex, List<object /*!>!*/> x)
  {
    Contract.Requires(Cce.NonNullElements(x));
    Counterexample = cex;
    Args = x;
  }
}