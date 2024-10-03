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
    Contract.Invariant(cce.NonNullElements(Args));
  }

  public CalleeCounterexampleInfo(Counterexample cex, List<object /*!>!*/> x)
  {
    Contract.Requires(cce.NonNullElements(x));
    Counterexample = cex;
    Args = x;
  }
}