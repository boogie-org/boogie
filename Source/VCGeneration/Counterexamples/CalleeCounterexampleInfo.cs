using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class CalleeCounterexampleInfo
{
  public Counterexample counterexample;

  public List<object> /*!>!*/
    args;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(cce.NonNullElements(args));
  }

  public CalleeCounterexampleInfo(Counterexample cex, List<object /*!>!*/> x)
  {
    Contract.Requires(cce.NonNullElements(x));
    counterexample = cex;
    args = x;
  }
}