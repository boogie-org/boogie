using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace VC;

class BlockListComparer : IEqualityComparer<List<Block>>
{
  public bool Equals(List<Block> x, List<Block> y)
  {
    return x == y || x.SequenceEqual(y);
  }

  public int GetHashCode(List<Block> obj)
  {
    int h = 0;
    Contract.Assume(obj != null);
    foreach (var b in obj)
    {
      if (b != null)
      {
        h += b.GetHashCode();
      }
    }

    return h;
  }
}