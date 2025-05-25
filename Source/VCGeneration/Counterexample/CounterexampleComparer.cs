using System.Collections.Generic;

namespace Microsoft.Boogie;

public class CounterexampleComparer : IComparer<Counterexample>, IEqualityComparer<Counterexample>
{
  private int Compare(List<Block> bs1, List<Block> bs2)
  {
    if (bs1.Count < bs2.Count)
    {
      return -1;
    }
    else if (bs2.Count < bs1.Count)
    {
      return 1;
    }

    for (int i = 0; i < bs1.Count; i++)
    {
      var b1 = bs1[i];
      var b2 = bs2[i];
      if (b1.tok.pos < b2.tok.pos)
      {
        return -1;
      }
      else if (b2.tok.pos < b1.tok.pos)
      {
        return 1;
      }
    }

    return 0;
  }

  public int Compare(Counterexample c1, Counterexample c2)
  {
    if (c1.GetLocation() == c2.GetLocation())
    {
      var c = Compare(c1.Trace, c2.Trace);
      if (c != 0)
      {
        return c;
      }

      // TODO(wuestholz): Generalize this to compare all Descriptions of the counterexample.
      var a1 = c1 as AssertCounterexample;
      var a2 = c2 as AssertCounterexample;
      if (a1 != null && a2 != null) {
        var s1 = a1.FailingAssert.Description?.FailureDescription;
        var s2 = a2.FailingAssert.Description?.FailureDescription;
        if (s1 != null && s2 != null)
        {
          return s1.CompareTo(s2);
        }
      }

      return 0;
    }

    if (c1.GetLocation() > c2.GetLocation())
    {
      return 1;
    }

    return -1;
  }

  public bool Equals(Counterexample x, Counterexample y)
  {
    return Compare(x, y) == 0;
  }

  public int GetHashCode(Counterexample obj)
  {
    return 0;
  }
}