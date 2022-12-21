using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class ListComparer<T> : IEqualityComparer<List<T>>
  {
    public bool Equals(List<T> l1, List<T> l2)
    {
      if (l1.Count != l2.Count)
      {
        return false;
      }

      for (int i = 0; i < l1.Count; i++)
      {
        if (!l1[i].Equals(l2[i]))
        {
          return false;
        }
      }

      return true;
    }

    public int GetHashCode(List<T> l)
    {
      int hCode = 0;
      l.Iter(x => { hCode = hCode ^ x.GetHashCode(); });
      return hCode.GetHashCode();
    }
  }

  public class HashSetComparer<T> : IEqualityComparer<HashSet<T>>
  {
    public bool Equals(HashSet<T> l1, HashSet<T> l2)
    {
      return l1.SetEquals(l2);
    }

    public int GetHashCode(HashSet<T> l)
    {
      int hCode = 0;
      l.Iter(x => { hCode = hCode ^ x.GetHashCode(); });
      return hCode.GetHashCode();
    }
  }
}