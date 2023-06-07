using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie
{
  public static class CollectionExtensions
  {
    public static void ForEach<T>(this IEnumerable<T> coll, Action<T> action)
    {
      foreach (var e in coll)
      {
        action(e);
      }
    }
    
    public static Dictionary<T, U> MapTo<T,U>(this IEnumerable<T> keys, IEnumerable<U> values)
    {
      return keys.Zip(values).ToDictionary(x => x.Item1, x => x.Item2);
    }
  }
}