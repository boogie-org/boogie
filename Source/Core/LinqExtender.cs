using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie
{
  public static class LinqExtender
  {
    
    public static string Concat(this IEnumerable<string> strings, string separator)
    {
      var sb = new StringBuilder();
      var first = true;
      foreach (var s in strings)
      {
        if (!first)
        {
          sb.Append(separator);
        }

        first = false;
        sb.Append(s);
      }

      return sb.ToString();
    }

    public static IEnumerable<T> Concat1<T>(this IEnumerable<T> objects, T final)
    {
      foreach (var s in objects)
      {
        yield return s;
      }

      yield return final;
    }

    public static string MapConcat<T>(this IEnumerable<T> objects, Func<T, string> toString, string separator)
    {
      var sb = new StringBuilder();
      var first = true;
      foreach (var s in objects)
      {
        if (!first)
        {
          sb.Append(separator);
        }

        first = false;
        sb.Append(toString(s));
      }

      return sb.ToString();
    }

    public static IEnumerable<T> SkipEnd<T>(this IEnumerable<T> source, int count)
    {
      var l = source.ToList();
      if (count >= l.Count)
      {
        return Enumerable.Empty<T>();
      }

      l.RemoveRange(l.Count - count, count);
      return l;
    }

    public static void Iter<T>(this IEnumerable<T> coll, Action<T> fn)
    {
      foreach (var e in coll)
      {
        fn(e);
      }
    }

    public static IEnumerable<Tuple<TSource1, TSource2>> Zip<TSource1, TSource2>(this IEnumerable<TSource1> source1,
      IEnumerable<TSource2> source2)
    {
      return source1.Zip(source2, (e1, e2) => new Tuple<TSource1, TSource2>(e1, e2));
    }
    
    /// <summary>
    /// Creates a map from telems to uelems.  telems and uelems must have the same number of elements.
    /// </summary>
    /// <param name="telems"></param>
    /// <param name="uelems"></param>
    /// <typeparam name="T"></typeparam>
    /// <typeparam name="U"></typeparam>
    /// <returns></returns>
    public static Dictionary<T, U> Map<T,U>(IEnumerable<T> telems, IEnumerable<U> uelems)
    {
      return telems.Zip(uelems).ToDictionary(x => x.Item1, x => x.Item2);
    }
  }
}