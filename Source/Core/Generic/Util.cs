using System;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public static class Util
  {
    public static void Shuffle<T>(Random random, IList<T> list)  
    {  
      for(var index = list.Count - 1; index > 0; index--) {
        var k = random.Next(0, index + 1); // The end is exclusive, so 0 <= k <= index
        (list[k], list[index]) = (list[index], list[k]);
      }  
    }
    
    public static string EscapeFilename(string fn)
    {
      return fn.Replace(':', '-').Replace('/', '-').Replace('\\', '-');
    }
    
    public static int GetHashCode<T1, T2>(T1 arg1, T2 arg2)
    {
      unchecked
      {
        return 31 * arg1.GetHashCode() + arg2.GetHashCode();
      }
    }
    
    public static int GetHashCode<T1, T2, T3>(T1 arg1, T2 arg2, T3 arg3)
    {
      unchecked
      {
        int hash = arg1.GetHashCode();
        hash = 31 * hash + arg2.GetHashCode();
        return 31 * hash + arg3.GetHashCode();
      }
    }

    public static int GetHashCode<T1, T2, T3, T4>(T1 arg1, T2 arg2, T3 arg3, 
      T4 arg4)
    {
      unchecked
      {
        int hash = arg1.GetHashCode();
        hash = 31 * hash + arg2.GetHashCode();
        hash = 31 * hash + arg3.GetHashCode();
        return 31 * hash + arg4.GetHashCode();
      }
    }
    
    public static int GetHashCode<T1, T2, T3, T4, T5>(T1 arg1, T2 arg2, T3 arg3, 
      T4 arg4, T5 arg5)
    {
      unchecked
      {
        int hash = arg1.GetHashCode();
        hash = 31 * hash + arg2.GetHashCode();
        hash = 31 * hash + arg3.GetHashCode();
        hash = 31 * hash + arg4.GetHashCode();
        return 31 * hash + arg5.GetHashCode();
      }
    }
    
    /**
     * A pure hash code implementation for strings, instead of the default implementation that returns different hash codes between program executions.
     */
    public static int GetDeterministicHashCode(this string str)
    {
      unchecked
      {
        int hash1 = (5381 << 16) + 5381;
        int hash2 = hash1;

        for (int i = 0; i < str.Length; i += 2)
        {
          hash1 = ((hash1 << 5) + hash1) ^ str[i];
          if (i == str.Length - 1)
          {
            break;
          }

          hash2 = ((hash2 << 5) + hash2) ^ str[i + 1];
        }

        return hash1 + (hash2 * 1566083941);
      }
    }
    
    public static V GetOrCreate<K, V>(this IDictionary<K, V> dictionary, K key, Func<V> createValue)
    {
      if (dictionary.TryGetValue(key, out var result)) {
        return result;
      }

      result = createValue();
      dictionary[key] = result;
      return result;
    }
    
    public static uint BoundedMultiply(uint a, uint b) {
      try {
        return a * b;
      } catch (OverflowException) {
        return UInt32.MaxValue;
      }
    }
  }
}