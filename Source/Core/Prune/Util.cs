using System;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public static class Util
  {
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
            break;
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