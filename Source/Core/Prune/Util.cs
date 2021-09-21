using System;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public static class Util
  {
    public static V GetOrCreate<K, V>(this IDictionary<K, V> dictionary, K key, Func<V> createValue)
    {
      if (dictionary.TryGetValue(key, out var result)) {
        return result;
      }

      result = createValue();
      dictionary[key] = result;
      return result;
    }
    
    public static uint SafeMult(uint a, uint b) {
      uint result = UInt32.MaxValue;
      try {
        checked {
          result = a * b;
        }
      } catch (OverflowException) { }

      return result;
    }
  }
}