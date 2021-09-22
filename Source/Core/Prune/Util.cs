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
    
    public static uint BoundedMultiply(uint a, uint b) {
      try {
        return a * b;
      } catch (OverflowException) {
        return UInt32.MaxValue;
      }
    }
  }
}