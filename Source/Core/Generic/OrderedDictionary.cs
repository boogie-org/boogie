using System.Collections;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie;

public class OrderedDictionary<TKey, TValue> : IEnumerable<KeyValuePair<TKey, TValue>> {
  private readonly Dictionary<TKey, TValue> mapping = new();
  private readonly List<TKey> orderedKeys = new();

  public void Add(TKey key, TValue value) {
    orderedKeys.Add(key);
    mapping[key] = value;
  }

  public bool ContainsKey(TKey key) {
    return mapping.ContainsKey(key);
  }

  public TValue this[TKey key] => mapping[key];

  public IEnumerable<TKey> Keys => orderedKeys;
  public IEnumerable<TValue> Values => orderedKeys.Select(k => mapping[k]);
  public IEnumerator<KeyValuePair<TKey, TValue>> GetEnumerator() {
    return mapping.GetEnumerator();
  }

  IEnumerator IEnumerable.GetEnumerator() {
    return GetEnumerator();
  }
}