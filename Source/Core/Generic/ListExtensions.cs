using System.Collections;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie;

public static class ListExtensions {
  public static IReadOnlyList<T> Reversed<T>(this IReadOnlyList<T> list) {
    return new ReversedReadOnlyList<T>(list);
  }
}

class ReversedReadOnlyList<T> : IReadOnlyList<T> {
  private readonly IReadOnlyList<T> inner;

  public ReversedReadOnlyList(IReadOnlyList<T> inner) {
    this.inner = inner;
  }

  public IEnumerator<T> GetEnumerator() {
    return Enumerable.Range(0, inner.Count).Select(index => this[index]).GetEnumerator();
  }

  IEnumerator IEnumerable.GetEnumerator() {
    return GetEnumerator();
  }

  public int Count => inner.Count;

  public T this[int index] => inner[^(index + 1)];
}