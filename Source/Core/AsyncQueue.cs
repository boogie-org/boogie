using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

/// <summary>
/// A queue from which items can be asynchronously dequeued before adding them. For example:
///
/// var queue = new AsyncQueue<int>()
/// var itemTask = queue.Dequeue();
/// queue.Enqueue(3);
/// Assert.AreEqual(3, await itemTask);
///
/// All methods are thread-safe.
/// Also supports pushing elements to the front of the queue.
/// </summary>
public class AsyncQueue<T>
{
  private readonly object myLock = new();
  private readonly LinkedList<T> items = new();
  private readonly SemaphoreSlim semaphore = new(0);

  public void Enqueue(T value)
  {
    lock (myLock) {
      items.AddLast(value);
    }
    semaphore.Release();
  }

  public void Push(T value)
  {
    lock (myLock) {
      items.AddFirst(value);
    }
    semaphore.Release();
  }

  public async Task<T> Dequeue(CancellationToken cancellationToken)
  {
    await semaphore.WaitAsync(cancellationToken);

    lock (myLock) {

      var first = items.First!;
      var result = first.Value;
      items.RemoveFirst();
      return result;
    }
  }

  public T[] ClearItems()
  {
    lock (myLock) {
      var clearItems = items.ToArray();
      items.Clear();
      return clearItems;
    }
  }
}
