#nullable enable
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
/// </summary>
public class AsyncQueue<T>
{
  private readonly object myLock = new();
  // At all times, either items or customers is empty.
  private readonly Queue<T> items = new();
  private readonly Queue<TaskCompletionSource<T>> customers = new();

  public void Enqueue(T value)
  {
    lock (myLock) {
      while (customers.TryDequeue(out var customer)) {
        if (customer.TrySetResult(value)) {
          return;
        }
      }

      items.Enqueue(value);
    }
  }

  public IEnumerable<T> Items
  {
    get
    {
      lock (myLock)
      {
        return items.ToArray();
      }
    }
  }

  public void Clear() {
    while (customers.TryDequeue(out var customer)) {
      customer.TrySetCanceled();
    }
  }

  public int Size => items.Count;

  public Task<T> Dequeue()
  {
    lock (myLock) {
      if (items.TryDequeue(out var result)) {
        return Task.FromResult(result);
      }

      var source = new TaskCompletionSource<T>();
      customers.Enqueue(source);
      // Ensure that the TrySetResult call in Enqueue completes immediately.
      return source.Task.ContinueWith(t => t.Result, CancellationToken.None,
        TaskContinuationOptions.RunContinuationsAsynchronously, TaskScheduler.Current);
    }
  }
}
