using System;
using System.Collections.Generic;
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
  // At all times, either items or customers is empty.
  private readonly LinkedList<T> items = new();
  private readonly Queue<TaskCompletionSource<T>> customers = new();

  public void Enqueue(T value)
  {
    lock (this) {
      if (TryEnqueue(value))
      {
        return;
      }

      items.AddLast(value);
    }
  }

  private bool TryEnqueue(T value)
  {
    while (customers.TryDequeue(out var customer)) {
      if (customer.TrySetResult(value)) {
        return true;
      }
    }

    return false;
  }

  public void Push(T value)
  {
    lock (myLock) {
      if (TryEnqueue(value))
      {
        return;
      }
      items.AddFirst(value);
    }
  }

  public Task<T> Dequeue(CancellationToken cancellationToken)
  {
    lock (myLock) {
      var first = items.First;
      if (first != null) {
        var result = first.Value;
        items.RemoveFirst();
        return Task.FromResult(result);
      }

      var source = new TaskCompletionSource<T>();
      cancellationToken.Register(() => source.SetCanceled(cancellationToken));
      customers.Enqueue(source);
      // Ensure that the TrySetResult call in Enqueue completes immediately.
      return source.Task.ContinueWith(t => t.Result, cancellationToken,
        TaskContinuationOptions.RunContinuationsAsynchronously, TaskScheduler.Current);
    }
  }

  public T[] ClearItems()
  {
    lock (myLock) {
      var result = new T[items.Count];
      items.CopyTo(result, 0);
      items.Clear();
      return result;
    }
  }
}
