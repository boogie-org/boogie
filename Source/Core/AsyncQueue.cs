using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

/// <summary>
/// A queue from which items can be dequeued even if they have not been enqueued yet.
/// All methods are thread-safe.
/// Also supports pushing elements to the front of the queue.
/// </summary>
public class AsyncQueue<T>
{
  private readonly LinkedList<T> items = new();
  private readonly Queue<TaskCompletionSource<T>> customers = new();

  public void Enqueue(T value)
  {
    lock (this) {
      while (customers.TryDequeue(out var customer)) {
        if (customer.TrySetResult(value)) {
          return;
        }
      }
      items.AddLast(value);
    }
  }

  public void Push(T value)
  {
    lock (this) {
      while (customers.TryDequeue(out var customer)) {
        if (customer.TrySetResult(value)) {
          return;
        }
      }
      items.AddFirst(value);
    }
  }

  public Task<T> DequeueAsync(CancellationToken cancellationToken)
  {
    lock (this) {
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
    lock (this) {
      var result = new T[items.Count];
      items.CopyTo(result, 0);
      items.Clear();
      return result;
    }
  }
}