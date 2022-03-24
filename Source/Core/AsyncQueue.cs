using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

/// <summary>
/// A queue from which
/// Items can be retrieved from the queue even if they have not been added yet.
/// </summary>
public class AsyncQueue<T>
{
  private readonly Queue<T> items = new();
  private readonly Queue<TaskCompletionSource<T>> customers = new();

  public void Enqueue(T value)
  {
    lock (this) {
      while (customers.TryDequeue(out var customer)) {
        if (customer.TrySetResult(value)) {
          return;
        }
      }
      items.Enqueue(value);
    }
  }

  public Task<T> Dequeue(CancellationToken cancellationToken)
  {
    lock (this) {
      if (items.TryDequeue(out var item)) {
        return Task.FromResult(item);
      }

      var source = new TaskCompletionSource<T>();
      cancellationToken.Register(() => source.SetCanceled(cancellationToken));
      customers.Enqueue(source);
      // Ensure that the TrySetResult call in Enqueue completes immediately.
      return source.Task.ContinueWith(t => t.Result, TaskContinuationOptions.RunContinuationsAsynchronously);
    }
  }

  public T[] ClearItems()
  {
    lock (this) {
      var result = items.ToArray();
      items.Clear();
      return result;
    }
  }
}