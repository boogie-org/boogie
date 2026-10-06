using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

/// <summary>
/// Uses a thread pool of a configurable size, with threads with a configurable stack size,
/// to queue tasks.
/// </summary>
public class CustomStackSizePoolTaskScheduler : TaskScheduler, IDisposable
{
  private readonly BlockingCollection<Task> queue = new();
  private readonly HashSet<Thread> threads;
  private readonly CancellationTokenSource disposeTokenSource = new();

  public static CustomStackSizePoolTaskScheduler Create(int stackSize, int threadCount)
  {
    return new CustomStackSizePoolTaskScheduler(stackSize, threadCount);
  }
  
  private CustomStackSizePoolTaskScheduler(int stackSize, int maximumConcurrencyLevel)
  {
    MaximumConcurrencyLevel = maximumConcurrencyLevel;

    threads = new HashSet<Thread>();
    for (int i = 0; i < maximumConcurrencyLevel; i++)
    {
      var thread = new Thread(WorkLoop, stackSize)
      {
        IsBackground = true,
        Name = $"CustomStackSizePoolTaskScheduler thread #{i+1}/{maximumConcurrencyLevel}"
      };
      threads.Add(thread);
      thread.Start();
    }
  }

  protected override void QueueTask(Task task)
  {
    queue.Add(task);
  }

  protected override bool TryExecuteTaskInline(Task task, bool taskWasPreviouslyQueued)
  {
    if (threads.Contains(Thread.CurrentThread)) {
      return TryExecuteTask(task);
    }

    return false;
  }

  public override int MaximumConcurrencyLevel { get; }

  protected override IEnumerable<Task> GetScheduledTasks()
  {
    return queue.ToArray();
  }
  
  private void WorkLoop()
  {
    while (!disposeTokenSource.IsCancellationRequested)
    {
      /*
       * Previously the code from RunItem was inlined, but that caused something akin to a memory leak.
       * It seems that variables declared inside the loop are not cleared across loop iterations
       * So values assigned in iteration X can only be garbage collected until they have been reassigned
       * in iteration X+1. If there is a long pause between that reassignment, which is the case here,
       * then it may take a long time before dead memory can be garbage collected.
       *
       * Inlining RunItem and manually setting variables to null at the end of the loop body does not work,
       * probably because such assignments are removed during C# compilation since they seem unused.
       */
      RunItem();
    }
  }

  private void RunItem()
  {
    try
    {
      var task = queue.Take(disposeTokenSource.Token);
      TryExecuteTask(task);
    }
    catch (OperationCanceledException)
    {
      // Disposing this scheduler cancels the wait for the next task
    }
  }

  /// <summary>
  /// Stops the threads from taking tasks: an idle thread ends at once, and a busy one once its task is done.
  /// A task that is still queued is not run.
  /// </summary>
  public void Dispose()
  {
    disposeTokenSource.Cancel();
  }
}