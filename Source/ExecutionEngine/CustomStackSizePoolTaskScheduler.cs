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
  private readonly AsyncQueue<Task> queue = new();
  private readonly HashSet<Thread> threads;

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
      var thread = new Thread(WorkLoop, stackSize) { IsBackground = true };
      threads.Add(thread);
      thread.Start();
    }

    var b = 3;
  }

  protected override void QueueTask(Task task)
  {
    queue.Enqueue(task);
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
    return queue.Items;
  }
  
  private void WorkLoop()
  {
    while (true)
    {
      var task = queue.Dequeue(CancellationToken.None).Result;
      TryExecuteTask(task);
    }
  }

  public void Dispose()
  {
    foreach (var thread in threads)
    {
      thread.Join();
    }
  }
}