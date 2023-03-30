using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

public class CustomStackSizePoolTaskScheduler : TaskScheduler, IDisposable
{
  private readonly int threadCount;
  private readonly ConcurrentQueue<Task> queue = new();
  private readonly SemaphoreSlim isWorkAvailable = new(0);
  private readonly Thread[] threads;

  public static CustomStackSizePoolTaskScheduler Create(int stackSize, int threadCount)
  {
    return new CustomStackSizePoolTaskScheduler(stackSize, threadCount);
  }
  
  private CustomStackSizePoolTaskScheduler(int stackSize, int threadCount)
  {
    this.threadCount = threadCount;

    threads = new Thread[this.threadCount];
    for (int i = 0; i < threads.Length; i++)
    {
      threads[i] = new Thread(WorkLoop, stackSize) { IsBackground = true };
      threads[i].Start();
    }
  }

  protected override void QueueTask(Task task)
  {
    queue.Enqueue(task);
    isWorkAvailable.Release(1);
  }

  protected override bool TryExecuteTaskInline(Task task, bool taskWasPreviouslyQueued)
  {
    return TryExecuteTask(task);
  }

  public override int MaximumConcurrencyLevel => threadCount;

  protected override IEnumerable<Task> GetScheduledTasks()
  {
    return queue;
  }
  
  private void WorkLoop()
  {
    while (true)
    {
      var task = BlockUntilTaskIsAvailable();
      TryExecuteTask(task);
    }
  }

  private Task BlockUntilTaskIsAvailable()
  {
    isWorkAvailable.Wait();
    queue.TryDequeue(out var task);
    return task;
  }

  public void Dispose()
  {
    for (int i = 0; i < threads.Length; i++) {
      threads[i].Join();
    }
  }
}