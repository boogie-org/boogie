using System;
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
  
  private async void WorkLoop()
  {
    while (true)
    {
      try
      {
        var task = await queue.Dequeue(disposeTokenSource.Token);
        TryExecuteTask(task);
      }
      catch (TaskCanceledException)
      {
        break;
      }
    }
  }

  public void Dispose()
  {
    disposeTokenSource.Cancel();
    foreach (var thread in threads)
    {
      thread.Join();
    }
  }
}