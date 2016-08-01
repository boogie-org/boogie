using System;
using System.Collections.Generic;
using System.Collections.Concurrent;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie
{
  // Implementation of System.Threading.Tasks.TaskScheduler which creates a unique thread per
  // task, and allows each thread to have its own custom stack size.  The standard
  // scheduler uses the .NET threadpool, which in turn inherits stack size from the EXE.
  public class ThreadTaskScheduler : TaskScheduler
  {
    private object tasklock; // Guards acess to the "tasks" queue
    private Queue<Task> tasks;

    private Thread[] dispatchers;
    private ManualResetEvent eventsWaiting;
    private int stackSize;

    public ThreadTaskScheduler(int StackReserveSize)
    {
      int MaxThreads = System.Environment.ProcessorCount;
      Initialize(StackReserveSize, MaxThreads);
    }

    public ThreadTaskScheduler(int StackReserveSize, int MaxThreads) 
    {
      Initialize(StackReserveSize, MaxThreads);
    }

    void Initialize(int StackReserveSize, int MaxThreads) 
    {
      Contract.Requires(StackReserveSize >= 0);
      Contract.Requires(MaxThreads > 0);

      tasklock = new object();
      tasks = new Queue<Task>();
      eventsWaiting = new ManualResetEvent(false);
      stackSize = StackReserveSize;
      dispatchers = new Thread[MaxThreads];
      for (int i = 0; i < MaxThreads; ++i) 
      {
        dispatchers[i] = new Thread(new ThreadStart(DispatcherMain));
        dispatchers[i].IsBackground = true;
        dispatchers[i].Start();
      }
    }

    protected override IEnumerable<Task> GetScheduledTasks() 
    {
      IEnumerable<Task> r;
      lock(tasklock)
      {
        r=tasks.ToArray<Task>();
      }
      return r;
    }

    protected override void QueueTask(Task task) 
    {
      lock (tasklock) 
      {
        tasks.Enqueue(task);
        eventsWaiting.Set();
      }
    }

    protected override bool TryExecuteTaskInline(Task task, bool taskWasPreviouslyQueued) 
    {
      return false;
    }

    private void DispatcherMain() 
    {
      while (true) 
      {
        Task t = null;
        lock (tasklock) 
        {
          if (tasks.Count > 0) 
          {
            t = tasks.Dequeue();
            if (tasks.Count == 0) 
            {
              eventsWaiting.Reset();
            }
          }
        }

        if (t != null) 
        {
          Thread th = new Thread(TaskMain, stackSize);
          th.Start(t);
          th.Join();
        }
        else 
        {
          eventsWaiting.WaitOne();
        }
      }
    }

    private void TaskMain(object data) 
    {
      Task t = (Task)data;
      TryExecuteTask(t);
    }
  }
}
