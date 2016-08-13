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
    private int stackSize;

    public ThreadTaskScheduler(int StackReserveSize)
    {
      Contract.Requires(StackReserveSize >= 0);

      stackSize = StackReserveSize;
    }

    protected override IEnumerable<Task> GetScheduledTasks() 
    {
      // There is never a queue of scheduled, but not running, tasks.  
      // So return an empty list.
      return new List<Task>();
    }

    protected override void QueueTask(Task task) 
    {
      // Each queued task runs on a newly-created thread with the required 
      // stack size.  The default .NET task scheduler is built on the .NET 
      // ThreadPool.  Its policy allows it to create thousands of threads 
      // if it chooses.
      //
      // Boogie creates tasks which in turn create tasks and wait on them.
      // So throttling tasks via a queue risks deadlock.

      Thread th = new Thread(TaskMain, stackSize);
      th.Start(task);
    }

    protected override bool TryExecuteTaskInline(Task task, bool taskWasPreviouslyQueued) 
    {
      return false;
    }

    private void TaskMain(object data) 
    {
      Task t = (Task)data;
      TryExecuteTask(t);
    }
  }
}
