using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using Microsoft.Boogie;
using NUnit.Framework;

namespace CoreTests; 

[TestFixture]
  public class DynamicStackReturnValueTest2
  {
    [Test]
    public void SmallStackRecursiveTest()
    {
      Assert.AreEqual(2, Recursive(2).Result);
    }

    [DebuggerStepThrough]
    private DynamicStack<int> Recursive(int iterations)
    {
      StateMachine stateMachine = new StateMachine();
      stateMachine.builder = DynamicStackBuilder<int>.Create();
      stateMachine.__this = this;
      stateMachine.iterations = iterations;
      stateMachine.state = -1;
      stateMachine.builder.Start<StateMachine>(ref stateMachine);
      return stateMachine.builder.Task;
    }

    [CompilerGenerated]
    private sealed class StateMachine : IAsyncStateMachine
    {
      public int state;
      public DynamicStackBuilder<int> builder;
      public int iterations;
      public DynamicStackReturnValueTest2 __this;
      private int result5__1;
      private int recValue5__2;
      private int s__3;
      private object u__1;

      void IAsyncStateMachine.MoveNext()
      {
        int num1 = this.state;
        int result51;
        try
        {
          DynamicStack<int> awaiter;
          int num2;
          if (num1 != 0)
          {
            this.result5__1 = 1;
            if (this.iterations > 1)
            {
              awaiter = this.__this.Recursive(this.iterations - 1).GetAwaiter();
              if (!awaiter.IsCompleted)
              {
                this.state = num2 = 0;
                this.u__1 = (object) awaiter;
                StateMachine stateMachine = this;
                this.builder.AwaitOnCompleted<DynamicStack<int>, StateMachine>(ref awaiter, ref stateMachine);
                return;
              }
            }
            else
              goto label_7;
          }
          else
          {
            awaiter = (DynamicStack<int>) this.u__1;
            this.u__1 = (object) null;
            this.state = num2 = -1;
          }
          this.s__3 = awaiter.GetResult();
          this.recValue5__2 = this.s__3;
          this.result5__1 += this.recValue5__2;
label_7:
          result51 = this.result5__1;
        }
        catch (Exception ex)
        {
          this.state = -2;
          this.builder.SetException(ex);
          return;
        }
        this.state = -2;
        this.builder.SetResult(result51);
      }

      [DebuggerHidden]
      void IAsyncStateMachine.SetStateMachine(IAsyncStateMachine stateMachine)
      {
      }
    }
  }