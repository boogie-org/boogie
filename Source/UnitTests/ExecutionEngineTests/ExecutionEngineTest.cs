using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.VisualStudio.TestPlatform.Common.Utilities;
using NUnit.Framework;
using VC;


namespace ExecutionEngineTests;

public class FakeDescription : ProofObligationDescription
{
  public override string SuccessDescription => "fake success";
  public override string FailureDescription => "fake failure";
  public override string ShortDescription => "fake";
}

[TestFixture]
public class ExecutionEngineTest {

  [Test]
  public async Task GetImplementationTasksTest() {
    var programString = @"
procedure First(y: int)
{
  assert 2 == 1;
}

procedure Second(y: int)
{
  assert 2 == 2;
}
".Trim();
    Parser.Parse(programString, "fakeFilename10", out var program);
    var options = CommandLineOptions.FromArguments();
    options.PrintErrorModel = 1;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    var tasks = engine.GetImplementationTasks(program);
    Assert.AreEqual(2, tasks.Count);
    Assert.NotNull(tasks[0].Implementation);
    tasks[0].Run();
    var firstResult = await tasks[0].ActualTask;
    Assert.AreEqual(ConditionGeneration.Outcome.Errors, firstResult.Outcome);
    Assert.AreEqual(true, firstResult.Errors[0].Model.ModelHasStatesAlready);

    tasks[1].Run();
    tasks[1].Cancel();
    Assert.CatchAsync<TaskCanceledException>(() => tasks[1].ActualTask);
  }

  [Test]
  public async Task VerifyProceduresConcurrently()
  {

    var programString = @"procedure Bad(y: int)
{
  assert 2 == 1;
}

procedure Bad2(y: int)
{
  assert 2 == 3;
}
";
    var options = CommandLineOptions.FromArguments();
    options.VcsCores = 4;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var expected = @"fakeFilename1(3,3): Error: This assertion might not hold.
Execution trace:
    fakeFilename1(3,3): anon0
fakeFilename1(8,3): Error: This assertion might not hold.
Execution trace:
    fakeFilename1(8,3): anon0

Boogie program verifier finished with 0 verified, 2 errors
".ReplaceLineEndings();

    for (int i = 0; i < 300; i++) {
      var writer = new StringWriter();
      Parser.Parse(programString, "fakeFilename1", out var program);
      await engine.ProcessProgram(writer, program, "fakeFilename");
      Assert.AreEqual(expected, writer.ToString());
    }
  }

  [Test]
  public async Task ConcurrentInferAndVerifyCalls() {
    var options = CommandLineOptions.FromArguments();
    options.VcsCores = 4;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var writer = new StringWriter();
    var concurrentWriterManager = new ConcurrentToSequentialWriteManager(writer);

    var programString = @"procedure Bad(y: int)
{
  assert 2 == 1;
}

procedure Good(y: int)
{
  assert 2 == 2;
}
";
    Parser.Parse(programString, "fakeFilename1", out var program1);
    Parser.Parse(programString, "fakeFilename2", out var program2);
    var task1Writer = concurrentWriterManager.AppendWriter();
    var task1 = engine.ProcessProgram(task1Writer, program1, "fakeFilename1");
    var task2Writer = concurrentWriterManager.AppendWriter();
    var task2 = engine.ProcessProgram(task2Writer, program2, "fakeFilename2");
    await Task.WhenAll(task1, task2);

    await task1Writer.DisposeAsync();
    await task2Writer.DisposeAsync();
    var output = writer.ToString();
    var expected = @"fakeFilename1(3,3): Error: This assertion might not hold.
Execution trace:
    fakeFilename1(3,3): anon0

Boogie program verifier finished with 1 verified, 1 error
fakeFilename2(3,3): Error: This assertion might not hold.
Execution trace:
    fakeFilename2(3,3): anon0

Boogie program verifier finished with 1 verified, 1 error
".ReplaceLineEndings();
    Assert.AreEqual(expected, output);
  }

  [Test]
  public async Task LoopInvariantDescriptions()
  {
    var options = CommandLineOptions.FromArguments();
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var writer = new StringWriter();

    var programString = @"procedure Test()
{
  var i: int;

  entry:
    i := 0;
    goto block850;

  block850:
    assert i == 0;
    havoc i;
    goto block850;

}
";

    Parser.Parse(programString, "fakeFilename", out var program1);
    foreach (var block in program1.Implementations.First().Blocks) {
      foreach (var cmd in block.cmds) {
        if (cmd is AssertCmd assertCmd) {
          assertCmd.Description = new FakeDescription();
        }
      }
    }

    await engine.ProcessProgram(writer, program1, "fakeFilename");
    await writer.DisposeAsync();
    var output = writer.ToString();
    var expected = @"fakeFilename(10,5): Error: This loop invariant might not be maintained by the loop.
fakeFilename(10,5): Related message: fake failure
Execution trace:
    fakeFilename(5,3): entry
    fakeFilename(9,3): block850

Boogie program verifier finished with 0 verified, 1 error
".ReplaceLineEndings();

    Assert.AreEqual(expected, output);
  }

  [Test]
  public async Task StatusTest() {
    
    var options = CommandLineOptions.FromArguments();
    options.VcsCores = 1;
    options.VerifySnapshots = 1;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var programString = @"procedure {:checksum ""stable""} Bad(y: int)
{
  assert 2 == 1;
}

procedure {:checksum ""stable""} Good(y: int)
{
  assert 2 == 2;
}
";
    Parser.Parse(programString, "fakeFilename1", out var program1);
    var tasks = engine.GetImplementationTasks(program1);
    var statusList = new List<(ImplementationTask, VerificationStatus)>();

    var first = tasks[0];
    var second = tasks[1];
    var statuses = first.ObservableStatus.Select(s => (implementationTask: first, s)).
      Merge(second.ObservableStatus.Select(status => (second, s: status)));
    statuses.Subscribe(t => statusList.Add(t));
    
    first.Run();
    second.Run();
    await statuses.ToTask();
    
    Assert.True(statusList.SequenceEqual(new[] {
      (first, VerificationStatus.Verifying),
      (second, VerificationStatus.Queued),
      (first, VerificationStatus.Error),
      (second, VerificationStatus.Verifying),
      (second, VerificationStatus.Correct),
    }));
    
    var tasks2 = engine.GetImplementationTasks(program1);
    Assert.AreEqual(VerificationStatus.Error, tasks2[0].CurrentStatus);
    Assert.AreEqual(VerificationStatus.Correct, tasks2[1].CurrentStatus);
    var statuses2 = first.ObservableStatus.Merge(second.ObservableStatus);
    Assert.IsFalse(await statuses2.Any().ToTask());
  }
}