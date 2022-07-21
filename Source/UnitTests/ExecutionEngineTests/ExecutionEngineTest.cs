using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
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
    var result1 = await tasks[0].TryRun()!.ToTask();
    var verificationResult1 = ((Completed)result1).Result;
    Assert.AreEqual(ConditionGeneration.Outcome.Errors, verificationResult1.Outcome);
    Assert.AreEqual(true, verificationResult1.Errors[0].Model.ModelHasStatesAlready);

    Assert.IsTrue(tasks[1].IsIdle);
    var runningStates = tasks[1].TryRun()!;
    Assert.IsFalse(tasks[1].IsIdle);
    var result2 = await runningStates.ToTask();
    Assert.IsTrue(tasks[1].IsIdle);
    var verificationResult2 = ((Completed)result2).Result;
    Assert.AreEqual(ConditionGeneration.Outcome.Correct, verificationResult2.Outcome);
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
      var result = writer.ToString();
      Assert.AreEqual(expected, result, $"iteration {i}, result {result}");
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
  public async Task RunCancelRunCancel() {
    var options = CommandLineOptions.FromArguments();
    options.VcsCores = 1;
    options.CreateSolver = (_, _) => new UnsatSolver(new SemaphoreSlim(0));
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var source = @"
procedure Foo(x: int) {
  assert true;
}".TrimStart();
    var result = Parser.Parse(source, "fakeFilename1", out var program);
    Assert.AreEqual(0, result);
    var tasks = engine.GetImplementationTasks(program)[0];
    var statusList1 = new List<IVerificationStatus>();
    var firstStatuses = tasks.TryRun()!;
    await firstStatuses.Where(s => s is Running).FirstAsync().ToTask();
    firstStatuses.Subscribe(statusList1.Add);
    tasks.Cancel();

    var secondStatuses = tasks.TryRun()!;
    tasks.Cancel();
    var statusList2 = new List<IVerificationStatus>();
    secondStatuses.Subscribe(statusList2.Add);
    await secondStatuses.DefaultIfEmpty().ToTask();
    var expected1 = new List<IVerificationStatus>() {
      new Running(), new Stale()
    };
    Assert.AreEqual(expected1, statusList1);
    var expected2 = new List<IVerificationStatus>() {
      new Stale()
    };
    Assert.AreEqual(expected2, statusList2.TakeLast(1));
  }

  [Test]
  public async Task RunRunCancelRunRun() {
    var options = CommandLineOptions.FromArguments();
    var returnCheckSat = new SemaphoreSlim(0);
    options.VcsCores = 1;
    options.CreateSolver = (_, _) => new UnsatSolver(returnCheckSat);
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var source = @"
procedure Foo(x: int) {
  assert true;
}".TrimStart();
    var result = Parser.Parse(source, "fakeFilename1", out var program);
    Assert.AreEqual(0, result);
    var tasks = engine.GetImplementationTasks(program)[0];
    var statusList1 = new List<IVerificationStatus>();
    var firstStatuses = tasks.TryRun()!;
    var runAfterRun1 = tasks.TryRun();
    Assert.AreEqual(null, runAfterRun1);
    firstStatuses.Subscribe(statusList1.Add);
    tasks.Cancel();

    var secondStatuses = tasks.TryRun()!;
    var runAfterRun2 = tasks.TryRun();
    Assert.AreEqual(null, runAfterRun2);
    var statusList2 = new List<IVerificationStatus>();
    secondStatuses.Subscribe(statusList2.Add);
    returnCheckSat.Release();
    var finalResult = await secondStatuses.ToTask();
    Assert.IsTrue(finalResult is Completed);
    var expected1 = new List<IVerificationStatus>() {
      new Running(), new Stale()
    };
    Assert.AreEqual(expected1, statusList1);
    var expected2 = new List<IVerificationStatus>() {
      new Running(), finalResult
    };
    Assert.AreEqual(expected2, statusList2.Where(s => s is not Queued));
  }

  [Test]
  public async Task StatusTest() {
    
    var options = CommandLineOptions.FromArguments();
    options.VcsCores = 1;
    options.VerifySnapshots = 1;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var programString = @"procedure {:priority 3} {:checksum ""stable""} Bad(y: int)
{
  assert 2 == 1;
}

procedure {:priority 2} {:checksum ""stable""} Good(y: int)
{
  assert 2 == 2;
}
";
    Parser.Parse(programString, "fakeFilename1", out var program);
    Assert.AreEqual("Bad", program.Implementations.ElementAt(0).Name);
    var tasks = engine.GetImplementationTasks(program);
    var statusList = new List<(string, IVerificationStatus)>();

    var first = tasks[0];
    var second = tasks[1];
    var firstName = first.Implementation.Name;
    var secondName = second.Implementation.Name;
    Assert.AreEqual("Bad", firstName);
    Assert.AreEqual("Good", secondName);

    Assert.True(first.CacheStatus is Stale);
    Assert.True(second.CacheStatus is Stale);

    var firstStatuses = first.TryRun()!;
    firstStatuses.Subscribe(t => statusList.Add(new (firstName, t)));
    var secondStatuses = second.TryRun()!;
    secondStatuses.Subscribe(t => statusList.Add((secondName, t)));
    await firstStatuses.Concat(secondStatuses).ToTask();

    Assert.AreEqual((firstName, new Running()), statusList[0]);
    Assert.AreEqual((secondName, new Queued()), statusList[1]);
    var indexTwoAndThreeOrdered = statusList.Skip(2).Take(2).OrderByDescending(k => k.Item1 == firstName).ToList();
    Assert.AreEqual(firstName, indexTwoAndThreeOrdered[0].Item1);
    Assert.IsTrue(indexTwoAndThreeOrdered[0].Item2 is Completed);
    Assert.AreEqual((secondName, new Running()), indexTwoAndThreeOrdered[1]);
    Assert.AreEqual(secondName, statusList[4].Item1);
    Assert.IsTrue(statusList[4].Item2 is Completed);
    
    var tasks2 = engine.GetImplementationTasks(program);
    Assert.True(tasks2[0].CacheStatus is Completed);
    Assert.AreEqual(ConditionGeneration.Outcome.Errors, ((Completed)tasks2[0].CacheStatus).Result.Outcome);

    Assert.True(tasks2[1].CacheStatus is Completed);
    Assert.AreEqual(ConditionGeneration.Outcome.Correct, ((Completed)tasks2[1].CacheStatus).Result.Outcome);
  }
}