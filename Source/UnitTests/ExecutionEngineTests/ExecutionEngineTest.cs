using System.IO;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests;

[TestFixture]
public class ExecutionEngineTest {

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
    var task1 = engine.ProcessProgram(task1Writer, program1, "fakeFilename");
    var task2Writer = concurrentWriterManager.AppendWriter();
    var task2 = engine.ProcessProgram(task2Writer, program2, "fakeFilename");
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
";
    Assert.AreEqual(expected, output);
  }
}