using System.IO;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests;

[TestFixture]
public class ConcurrentToSequentialWriteManagerTest {

  [Test]
  public async Task ThreeConcurrentWriters() {
    var writer = new StringWriter();
    var manager = new ConcurrentToSequentialWriteManager(writer);

    var first = manager.AppendWriter();
    var second = manager.AppendWriter();
    var third = manager.AppendWriter();

    await second.WriteLineAsync("secondLine1");
    await first.WriteLineAsync("firstLine1");
    Assert.AreEqual("firstLine1\n", writer.ToString().Replace("\r\n", "\n"));

    await first.DisposeAsync();
    await second.WriteLineAsync("secondLine2");
    await third.WriteLineAsync("thirdLine1");
    Assert.AreEqual("firstLine1\nsecondLine1\nsecondLine2\n", writer.ToString().Replace("\r\n", "\n"));
    await second.DisposeAsync();
    Assert.AreEqual("firstLine1\nsecondLine1\nsecondLine2\nthirdLine1\n", writer.ToString().Replace("\r\n", "\n"));
  }
}