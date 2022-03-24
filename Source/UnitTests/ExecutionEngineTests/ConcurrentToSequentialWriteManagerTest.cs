using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;
using VC;

namespace ExecutionEngineTests;

[TestFixture]
public class ConcurrentToSequentialWriteManagerTest {

  [Test]
  public async Task FirstNotDisposedWriterWritesImmediately() {
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

  [Test]
  public void ThreeConcurrentWriters()
  {
    var amount = 1000;
    var writer = new StringWriter();
    var manager = new ConcurrentToSequentialWriteManager(writer);

    var first = manager.AppendWriter();
    var second = manager.AppendWriter();
    var third = manager.AppendWriter();

    var thread1 = new Thread(() =>
    {
      for (int i = 0; i < amount; i++) {
        first.WriteLine(i);
      }
      first.Dispose();
    });

    var thread2 = new Thread(() =>
    {
      for (int i = 0; i < 2 * amount; i++) {
        second.WriteLine(i);
      }
      second.Dispose();
    });

    var thread3 = new Thread(() =>
    {
      for (int i = 0; i < 3 * amount; i++) {
        third.WriteLine(i);
      }
      third.Dispose();
    });
    thread3.Start();
    thread2.Start();
    thread1.Start();
    thread1.Join();
    thread2.Join();
    thread3.Join();

    var output = writer.ToString().TrimEnd().Split("\n");

    for (int i = 0; i < amount; i++) {
      Assert.AreEqual(i.ToString(), output[i]);
    }
    for (int i = 0; i < 2 * amount; i++) {
      Assert.AreEqual(i.ToString(), output[i + amount]);
    }
    for (int i = 0; i < 3 * amount; i++) {
      Assert.AreEqual(i.ToString(), output[i + amount * 3]);
    }
  }
}