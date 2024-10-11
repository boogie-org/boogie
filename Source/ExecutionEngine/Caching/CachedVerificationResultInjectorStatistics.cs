using System.Collections.Concurrent;
using System.IO;
using System.Linq;

namespace Microsoft.Boogie;

sealed class CachedVerificationResultInjectorStatistics
{
  ConcurrentDictionary<string, CachedVerificationResultInjectorRun> runs =
    new ConcurrentDictionary<string, CachedVerificationResultInjectorRun>();

  public bool AddRun(string requestId, CachedVerificationResultInjectorRun run)
  {
    return runs.TryAdd(requestId, run);
  }

  public string Output(bool printTime = false)
  {
    var wr = new StringWriter();
    if (runs.Any())
    {
      wr.WriteLine("Cached verification result injector statistics as CSV:");
      wr.WriteLine("Request ID, Transformed, Low, Medium, High, Skipped{0}", printTime ? ", Time (ms)" : "");
      foreach (var kv in runs.OrderBy(kv => ExecutionEngine.AutoRequestId(kv.Key)))
      {
        var t = printTime ? string.Format(", {0,8:F0}", kv.Value.End.Subtract(kv.Value.Start).TotalMilliseconds) : "";
        wr.WriteLine("{0,-19}, {1,3}, {2,3}, {3,3}, {4,3}, {5,3}{6}", kv.Key, kv.Value.TransformedImplementationCount,
          kv.Value.LowPriorityImplementationCount, kv.Value.MediumPriorityImplementationCount,
          kv.Value.HighPriorityImplementationCount, kv.Value.SkippedImplementationCount, t);
      }
    }

    return wr.ToString();
  }
}