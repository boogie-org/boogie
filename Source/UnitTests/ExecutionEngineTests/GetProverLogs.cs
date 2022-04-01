using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests;

public static class GetProverLogs
{
  public static async Task<string> GetProverLogForProgram(ExecutionEngineOptions options, string procedure)
  {
    var logs = await GetProverLogsForProgram(options, procedure).ToListAsync();
    Assert.AreEqual(1, logs.Count);
    return logs[0];
  }
    
  public static async IAsyncEnumerable<string> GetProverLogsForProgram(ExecutionEngineOptions options, string procedure1)
  {
    string directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    using (var engine = ExecutionEngine.CreateWithoutSharedCache(options)) {
      var defines = new List<string>() { "FILE_0" };

      // Parse error are printed to StdOut :/
      int errorCount = Parser.Parse(new StringReader(procedure1), "1", defines, out Program program1,
        engine.Options.UseBaseNameForFileName);
      Assert.AreEqual(0, errorCount);
      Directory.CreateDirectory(directory);
      var temp1 = directory + "/proverLog";
      engine.Options.ProverLogFilePath = temp1;
      engine.Options.ProverOptions.Add("SOLVER=noop");
      var success1 = await engine.ProcessProgram(Console.Out, program1, "1");
    }
    foreach (var proverFile in Directory.GetFiles(directory)) {
      yield return await File.ReadAllTextAsync(proverFile);
    }
  }
}