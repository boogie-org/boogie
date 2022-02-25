using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests;

public static class GetProverLogs
{
  public static string GetProverLogForProgram(ExecutionEngineOptions options, string procedure)
  {
    var logs = GetProverLogsForProgram(options, procedure).ToList();
    Assert.AreEqual(1, logs.Count);
    return logs[0];
  }
    
  public static IEnumerable<string> GetProverLogsForProgram(ExecutionEngineOptions options, string procedure1)
  {
    using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    ExecutionEngine.printer = new ConsolePrinter(engine.Options);
    var defines = new List<string>() { "FILE_0" };

    // Parse error are printed to StdOut :/
    int errorCount = Parser.Parse(new StringReader(procedure1), "1", defines, out Program program1,
      engine.Options.UseBaseNameForFileName);
    Assert.AreEqual(0, errorCount);
    string directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    var temp1 = directory + "/proverLog";
    engine.Options.ProverLogFilePath = temp1;
    engine.Options.ProverOptions.Add("SOLVER=noop");
    var success1 = engine.ProcessProgram(program1, "1");
    foreach (var proverFile in Directory.GetFiles(directory)) {
      yield return File.ReadAllText(proverFile);
    }
  }
}