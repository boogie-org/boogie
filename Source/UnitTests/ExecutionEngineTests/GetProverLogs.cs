using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests;

public static class GetProverLogs
{
  public static string GetProverLogForProgram(CommandLineOptions options, string procedure)
  {
    CommandLineOptions.Install(options);
    var logs = GetProverLogsForProgram(procedure).ToList();
    Assert.AreEqual(1, logs.Count);
    return logs[0];
  }
    
  public static IEnumerable<string> GetProverLogsForProgram(string procedure1)
  {
    ExecutionEngine.printer = new ConsolePrinter();
    var defines = new List<string>() { "FILE_0" };

    // Parse error are printed to StdOut :/
    int errorCount = Parser.Parse(new StringReader(procedure1), "1", defines, out Program program1,
      CommandLineOptions.Clo.UseBaseNameForFileName);
    Assert.AreEqual(0, errorCount);
    string directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    var temp1 = directory + "/proverLog";
    CommandLineOptions.Clo.ProverLogFilePath = temp1;
    CommandLineOptions.Clo.ProverOptions.Add("SOLVER=noop");
    var success1 = ExecutionEngine.ProcessProgram(program1, "1");
    foreach (var proverFile in Directory.GetFiles(directory)) {
      yield return File.ReadAllText(proverFile);
    }
  }
}