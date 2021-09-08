using System;
using Microsoft.Boogie;
using Microsoft.BaseTypes;
using NUnit.Framework;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace ExecutionEngineTests
{
  [TestFixture]
  public class ProofIsolation
  {
    [Test()]
    public void Implementation()
    {
      var procedure1 = @"
procedure M(x: int) 
  requires x == 2; {
  assert x + x == 4;
}";
      
      var procedure1And2 = $@"
{procedure1}

procedure N(x: int) 
  requires x == 3; {{
  assert x * x == 9;
}}";
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.Parse(new string[]{});
      ExecutionEngine.printer = new ConsolePrinter();
      
      var proverLog1 = GetProverLogForProgram(procedure1).ToList();
      CommandLineOptions.Clo.ProcsToCheck.Add("M");
      var proverLog2 = GetProverLogForProgram(procedure1And2).ToList();
      Assert.AreEqual(proverLog1.Count, proverLog2.Count);
      Assert.AreEqual(proverLog1[0], proverLog2[0]);
    }

    private static IEnumerable<string> GetProverLogForProgram(string procedure1)
    {
      var defines = new List<string>() { "FILE_0" };

      // Parse error are printed to StdOut :/
      int errorCount = Parser.Parse(new StringReader(procedure1), "1", defines, out Program program1,
        CommandLineOptions.Clo.UseBaseNameForFileName);
      string directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
      Directory.CreateDirectory(directory);
      var temp1 = directory + "/proverLog";
      CommandLineOptions.Clo.ProverLogFilePath = temp1;
      var success1 = ExecutionEngine.ProcessProgram(program1, "1");
      foreach (var proverFile in Directory.GetFiles(directory)) {
        yield return File.ReadAllText(proverFile);
      }
    }
  }  
}

