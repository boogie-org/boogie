using System.Collections.Generic;
using System.IO;
using System.Reflection;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests
{
  [TestFixture]
  public class SolverVerificationCancellationTest
  {
    public Program GetProgram(string filename) {
      var options = CommandLineOptions.FromArguments();
      CommandLineOptions.Install(options);
      var assembly = Assembly.GetExecutingAssembly();
      var stream = assembly.GetManifestResourceStream($"ExecutionEngineTests.testfiles.{filename}.bpl");
      Assert.IsNotNull(stream);
      var code = new StreamReader(stream).ReadToEnd();
      var defines = new List<string>() { "FILE_0" };
      int errorCount = Parser.Parse(new StreamReader(code), "1", defines, out Program program,
        CommandLineOptions.Clo.UseBaseNameForFileName);
      Assert.AreEqual(0, errorCount);
      
      ExecutionEngine.EliminateDeadVariables(program);
      ExecutionEngine.CollectModSets(program);
      ExecutionEngine.CoalesceBlocks(program);
      ExecutionEngine.Inline(program);
      return program;
    }
    
    [Test()]
    public void BoogieCorrectlyCancelsProvers() {
      var infiniteProgram = GetProgram("cancellation-token-test");
      var terminatingProgram = GetProgram("cancellation-token-test-succeed");
      
      // We limit the number of checkers to 1.
      CommandLineOptions.Clo.VcsCores = 1;

      var requestId = ExecutionEngine.FreshRequestId();
      Task.Run(() => {
        var statistics = new PipelineStatistics();
        return ExecutionEngine.InferAndVerify(infiniteProgram, statistics, requestId, null, requestId);
      });
      Task.Delay(2000);
      ExecutionEngine.CancelRequest(requestId);
      var statistics = new PipelineStatistics();
      var requestId2 = ExecutionEngine.FreshRequestId();
      ExecutionEngine.InferAndVerify(terminatingProgram, statistics, requestId2, null, requestId2);
      // This test should terminate.
    }
  }  
}

