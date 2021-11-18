using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using NUnit.Framework;
using VC;

namespace ExecutionEngineTests {
  [TestFixture]
  public class Splits {
    [Test]
    public void FindManualSplits() {
      var procedure1 = @"
procedure M() {
  assert               0 + 0 == 0;
  assert {:split_here} 1 + 1 == 2;
  assert               2 + 3 == 5;
  assert {:split_here} 1 + 1 == 2;
  assert               2 + 2 == 5;
  assert {:split_here} 3 + 3 == 33;
}";
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.Parse(new string[]{});
      ExecutionEngine.printer = new ConsolePrinter();
      
      var defines = new List<string>() { "FILE_0" };
      int errorCount = Parser.Parse(new StringReader(procedure1), "1", defines, out Program program,
        CommandLineOptions.Clo.UseBaseNameForFileName);
      PipelineOutcome oc = ExecutionEngine.ResolveAndTypecheck(program, "FILE_0", out var civlTypeChecker);
      Assert.AreEqual(PipelineOutcome.ResolvedAndTypeChecked, oc);
      
      var implementation = program.Implementations.Single();
      
      var checkerPool = new CheckerPool(CommandLineOptions.Clo);
      var vcGen = new VCGen(program, checkerPool);
      var gotoCmdOrigins = vcGen.PassifyImpl(implementation, out var mvInfo);
      var initialSplit = new Split(implementation.Blocks, gotoCmdOrigins, vcGen, implementation);
      var manualSplits = Split.FindManualSplits(initialSplit, false);
      // TODO: Actual assertions, I just used this to debug and understand the splitting logic for now
    }
  }
}