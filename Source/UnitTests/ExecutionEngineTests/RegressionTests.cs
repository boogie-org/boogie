using System.Collections.Generic;
using System.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using Microsoft.Boogie.VCExprAST;
using NUnit.Framework;
using VC;

namespace ExecutionEngineTests
{
  [TestFixture]
  public class RegressionTests
  {
    [Test]
    public async Task NoNullPointerExceptionEvenIfConcurrencyRaces()
    {
      SMTLibOptions smtLibOptions = CommandLineOptions.FromArguments();
      VCExpressionGenerator vgen = new VCExpressionGenerator();
      VCGenerationOptions genOptions = new VCGenerationOptions(new List<string>() { });
      var smtLibProverOptions = new SMTLibSolverOptions(smtLibOptions);
      smtLibProverOptions.Solver = SolverKind.NoOpWithZ3Options;
      var smtLibInteractiveTheoremProver = new SMTLibInteractiveTheoremProver(
        smtLibOptions,
        smtLibProverOptions,
        new VCExpressionGenerator(),
        new SMTLibProverContext(vgen, genOptions, smtLibOptions)
      );
      smtLibInteractiveTheoremProver.Close();
      // No null pointer exception should arise here
      await smtLibInteractiveTheoremProver.GoBackToIdle();
      Assert.IsTrue(true);
    }
  }
}
