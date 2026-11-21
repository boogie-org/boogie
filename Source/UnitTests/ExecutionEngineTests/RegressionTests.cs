using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading;
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
    // #1133 sibling: a CurrentCulture Convert.ToDouble rejects the dotted
    // "/vcsMaxCost:2.5" under comma-decimal locales like fr-FR/pt-PT.
    [Test]
    public void GetDoubleArgumentParsesInvariantUnderCommaDecimalLocale()
    {
      var originalCulture = Thread.CurrentThread.CurrentCulture;
      try
      {
        Thread.CurrentThread.CurrentCulture = new CultureInfo("fr-FR");

        var options = new CommandLineOptions(TextWriter.Null, new ConsolePrinter());
        var ok = options.Parse(new[] { "/vcsMaxCost:2.5" });

        Assert.IsTrue(ok, "Parsing /vcsMaxCost:2.5 should succeed under fr-FR");
        Assert.AreEqual(2.5, options.VcsMaxCost, "VcsMaxCost should be 2.5, not the 1.0 default");
      }
      finally
      {
        Thread.CurrentThread.CurrentCulture = originalCulture;
      }
    }

    // #1133 sibling (Turkish-I): a CurrentCulture ToLower turns "YICES2" into
    // "yıces2" under tr-TR, so the solver keyword fails to match.
    [Test]
    public void SolverOptionParsesInvariantUnderTurkishLocale()
    {
      var originalCulture = Thread.CurrentThread.CurrentCulture;
      try
      {
        Thread.CurrentThread.CurrentCulture = new CultureInfo("tr-TR");

        SMTLibOptions smtLibOptions = CommandLineOptions.FromArguments(TextWriter.Null);
        var proverOptions = new SMTLibSolverOptions(smtLibOptions);

        Assert.DoesNotThrow(() => proverOptions.Parse(new[] { "SOLVER=YICES2" }),
          "Parsing SOLVER=YICES2 should not throw under tr-TR");
        Assert.AreEqual(SolverKind.YICES2, proverOptions.Solver);
      }
      finally
      {
        Thread.CurrentThread.CurrentCulture = originalCulture;
      }
    }

    [Test]
    public async Task NoNullPointerExceptionEvenIfConcurrencyRaces()
    {
      SMTLibOptions smtLibOptions = CommandLineOptions.FromArguments(TextWriter.Null);
      VCExpressionGenerator vgen = new VCExpressionGenerator();
      VCGenerationOptions genOptions = new VCGenerationOptions(smtLibOptions, new List<string>() { });
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
