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
    [TestCase("exists", false, false)]
    [TestCase("forall", false, false)]
    [TestCase("exists", true, false)]
    [TestCase("forall", true, true)]
    public async Task BooleanEqualityExposesSkolemization(string quantifier, bool reverse, bool negate)
    {
      var quantified = $@"({quantifier} x: int :: {{:add_to_pool ""L"", x}} P(x))";
      var equality = reverse ? $"{quantified} == b" : $"b == {quantified}";
      var program = $@"
function P(int): bool;
procedure M(b: bool)
{{
  assume (forall {{:pool ""L""}} y: int :: !P(y));
  assume {(negate ? $"!({equality})" : equality)};
  assert false;
}}";
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      options.NormalizeNames = false;
      var log = await GetProverLogs.GetProverLogForProgram(options, program);

      StringAssert.Contains("skolemConstant", log);
      StringAssert.Contains("(not (P skolemConstant0))", log);
      StringAssert.Contains($"({quantifier} ((x", log);
    }

    [Test]
    public async Task BooleanEqualityPreservesInstantiationLabels()
    {
      var program = @"
function P(int): bool;
procedure M(b: bool)
{
  assume b == (forall {:pool ""L""} x: int :: {P(x)} P(x));
  assert {:add_to_pool ""L"", 0} false;
}";
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      options.NormalizeNames = false;
      var log = await GetProverLogs.GetProverLogForProgram(options, program);

      StringAssert.Contains("skolemConstant", log);
      StringAssert.Contains("(P 0)", log);
    }

    [Test]
    public async Task NonBooleanEqualityDoesNotExposeSkolemization()
    {
      var program = @"
function P(int): bool;
procedure M(n: int)
{
  assume (forall {:pool ""L""} y: int :: P(y));
  assume n == (if (exists x: int :: {:add_to_pool ""L"", x} P(x)) then 0 else 1);
  assert false;
}";
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      options.NormalizeNames = false;
      var log = await GetProverLogs.GetProverLogForProgram(options, program);

      StringAssert.DoesNotContain("skolemConstant", log);
    }

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
