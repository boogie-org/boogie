using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using Microsoft.Boogie.VCExprAST;
using NUnit.Framework;
using VC;

namespace ExecutionEngineTests
{
  [TestFixture]
  public class OutputPrinterTest
  {
    public Program GetProgram(ExecutionEngine engine, string code) {
      var bplFileName = "1";
      int errorCount = Parser.Parse(code, bplFileName, out Program program,
        engine.Options.UseBaseNameForFileName);
      Assert.AreEqual(0, errorCount);

      engine.ResolveAndTypecheck(program, bplFileName, out _);
      engine.EliminateDeadVariables(program);
      engine.CollectModSets(program);
      engine.CoalesceBlocks(program);
      engine.Inline(program);
      return program;
    }

    [Test]
    public async Task NoNullPointerExceptionEvenIfConcurrencyRaces() {
      SMTLibOptions smtLibOptions = CommandLineOptions.FromArguments();
      VCExpressionGenerator vgen = new VCExpressionGenerator();
      VCGenerationOptions genOptions = new VCGenerationOptions(new List<string>(){});
      var smtLibProverOptions = new SMTLibProverOptions(smtLibOptions);
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
    
    [Test]
    public async Task InferAndVerifyCanBeCancelledWhileWaitingForProver() {
      var printer = new TestPrinter();
      var options = new CommandLineOptions(printer);
      using var executionEngine = ExecutionEngine.CreateWithoutSharedCache(options);
      var terminatingProgram = GetProgram(executionEngine, fast);
      
      // We limit the number of checkers to 1.
      options.VcsCores = 1;

      var requestId = ExecutionEngine.FreshRequestId();
      
      var outcome =
        executionEngine.InferAndVerify(terminatingProgram, new PipelineStatistics(), requestId, null, requestId);
      Assert.AreEqual(outcome, PipelineOutcome.VerificationCompleted);
      Assert.AreEqual(1, printer.SplitResults.Count);
      Assert.AreEqual(1, printer.Implementations.Count);
      Assert.AreEqual(1, printer.StartedImplementations.Count);
      Assert.AreEqual(1, printer.FinishedImplementations.Count);
      Assert.AreEqual(1, printer.FinishedImplementations[0].Item2.Errors.Count());
      Assert.AreEqual(true, printer.FinishedImplementations[0].Item2.Errors[0] is ReturnCounterexample);
    }

    private string fast = @"
procedure easy() ensures 1 + 1 == 0; {
}
";
  }

  public class TestPrinter : OutputPrinter {
    public List<Tuple<Split, VCResult>> SplitResults = new();
    public List<Implementation> Implementations = new();
    public List<Implementation> StartedImplementations = new();
    public List<Tuple<Implementation, VerificationResult>> FinishedImplementations = new();
    public void ReportSplitResult(Split split, VCResult splitResult) {
      SplitResults.Add(new Tuple<Split, VCResult>(split, splitResult));
    }

    public ExecutionEngineOptions Options { get; set; }

    public void ErrorWriteLine(TextWriter tw, string s) {
      //
    }

    public void ErrorWriteLine(TextWriter tw, string format, params object[] args) {
      //
    }

    public void AdvisoryWriteLine(TextWriter output, string format, params object[] args) {
      //
    }

    public void AdvisoryWriteLine(string format, params object[] args) {
      //
    }

    public void Inform(string s, TextWriter tw) {
      //
    }

    public void WriteTrailer(TextWriter textWriter, PipelineStatistics stats) {
      throw new NotImplementedException();
    }

    public void WriteTrailer(PipelineStatistics stats) {
      //
    }

    public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true) {
      //
    }

    public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null) {
      //
    }

    public void ReportImplementationsBeforeVerification(Implementation[] implementations) {
      Implementations = implementations.ToList();
    }

    public void ReportStartVerifyImplementation(Implementation implementation) {
      StartedImplementations.Add(implementation);
    }

    public void ReportEndVerifyImplementation(Implementation implementation, VerificationResult result) {
      FinishedImplementations.Add(new Tuple<Implementation, VerificationResult>(implementation, result));
    }
  }
}
