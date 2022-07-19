using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using Microsoft.Boogie.VCExprAST;
using NUnit.Framework;
using VC;
using VCGeneration;

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

    [Test]
    public async Task SolverCrash()
    {
      var printer = new TestPrinter();
      var options = CommandLineOptions.FromArguments(printer);
      options.CreateSolver = (_, _) => new OverflowSolver();
      var executionEngine = ExecutionEngine.CreateWithoutSharedCache(options);

      var terminatingProgram = GetProgram(executionEngine, fast);

      // We limit the number of checkers to 1.
      options.VcsCores = 1;

      var outcome1 = await executionEngine.GetImplementationTasks(terminatingProgram)[0].TryRun()!.ToTask();
      Assert.IsTrue(outcome1 is Completed completed && completed.Result.Outcome == ConditionGeneration.Outcome.Inconclusive);
      options.CreateSolver = (_ ,_ ) => new UnsatSolver();
      var outcome2 = await executionEngine.GetImplementationTasks(terminatingProgram)[0].TryRun()!.ToTask();
      Assert.IsTrue(outcome2 is Completed completed2 && completed2.Result.Outcome == ConditionGeneration.Outcome.Correct);
    }

    [Test]
    public async Task InferAndVerifyCanBeCancelledWhileWaitingForProver() {
      var printer = new TestPrinter();
      var options = CommandLineOptions.FromArguments(printer);
      var executionEngine = ExecutionEngine.CreateWithoutSharedCache(options);
      
      var terminatingProgram = GetProgram(executionEngine, fast);
      
      // We limit the number of checkers to 1.
      options.VcsCores = 1;

      var requestId = ExecutionEngine.FreshRequestId();
      
      var outcome = await
        executionEngine.InferAndVerify(Console.Out, terminatingProgram, new PipelineStatistics(), requestId, null, requestId);
      Assert.AreEqual(PipelineOutcome.VerificationCompleted, outcome);
      Assert.AreEqual(1, printer.SplitResults.Count);
      Assert.AreEqual(1, printer.Implementations.Count);
      Assert.AreEqual(1, printer.StartedImplementations.Count);
      Assert.AreEqual(1, printer.FinishedImplementations.Count);
      Assert.AreEqual(1, printer.FinishedImplementations[0].Item2.Errors.Count());
      Assert.AreEqual(true, printer.FinishedImplementations[0].Item2.Errors[0] is ReturnCounterexample);
      var vcResult = printer.SplitResults[0].Item2;
      Assert.AreEqual(1, vcResult.asserts.Count);
      var assertion = vcResult.asserts[0];
      vcResult.ComputePerAssertOutcomes(out var perAssertOutcome, out var perAssertCounterExamples);
      Assert.Contains(assertion, perAssertOutcome.Keys);
      Assert.Contains(assertion, perAssertCounterExamples.Keys);
      var outcomeAssertion = perAssertOutcome[assertion];
      var counterExampleAssertion = perAssertCounterExamples[assertion];
      Assert.AreEqual(ProverInterface.Outcome.Invalid, outcomeAssertion);
      Assert.AreEqual(true, counterExampleAssertion is ReturnCounterexample);
      var returnCounterExample = (ReturnCounterexample)counterExampleAssertion;
      Assert.AreEqual(returnCounterExample.FailingAssert, assertion);
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
