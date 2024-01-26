using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using VC;
using VCGeneration;

namespace Microsoft.Boogie;

public sealed class ImplementationRunResult
{
  private readonly Implementation implementation;
  public readonly string ProgramId;
  public string MessageIfVerifies => (implementation as ICarriesAttributes).FindStringAttribute("msg_if_verifies");
  public string Checksum => implementation.Checksum;
  public string DependenciesChecksum => implementation.DependencyChecksum;

  public ISet<byte[]> AssertionChecksums => implementation.AssertionChecksums;

  public DateTime Start { get; set; }
  public DateTime End { get; set; }

  /// <summary>
  /// Gets or sets the elapsed time, excluding SMT solver setup costs.
  /// (This is narrower than <c>Start - End</c>.)
  /// <c>Start</c> and <c>End</c> are kept because we need them in XML reports.
  /// </summary>
  public TimeSpan Elapsed { get; set; }

  public int ResourceCount { get; set; }

  public int ProofObligationCount
  {
    get { return ProofObligationCountAfter - ProofObligationCountBefore; }
  }

  public int ProofObligationCountBefore { get; set; }
  public int ProofObligationCountAfter { get; set; }

  public VcOutcome VcOutcome { get; set; }
  public List<Counterexample> Errors = new();
  public List<VerificationRunResult> VCResults;

  public ErrorInformation ErrorBeforeVerification { get; set; }

  public ImplementationRunResult(Implementation implementation, string programId = null)
  {
    this.implementation = implementation;
    ProgramId = programId;
  }

  public ErrorInformation GetOutcomeError(ExecutionEngineOptions options) {
    return ExecutionEngine.GetOutcomeError(options, VcOutcome, implementation.VerboseName, implementation.tok, MessageIfVerifies,
      TextWriter.Null, implementation.GetTimeLimit(options), Errors);
  }

  public String GetOutput(OutputPrinter printer,
    ExecutionEngine engine,
    PipelineStatistics stats, ErrorReporterDelegate er) {
    var result = new StringWriter();
    if (ErrorBeforeVerification != null) {
      printer.WriteErrorInformation(ErrorBeforeVerification, result);
    }

    engine.ProcessOutcome(printer, VcOutcome, Errors, TimeIndication(engine.Options), stats,
      result, implementation.GetTimeLimit(engine.Options), er, implementation.VerboseName, implementation.tok,
      MessageIfVerifies);

    engine.ProcessErrors(printer, Errors, VcOutcome, result, er, implementation);

    return result.ToString();
  }

  public void ProcessXml(ExecutionEngine engine) {
    if (engine.Options.XmlSink == null) {
      return;
    }

    lock (engine.Options.XmlSink) {
      engine.Options.XmlSink.WriteStartMethod(implementation.VerboseName, Start);

      foreach (var vcResult in VCResults.OrderBy(s => (vcNum: s.VcNum, iteration: s.Iteration))) {
        engine.Options.XmlSink.WriteSplit(vcResult.VcNum, vcResult.Iteration, vcResult.Asserts, vcResult.StartTime,
          vcResult.Outcome.ToString().ToLowerInvariant(), vcResult.RunTime, vcResult.ResourceCount);
      }

      engine.Options.XmlSink.WriteEndMethod(VcOutcome.ToString().ToLowerInvariant(),
        End, Elapsed,
        ResourceCount);
    }
  }

  private string TimeIndication(ExecutionEngineOptions options)
  {
    var result = "";
    if (options.Trace)
    {
      result = string.Format("  [{0:F3} s, solver resource count: {1}, {2} proof obligation{3}]  ",
        Elapsed.TotalSeconds,
        ResourceCount,
        ProofObligationCount,
        ProofObligationCount == 1 ? "" : "s");
    }
    else if (options.TraceProofObligations)
    {
      result = string.Format("  [{0} proof obligation{1}]  ", ProofObligationCount,
        ProofObligationCount == 1 ? "" : "s");
    }

    return result;
  }
}
