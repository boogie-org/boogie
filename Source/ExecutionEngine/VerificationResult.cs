using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using VC;
using VCGeneration;

namespace Microsoft.Boogie;

public sealed class VerificationResult
{
  private readonly Implementation implementation;
  public readonly string ProgramId;
  public string MessageIfVerifies => implementation.FindStringAttribute("msg_if_verifies");
  public string Checksum => implementation.Checksum;
  public string DependenciesChecksum => implementation.DependencyChecksum;

  public ISet<byte[]> AssertionChecksums => implementation.AssertionChecksums;

  public DateTime Start { get; set; }
  public DateTime End { get; set; }

  public int ResourceCount { get; set; }

  public int ProofObligationCount
  {
    get { return ProofObligationCountAfter - ProofObligationCountBefore; }
  }

  public int ProofObligationCountBefore { get; set; }
  public int ProofObligationCountAfter { get; set; }

  public ConditionGeneration.Outcome Outcome { get; set; }
  public List<Counterexample> Errors = new();
  public List<VCResult> VCResults;

  public ErrorInformation ErrorBeforeVerification { get; set; }

  public VerificationResult(Implementation implementation, string programId = null)
  {
    this.implementation = implementation;
    ProgramId = programId;
  }

  public ErrorInformation GetOutcomeError(ExecutionEngineOptions options) {
    return ExecutionEngine.GetOutcomeError(options, Outcome, implementation.Name, implementation.tok, MessageIfVerifies,
      TextWriter.Null, implementation.GetTimeLimit(options), Errors);
  }

  public String GetOutput(OutputPrinter printer,
    ExecutionEngine engine,
    PipelineStatistics stats, ErrorReporterDelegate er) {
    var result = new StringWriter();
    if (ErrorBeforeVerification != null) {
      printer.WriteErrorInformation(ErrorBeforeVerification, result);
    }

    engine.ProcessOutcome(printer, Outcome, Errors, TimeIndication(engine.Options), stats,
      result, implementation.GetTimeLimit(engine.Options), er, implementation.Name, implementation.tok,
      MessageIfVerifies);

    engine.ProcessErrors(printer, Errors, Outcome, result, er, implementation);

    return result.ToString();
  }

  public void ProcessXml(ExecutionEngine engine) {
    if (engine.Options.XmlSink == null) {
      return;
    }

    lock (engine.Options.XmlSink) {
      engine.Options.XmlSink.WriteStartMethod(implementation.Name, Start);

      foreach (var vcResult in VCResults.OrderBy(s => (s.vcNum, s.iteration))) {
        engine.Options.XmlSink.WriteSplit(vcResult.vcNum, vcResult.iteration, vcResult.asserts, vcResult.startTime,
          vcResult.outcome.ToString().ToLowerInvariant(), vcResult.runTime, vcResult.resourceCount);
      }

      engine.Options.XmlSink.WriteEndMethod(Outcome.ToString().ToLowerInvariant(),
        End, End - Start,
        ResourceCount);
    }
  }

  private string TimeIndication(ExecutionEngineOptions options)
  {
    var result = "";
    if (options.Trace)
    {
      result = string.Format("  [{0:F3} s, solver resource count: {1}, {2} proof obligation{3}]  ",
        (End - Start).TotalSeconds,
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