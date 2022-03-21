using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using VC;

namespace Microsoft.Boogie;

public sealed class VerificationResult
{
  public readonly string RequestId;
  public readonly string Checksum;
  public readonly string DependeciesChecksum;
  public readonly string ImplementationName;
  public readonly IToken ImplementationToken;
  public readonly string ProgramId;
  public readonly string MessageIfVerifies;

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

  public ISet<byte[]> AssertionChecksums { get; }
  public ErrorInformation ErrorBeforeVerification { get; set; }

  public VerificationResult(string requestId, Implementation implementation, string programId = null)
  {
    Checksum = implementation.Checksum;
    DependeciesChecksum = implementation.DependencyChecksum;
    RequestId = requestId;
    ImplementationName = implementation.Name;
    ImplementationToken = implementation.tok;
    ProgramId = programId;
    AssertionChecksums = implementation.AssertionChecksums;
    MessageIfVerifies = implementation.FindStringAttribute("msg_if_verifies");
  }

  public String GetOutput(OutputPrinter printer,
    ExecutionEngine engine,
    PipelineStatistics stats, ErrorReporterDelegate er,
    Implementation implementation) {
    var result = new StringWriter();
    if (ErrorBeforeVerification != null) {
      printer.WriteErrorInformation(ErrorBeforeVerification, result);
    }

    engine.ProcessOutcome(printer, Outcome, Errors, TimeIndication(engine.Options), stats,
      result, implementation.GetTimeLimit(engine.Options), er, ImplementationName, ImplementationToken,
      RequestId, MessageIfVerifies);

    engine.ProcessErrors(printer, Errors, Outcome, result, er, implementation);

    return result.ToString();
  }

  public void ProcessXml(ExecutionEngine engine) {
    if (engine.Options.XmlSink == null) {
      return;
    }

    lock (engine.Options.XmlSink) {
      engine.Options.XmlSink.WriteStartMethod(ImplementationName, Start);

      foreach (var vcResult in VCResults.OrderBy(s => s.vcNum)) {
        engine.Options.XmlSink.WriteSplit(vcResult.vcNum, vcResult.asserts, vcResult.startTime,
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