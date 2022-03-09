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
  public List<Counterexample> Errors;
  public List<VCResult> VCResults;

  public ISet<byte[]> AssertionChecksums { get; private set; }

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

  public void Emit(ExecutionEngine engine, PipelineStatistics stats, ErrorReporterDelegate er, int index,
    OutputCollector outputCollector, StringWriter output, Implementation impl, bool wasCached)
  {
    engine.ProcessOutcome(Outcome, Errors, engine.TimeIndication(this), stats,
      output, impl.GetTimeLimit(engine.Options), er, ImplementationName,
      ImplementationToken,
      RequestId, MessageIfVerifies, wasCached);

    engine.ProcessErrors(Errors, Outcome, output, er, impl);

    if (engine.Options.XmlSink != null) {
      lock (engine.Options.XmlSink) {
        engine.Options.XmlSink.WriteStartMethod(impl.Name, Start);

        foreach (var vcResult in VCResults.OrderBy(s => s.vcNum)) {
          engine.Options.XmlSink.WriteSplit(vcResult.vcNum, vcResult.asserts, vcResult.startTime,
            vcResult.outcome.ToString().ToLowerInvariant(), vcResult.runTime, vcResult.resourceCount);
        }

        engine.Options.XmlSink.WriteEndMethod(Outcome.ToString().ToLowerInvariant(),
          End, End - Start,
          ResourceCount);
      }
    }

    outputCollector.Add(index, output);

    outputCollector.WriteMoreOutput();

    if (Outcome == VCGen.Outcome.Errors || engine.Options.Trace) {
      Console.Out.Flush();
    }
  }
}