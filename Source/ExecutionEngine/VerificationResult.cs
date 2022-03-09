using System;
using System.Collections.Generic;
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
}