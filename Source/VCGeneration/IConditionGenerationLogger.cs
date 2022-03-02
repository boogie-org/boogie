using System.Collections.Generic;
using Microsoft.Boogie;

namespace VC;

public interface IConditionGenerationLogger {
  public void ReportAssertionBatchResult(Implementation implementation,
    Dictionary<AssertCmd, ConditionGeneration.Outcome> perAssertOutcome,
    Dictionary<AssertCmd, Counterexample> perAssertCounterExamples);
}