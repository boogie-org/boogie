using System.Collections.Generic;
using Microsoft.Boogie;

namespace VC;

public interface IConditionGenerationLogger {
  public void ReportSplitResult(Split split,
    Dictionary<AssertCmd, ConditionGeneration.Outcome> perAssertOutcome,
    Dictionary<AssertCmd, Counterexample> perAssertCounterExamples);
}
