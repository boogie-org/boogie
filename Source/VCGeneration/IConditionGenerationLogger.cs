using System.Collections.Generic;
using Microsoft.Boogie;

namespace VC;

public interface IConditionGenerationLogger {
  public void ReportSplitResult(Split split,
    VCResult splitResult);
}
