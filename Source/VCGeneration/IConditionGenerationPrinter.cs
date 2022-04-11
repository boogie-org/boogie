using System.Collections.Generic;
using Microsoft.Boogie;

namespace VC;

public interface IConditionGenerationPrinter {
  public void ReportSplitResult(Split split, VCResult splitResult);
}
