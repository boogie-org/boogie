using System.Collections.Generic;
using Microsoft.Boogie;

namespace VC;

public interface IConditionGenerationLogger {
  public void ReportVerificationStarts(List<IToken> splitTok, IToken implementationTok);

  public void ReportVerificationCompleted(List<IToken> splitTok, IToken implementationTok,
    ConditionGeneration.Outcome outcome, int totalResourceCount);
}