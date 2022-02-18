using Microsoft.Boogie;

namespace VC;

public interface IConditionGenerationLogger {
  public void ReportVerificationStarts(IToken splitTok, IToken implementationTok);

  public void ReportVerificationCompleted(IToken splitTok, IToken implementationTok,
    ConditionGeneration.Outcome outcome, int totalResourceCount);
}