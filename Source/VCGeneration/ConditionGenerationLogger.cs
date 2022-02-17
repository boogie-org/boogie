using Microsoft.Boogie;

namespace VC;
public abstract class ConditionGenerationLogger {
  public virtual void VerificationStarts(IToken splitTok, IToken implementationTok) {
    // Nothing to do by default
  }

  public virtual void VerificationCompleted(IToken splitTok, IToken implementationTok,
    ConditionGeneration.Outcome outcome, int totalResourceCount) {
    // Nothing to do by default
  }
}