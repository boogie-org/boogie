namespace Microsoft.Boogie;

/// <summary>
/// A multi-faceted description of a proof obligation. This class is intended
/// to provide several forms of human-readable text summarizing the meaning of
/// a proof obligation: one for the case where the proof has succeeded, one
/// for the case where the proof has failed, and one for the case of quickly
/// identifying the type of proof obligation (for inclusion in long lists of
/// proof obligations, for example).
/// </summary>
public abstract class ProofObligationDescription {
  /// <summary>
  /// A description of what this proof obligation means when it has been
  /// successfully proved.
  /// </summary>
  public abstract string SuccessDescription { get; }

  /// <summary>
  /// A description of what this proof obligation means (or might mean)
  /// when the prover has failed to establish its validity.
  /// </summary>
  public virtual string FailureDescription =>
    $"Failed to prove: {SuccessDescription}";

  /// <summary>
  /// A short description of the general type of this proof obligation.
  /// Should be a unique identifier appropriate for programmatic comparison
  /// but also comprehensible to humans.
  /// </summary>
  public abstract string ShortDescription { get; }
}

public class AssertionDescription : ProofObligationDescription
{
  public override string SuccessDescription => "this assertion holds";

  public override string FailureDescription => "this assertion could not be proved";

  public override string ShortDescription => "assert";
}

public class PreconditionDescription : ProofObligationDescription
{
  public override string SuccessDescription =>
    "all preconditions hold for this call";

  public override string FailureDescription =>
    "a precondition for this call could not be proved";

  public override string ShortDescription => "precondition";
}

public class RequiresDescription : ProofObligationDescription
{
  public override string SuccessDescription =>
    "this precondition holds";

  public override string FailureDescription =>
    "this is the precondition that could not be proved";

  public override string ShortDescription => "requires";
}

public class PostconditionDescription : ProofObligationDescription
{
  public override string SuccessDescription =>
    "all postconditions hold for this return path";

  public override string FailureDescription =>
    "a postcondition could not be proved on this return path";

  public override string ShortDescription => "postcondition";
}

public class EnsuresDescription : ProofObligationDescription
{
  public override string SuccessDescription =>
    "this postcondition holds";

  public override string FailureDescription =>
    "this is the postcondition that could not be proved";

  public override string ShortDescription => "ensures";
}

public class InvariantEstablishedDescription : AssertionDescription
{
  public override string SuccessDescription =>
    "this loop invariant holds on entry";

  public override string FailureDescription =>
    "this loop invariant could not be proved on entry";

  public override string ShortDescription => "invariant established";
}

public class InvariantMaintainedDescription : AssertionDescription
{
  public override string SuccessDescription =>
    "this loop invariant is maintained by the loop";

  public override string FailureDescription =>
    "this invariant could not be proved to be maintained by the loop";

  public override string ShortDescription => "invariant maintained";
}

public class FailureOnlyDescription : AssertionDescription
{
  public override string SuccessDescription =>
    $"Error cannot occur: {errorMessage}";

  public override string FailureDescription => errorMessage;

  public override string ShortDescription => "assert";

  private readonly string errorMessage;

  public FailureOnlyDescription(string errorMessage) {
    this.errorMessage = errorMessage;
  }
}
