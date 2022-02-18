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
  /// successfully proven.
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
  /// </summary>
  public abstract string ShortDescription { get; }
}

public class AssertionDescription : ProofObligationDescription
{
  public override string SuccessDescription => "This assertion holds.";

  public override string FailureDescription => "This assertion might not hold.";

  public override string ShortDescription => "assert";
}

public class PreconditionDescription : ProofObligationDescription
{
  public override string SuccessDescription =>
    "All preconditions hold for call.";

  public override string FailureDescription =>
    "A precondition for this call might not hold.";

  public override string ShortDescription => "precondition";
}

public class RequiresDescription : ProofObligationDescription
{
  public override string SuccessDescription =>
    "This precondition holds.";

  public override string FailureDescription =>
    "This is the precondition that might not hold.";

  public override string ShortDescription => "requires";
}

public class PostconditionDescription : ProofObligationDescription
{
  public override string SuccessDescription =>
    "All postconditions hold for this return path.";

  public override string FailureDescription =>
    "A postcondition might not hold on this return path.";

  public override string ShortDescription => "postcondition";
}

public class EnsuresDescription : ProofObligationDescription
{
  public override string SuccessDescription =>
    "This postcondition holds.";

  public override string FailureDescription =>
    "This is the postcondition that might not hold.";

  public override string ShortDescription => "ensures";
}

public class InvariantEstablishedDescription : AssertionDescription
{
  public override string SuccessDescription =>
    "This loop invariant holds on entry.";

  public override string FailureDescription =>
    "This loop invariant might not hold on entry.";

  public override string ShortDescription => "invariant established";
}

public class InvariantMaintainedDescription : AssertionDescription
{
  public override string SuccessDescription =>
    "This loop invariant is maintained by the loop.";

  public override string FailureDescription =>
    "This loop invariant might not be maintained by the loop.";

  public override string ShortDescription => "invariant maintained";
}
