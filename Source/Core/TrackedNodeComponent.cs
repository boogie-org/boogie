using System;

namespace Microsoft.Boogie
{
  /// <summary>
  /// Represents an AST node, or component of a node, that is being
  /// tracked during the proof process to determine whether it was
  /// used as part of a completed proof.
  /// </summary>
  public abstract record TrackedNodeComponent()
  {
    /// <summary>
    /// The string used to represent this component in the solver.
    /// </summary>
    public abstract string SolverLabel { get; }

    /// <summary>
    /// A human-readable description of this component in terms of
    /// user-provided :id attributes.
    /// </summary>
    public abstract string Description { get; }

    /// <summary>
    /// This suffix indicates that an ID string represents the assumption of
    /// a specific ensures clause after a specific call.
    /// </summary>
    protected const string ensuresSuffix = "ensures";

    /// <summary>
    /// This suffix indicates that an ID string represents the goal of
    /// proving a specific requires clause before a specific call.
    /// </summary>
    protected const string requiresSuffix = "requires";

    /// <summary>
    /// This suffix indicates that an ID string represents the assumption
    /// of a specific requires clause after a specific call.
    /// </summary>
    protected const string requiresAssumedSuffix = "requires_assumed";

    /// <summary>
    /// This suffix indicates that an ID string represents the goal of
    /// proving that a specific loop invariant is established.
    /// </summary>
    protected const string establishedSuffix = "established";

    /// <summary>
    /// This suffix indicates that an ID string represents the goal of
    /// proving that a specific loop invariant is maintained.
    /// </summary>
    protected const string maintainedSuffix = "maintained";

    /// <summary>
    /// This suffix indicates that an ID string represents the asssumption
    /// of a specific loop invariant in the body of the loop.
    /// </summary>
    protected const string assumeInBodySuffix = "assume_in_body";

    /// <summary>
    /// Reverse the transformation of TrackedNodeComponent to string
    /// done by the SolverLabel attribute.
    /// </summary>
    public static TrackedNodeComponent ParseSolverString(string idString)
    {
      var parts = idString.Split('$');
      if (parts.Length == 3 && parts[2].Equals(requiresSuffix)) {
        var reqId = parts[0];
        var callId = parts[1];
        return new TrackedCallRequiresGoal(callId, reqId);
      }
      else if (parts.Length == 3 && parts[2].Equals(requiresAssumedSuffix)) {
        var reqId = parts[0];
        var callId = parts[1];
        return new TrackedCallRequiresAssumed(callId, reqId);
      }
      else if (parts.Length == 3 && parts[2].Equals(ensuresSuffix)) {
        var ensId = parts[0];
        var callId = parts[1];
        return new TrackedCallEnsures(callId, ensId);
      }
      else if (parts.Length == 2 && parts[1].Equals(establishedSuffix)) {
        return new TrackedInvariantEstablished(parts[0]);
      }
      else if (parts.Length == 2 && parts[1].Equals(maintainedSuffix)) {
        return new TrackedInvariantMaintained(parts[0]);
      }
      else if (parts.Length == 2 && parts[1].Equals(assumeInBodySuffix)) {
        return new TrackedInvariantAssumed(parts[0]);
      }
      else if (parts.Length > 1) {
        throw new ArgumentException($"Malformed program element ID string: {idString}");
      }
      else {
        return new LabeledNodeComponent(idString);
      }
    }
  }

  public record LabeledNodeComponent(string id) : TrackedNodeComponent()
  {
    public override string SolverLabel => id;
    public override string Description => id;
  }

  public record TrackedCallRequiresGoal(string callId, string requiresId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{requiresId}${callId}${requiresSuffix}";
    public override string Description => $"requires clause {requiresId} proved for call {callId}";
  }

  public record TrackedCallRequiresAssumed(string callId, string requiresId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{requiresId}${callId}${requiresAssumedSuffix}";
    public override string Description => $"requires clause {requiresId} assumed from call {callId}";
  }

  public record TrackedCallEnsures(string callId, string ensuresId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{ensuresId}${callId}${ensuresSuffix}";
    public override string Description => $"ensures clause {ensuresId} from call {callId}";
  }

  public record TrackedInvariantAssumed(string invariantId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{invariantId}${assumeInBodySuffix}";
    public override string Description => $"invariant {invariantId} assumed in body";
  }

  public record TrackedInvariantEstablished(string invariantId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{invariantId}${establishedSuffix}";
    public override string Description => $"invariant {invariantId} established";
  }

  public record TrackedInvariantMaintained(string invariantId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{invariantId}${maintainedSuffix}";
    public override string Description => $"invariant {invariantId} maintained";
  }
}