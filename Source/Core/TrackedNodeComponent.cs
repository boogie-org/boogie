using System;

namespace Microsoft.Boogie
{
  // Represents an AST node, or component of a node, that is being
  // tracked during the proof process to determine whether it was
  // used as part of a completed proof.
  public abstract record TrackedNodeComponent()
  {
    public abstract string SolverLabel { get; }

    // This suffix indicates that an ID string represents the assumption of
    // a specific ensures clause after a specific call.
    protected const string ensuresSuffix = "ensures";

    // This suffix indicates that an ID string represents the goal of
    // proving a specific requires clause before a specific call.
    protected const string requiresSuffix = "requires";

    // This suffix indicates that an ID string represents the assumption
    // of a specific requires clause after a specific call.
    protected const string requiresAssumedSuffix = "requires_assumed";

    // This suffix indicates that an ID string represents the goal of
    // proving that a specific loop invariant is established.
    protected const string establishedSuffix = "established";

    // This suffix indicates that an ID string represents the goal of
    // proving that a specific loop invariant is maintained.
    protected const string maintainedSuffix = "maintained";

    // This suffix indicates that an ID string represents the asssumption
    // of a specific loop invariant in the body of the loop.
    protected const string assumeInBodySuffix = "assume_in_body";

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
  }

  public record TrackedCallRequiresGoal(string callId, string requiresId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{requiresId}${callId}${requiresSuffix}";
  }

  public record TrackedCallRequiresAssumed(string callId, string requiresId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{requiresId}${callId}${requiresAssumedSuffix}";
  }

  public record TrackedCallEnsures(string callId, string ensuresId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{ensuresId}${callId}${ensuresSuffix}";
  }

  public record TrackedInvariantAssumed(string invariantId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{invariantId}${assumeInBodySuffix}";
  }

  public record TrackedInvariantEstablished(string invariantId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{invariantId}${establishedSuffix}";
  }

  public record TrackedInvariantMaintained(string invariantId) : TrackedNodeComponent()
  {
    public override string SolverLabel => $"{invariantId}${maintainedSuffix}";
  }
}