using System;

namespace Microsoft.Boogie
{
  public abstract record ProgramElement()
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

    public static ProgramElement ParseSolverString(string idString)
    {
      var parts = idString.Split('$');
      if (parts.Length == 3 && parts[2].Equals(requiresSuffix)) {
        var reqId = parts[0];
        var callId = parts[1];
        return new CallRequiresGoalElement(callId, reqId);
      }
      else if (parts.Length == 3 && parts[2].Equals(requiresAssumedSuffix)) {
        var reqId = parts[0];
        var callId = parts[1];
        return new CallRequiresAssumedElement(callId, reqId);
      }
      else if (parts.Length == 3 && parts[2].Equals(ensuresSuffix)) {
        var ensId = parts[0];
        var callId = parts[1];
        return new CallEnsuresElement(callId, ensId);
      }
      else if (parts.Length == 2 && parts[1].Equals(establishedSuffix)) {
        return new InvariantEstablishedElement(parts[0]);
      }
      else if (parts.Length == 2 && parts[1].Equals(maintainedSuffix)) {
        return new InvariantMaintainedElement(parts[0]);
      }
      else if (parts.Length == 2 && parts[1].Equals(assumeInBodySuffix)) {
        return new InvariantAssumedElement(parts[0]);
      }
      else if (parts.Length > 1) {
        throw new ArgumentException($"Malformed program element ID string: {idString}");
      }
      else {
        return new LabeledElement(idString);
      }
    }
  }

  public record LabeledElement(string id) : ProgramElement()
  {
    public override string SolverLabel => id;
  }

  public record CallRequiresGoalElement(string callId, string requiresId) : ProgramElement()
  {
    public override string SolverLabel => $"{requiresId}${callId}${requiresSuffix}";
  }

  public record CallRequiresAssumedElement(string callId, string requiresId) : ProgramElement()
  {
    public override string SolverLabel => $"{requiresId}${callId}${requiresAssumedSuffix}";
  }

  public record CallEnsuresElement(string callId, string ensuresId) : ProgramElement()
  {
    public override string SolverLabel => $"{ensuresId}${callId}${ensuresSuffix}";
  }

  public record InvariantAssumedElement(string invariantId) : ProgramElement()
  {
    public override string SolverLabel => $"{invariantId}${assumeInBodySuffix}";
  }

  public record InvariantEstablishedElement(string invariantId) : ProgramElement()
  {
    public override string SolverLabel => $"{invariantId}${establishedSuffix}";
  }

  public record InvariantMaintainedElement(string invariantId) : ProgramElement()
  {
    public override string SolverLabel => $"{invariantId}${maintainedSuffix}";
  }
}