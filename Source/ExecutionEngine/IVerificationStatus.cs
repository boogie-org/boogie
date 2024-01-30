#nullable enable
using VC;

namespace Microsoft.Boogie;

public interface IVerificationStatus {}

/// <summary>
/// Results are available
/// </summary>
public record Completed(VerificationRunResult Result) : IVerificationStatus;

/// <summary>
/// Scheduled to be run but waiting for resources
/// </summary>
public record Queued : IVerificationStatus;

/// <summary>
/// Not scheduled to be run
/// </summary>
public record Stale : IVerificationStatus;

/// <summary>
/// Currently being run
/// </summary>
public record Running : IVerificationStatus;