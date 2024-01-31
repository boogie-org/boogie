#nullable enable
using System;
using System.Diagnostics;
using VC;

namespace Microsoft.Boogie;

public interface IVerificationTask {
  IVerificationStatus CacheStatus { get; }

  ProcessedProgram ProcessedProgram { get; }
  ManualSplit Split { get; }

  /// <summary>
  /// Associated with the verification scope this task occurs in. Multiple tasks can occur in the same scope
  /// Boogie's terms for a verification scope is an Implementation
  /// </summary>
  IToken ScopeToken { get; }

  /// <summary>
  /// Token that identifies where this task originates from
  /// </summary>
  IToken Token { get; }

  /// <summary>
  /// If not running, start running.
  /// If already running and not cancelled, return null.
  /// If already running but being cancelled, queue a new run and return its observable.
  /// If already running but being cancelled, and a new run is queued, return null.
  /// </summary>
  IObservable<IVerificationStatus>? TryRun();
  bool IsIdle { get; }
  void Cancel();
}