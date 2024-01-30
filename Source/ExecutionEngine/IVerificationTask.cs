#nullable enable
using System;
using VC;

namespace Microsoft.Boogie;

public interface IVerificationTask {
  IVerificationStatus CacheStatus { get; }

  ProcessedProgram ProcessedProgram { get; }
  ManualSplit Split { get; }

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