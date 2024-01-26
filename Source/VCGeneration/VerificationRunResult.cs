using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;

namespace VC
{
  public record VerificationRunResult
  (
    int vcNum,
    int Iteration,
    DateTime StartTime,
    Outcome Outcome,
    TimeSpan RunTime,
    int MaxCounterExamples,
    List<Counterexample> CounterExamples,
    List<AssertCmd> Asserts,
    IEnumerable<TrackedNodeComponent> CoveredElements,
    int ResourceCount,
    SolverKind? SolverUsed
  ) {
    public void ComputePerAssertOutcomes(out Dictionary<AssertCmd, Outcome> perAssertOutcome,
      out Dictionary<AssertCmd, Counterexample> perAssertCounterExamples) {
      perAssertOutcome = new();
      perAssertCounterExamples = new();
      if (Outcome == Outcome.Valid) {
        perAssertOutcome = Asserts.ToDictionary(cmd => cmd, _ => Outcome.Valid);
      } else {
        foreach (var counterExample in CounterExamples) {
          AssertCmd underlyingAssert;
          if (counterExample is AssertCounterexample assertCounterexample) {
            underlyingAssert = assertCounterexample.FailingAssert;
          } else if (counterExample is CallCounterexample callCounterexample) {
            underlyingAssert = callCounterexample.FailingAssert;
          } else if (counterExample is ReturnCounterexample returnCounterexample) {
            underlyingAssert = returnCounterexample.FailingAssert;
          } else {
            continue;
          }

          // We ensure that the underlyingAssert is among the original asserts
          if (!Asserts.Contains(underlyingAssert)) {
            continue;
          }

          perAssertOutcome.TryAdd(underlyingAssert, Outcome.Invalid);
          perAssertCounterExamples.TryAdd(underlyingAssert, counterExample);
        }

        var remainingOutcome =
          Outcome == Outcome.Invalid && CounterExamples.Count < MaxCounterExamples
            // We could not extract more counterexamples, remaining assertions are thus valid 
            ? Outcome.Valid
            : Outcome == Outcome.Invalid
              // We reached the maximum number of counterexamples, we can't infer anything for the remaining assertions
              ? Outcome.Undetermined
              // TimeOut, OutOfMemory, OutOfResource, Undetermined for a single split also applies to assertions
              : Outcome;

        foreach (var assert in Asserts) {
          perAssertOutcome.TryAdd(assert, remainingOutcome);
        }
      }
    }
  }
}
