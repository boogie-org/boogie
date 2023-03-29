using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.IO;
using Microsoft.BaseTypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{
  using Bpl = Microsoft.Boogie;
  using System.Threading.Tasks;

  public record VCResult
  (
    int vcNum,
    int iteration,
    DateTime startTime,
    ProverInterface.Outcome outcome,
    TimeSpan runTime,
    int maxCounterExamples,
    List<Counterexample> counterExamples,
    List<AssertCmd> asserts,
    int resourceCount
  ) {
    public void ComputePerAssertOutcomes(out Dictionary<AssertCmd, ProverInterface.Outcome> perAssertOutcome,
      out Dictionary<AssertCmd, Counterexample> perAssertCounterExamples) {
      perAssertOutcome = new();
      perAssertCounterExamples = new();
      if (outcome == ProverInterface.Outcome.Valid) {
        perAssertOutcome = asserts.ToDictionary(cmd => cmd, assertCmd => ProverInterface.Outcome.Valid);
      } else {
        foreach (var counterExample in counterExamples) {
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
          if (!asserts.Contains(underlyingAssert)) {
            continue;
          }

          perAssertOutcome.TryAdd(underlyingAssert, ProverInterface.Outcome.Invalid);
          perAssertCounterExamples.TryAdd(underlyingAssert, counterExample);
        }

        var remainingOutcome =
          outcome == ProverInterface.Outcome.Invalid && counterExamples.Count < maxCounterExamples
            // We could not extract more counterexamples, remaining assertions are thus valid 
            ? ProverInterface.Outcome.Valid
            : outcome == ProverInterface.Outcome.Invalid
              // We reached the maximum number of counterexamples, we can't infer anything for the remaining assertions
              ? ProverInterface.Outcome.Undetermined
              // TimeOut, OutOfMemory, OutOfResource, Undetermined for a single split also applies to assertions
              : outcome;

        foreach (var assert in asserts) {
          perAssertOutcome.TryAdd(assert, remainingOutcome);
        }
      }
    }
  }
}
