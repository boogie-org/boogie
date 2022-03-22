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
          // Only deal with the ocunter-examples that cover the asserts of this split.
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

          if (!asserts.Contains(underlyingAssert)) {
            continue;
          }

          perAssertOutcome.Add(underlyingAssert, ProverInterface.Outcome.Invalid);
          perAssertCounterExamples.Add(underlyingAssert, counterExample);
        }

        var remainingOutcome =
          outcome == ProverInterface.Outcome.Invalid && counterExamples.Count < maxCounterExamples
            ? ProverInterface.Outcome.Valid
            : outcome;
        // Everything not listed is successful if no counter-example covers it and we did not reach the limit of counter-examples
        foreach (var assert in asserts) {
          perAssertOutcome.TryAdd(assert, remainingOutcome);
        }
      }
    }
  }
}
