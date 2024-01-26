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
using Microsoft.Boogie.SMTLib;

namespace VC
{
  using Bpl = Microsoft.Boogie;
  using System.Threading.Tasks;

  public record VerificationRunResult
  (
    int VcNum,
    int Iteration,
    DateTime StartTime,
    Bpl.SolverOutcome Outcome,
    TimeSpan RunTime,
    int MaxCounterExamples,
    List<Counterexample> CounterExamples,
    List<AssertCmd> Asserts,
    IEnumerable<TrackedNodeComponent> CoveredElements,
    int ResourceCount,
    SolverKind? SolverUsed
  ) {
    public void ComputePerAssertOutcomes(out Dictionary<AssertCmd, Bpl.SolverOutcome> perAssertOutcome,
      out Dictionary<AssertCmd, Counterexample> perAssertCounterExamples) {
      perAssertOutcome = new();
      perAssertCounterExamples = new();
      if (Outcome == Bpl.SolverOutcome.Valid) {
        perAssertOutcome = Asserts.ToDictionary(cmd => cmd, assertCmd => Bpl.SolverOutcome.Valid);
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

          perAssertOutcome.TryAdd(underlyingAssert, Bpl.SolverOutcome.Invalid);
          perAssertCounterExamples.TryAdd(underlyingAssert, counterExample);
        }

        var remainingOutcome =
          Outcome == Bpl.SolverOutcome.Invalid && CounterExamples.Count < MaxCounterExamples
            // We could not extract more counterexamples, remaining assertions are thus valid 
            ? Bpl.SolverOutcome.Valid
            : Outcome == Bpl.SolverOutcome.Invalid
              // We reached the maximum number of counterexamples, we can't infer anything for the remaining assertions
              ? Bpl.SolverOutcome.Undetermined
              // TimeOut, OutOfMemory, OutOfResource, Undetermined for a single split also applies to assertions
              : Outcome;

        foreach (var assert in Asserts) {
          perAssertOutcome.TryAdd(assert, remainingOutcome);
        }
      }
    }
  }
}
