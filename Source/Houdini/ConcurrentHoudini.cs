using System;
using System.IO;
using System.Collections.Generic;
using System.Collections.Concurrent;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Text.RegularExpressions;
using System.Linq;

namespace Microsoft.Boogie.Houdini
{
  public class ConcurrentHoudini : Houdini
  {
    int id;

//    private static ConcurrentDictionary<RefutedAnnotation, int> refutedSharedAnnotations;
    private static ConcurrentDictionary<string, RefutedAnnotation> refutedSharedAnnotations;

    public ConcurrentHoudini(int id, Program program, HoudiniSession.HoudiniStatistics stats, string cexTraceFile = "houdiniCexTrace.bpl")
      : base(program, stats, cexTraceFile)
    {
      this.id = id;
    }

    static ConcurrentHoudini()
    {
      refutedSharedAnnotations = new ConcurrentDictionary<string, RefutedAnnotation>();
    }

    public ConcurrentDictionary<string, RefutedAnnotation> RefutedSharedAnnotations { get { return refutedSharedAnnotations; } }   

    private bool ExchangeRefutedAnnotations()
    {
      int count = 0;

      foreach (string key in refutedSharedAnnotations.Keys) {
        KeyValuePair<Variable, bool> kv = currentHoudiniState.Assignment.FirstOrDefault(entry => entry.Key.Name.Equals(key) && entry.Value);
        RefutedAnnotation ra = refutedSharedAnnotations[key];

        if (kv.Key != null) {
          if (CommandLineOptions.Clo.DebugParallelHoudini)
            Console.WriteLine("(+) " + ra.Constant + "," + ra.Kind + "," + ra.CalleeProc + "," + ra.RefutationSite);

          AddRelatedToWorkList(ra);
          UpdateAssignment(ra);
          count++;
        }
      }

      if (CommandLineOptions.Clo.DebugParallelHoudini)
        Console.WriteLine("# refuted annotations received from the shared exchanging set: " + count);

      return count > 0 ? true : false;
    }

    protected override bool UpdateAssignmentWorkList(ProverInterface.Outcome outcome,
                                                     List<Counterexample> errors)
    {
      Contract.Assume(currentHoudiniState.Implementation != null);
      bool dequeue = true;

      switch (outcome) {
        case ProverInterface.Outcome.Valid:
        //yeah, dequeue
        break;

        case ProverInterface.Outcome.Invalid:
        Contract.Assume(errors != null);

        foreach (Counterexample error in errors) {
          RefutedAnnotation refutedAnnotation = ExtractRefutedAnnotation(error);
          // some candidate annotation removed
          if (refutedAnnotation != null) {
            if (CommandLineOptions.Clo.HoudiniShareRefutedCandidates)
              refutedSharedAnnotations.TryAdd (refutedAnnotation.Constant.Name, refutedAnnotation);
            AddRelatedToWorkList(refutedAnnotation);
            UpdateAssignment(refutedAnnotation);
            dequeue = false;

            #region Extra debugging output
            if (CommandLineOptions.Clo.Trace) {
              using (var cexWriter = new System.IO.StreamWriter(cexTraceFile, true)) {
                cexWriter.WriteLine("Counter example for " + refutedAnnotation.Constant);
                cexWriter.Write(error.ToString());
                cexWriter.WriteLine();
                using (var writer = new Microsoft.Boogie.TokenTextWriter(cexWriter))
                  foreach (Microsoft.Boogie.Block blk in error.Trace)
                    blk.Emit(writer, 15);
                //cexWriter.WriteLine(); 
              }
            }
            #endregion
          }
        }

        if (CommandLineOptions.Clo.DebugParallelHoudini)
          Console.WriteLine("# exchange set size: " + refutedSharedAnnotations.Count);

        if (CommandLineOptions.Clo.HoudiniShareRefutedCandidates)
          if (ExchangeRefutedAnnotations()) dequeue = false;

        break;
        default:
        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine("Timeout/Spaceout while verifying " + currentHoudiniState.Implementation.Name);
        }

        HoudiniSession houdiniSession;
        houdiniSessions.TryGetValue(currentHoudiniState.Implementation, out houdiniSession);

        foreach (Variable v in houdiniSession.houdiniAssertConstants) {
          if (CommandLineOptions.Clo.Trace) {
            Console.WriteLine("Removing " + v);
          }
          currentHoudiniState.Assignment.Remove(v);
          currentHoudiniState.Assignment.Add(v, false);
          this.NotifyConstant(v.Name);
        }

        currentHoudiniState.addToBlackList(currentHoudiniState.Implementation.Name);
        break;
      }

      return dequeue;
    }

    public override HoudiniOutcome PerformHoudiniInference(int stage = 0, 
                                                           IEnumerable<int> completedStages = null,
                                                           Dictionary<string, bool> initialAssignment = null)
    {
      this.NotifyStart(program, houdiniConstants.Count);

      currentHoudiniState = new HoudiniState(BuildWorkList(program), BuildAssignment(houdiniConstants));

      if(initialAssignment != null) {
        foreach(var v in currentHoudiniState.Assignment.Keys.ToList()) {
          currentHoudiniState.Assignment[v] = initialAssignment[v.Name];
        }
      }

      foreach (Implementation impl in vcgenFailures) {
        currentHoudiniState.addToBlackList(impl.Name);
      }

      while (currentHoudiniState.WorkQueue.Count > 0) {
        this.NotifyIteration();

        if (CommandLineOptions.Clo.HoudiniShareRefutedCandidates)
          ExchangeRefutedAnnotations();

        currentHoudiniState.Implementation = currentHoudiniState.WorkQueue.Peek();
        this.NotifyImplementation(currentHoudiniState.Implementation);

        HoudiniSession session;
        this.houdiniSessions.TryGetValue(currentHoudiniState.Implementation, out session);
        HoudiniVerifyCurrent(session, stage, completedStages);
      }

      this.NotifyEnd(true);
      Dictionary<string, bool> assignment = new Dictionary<string, bool>();
      foreach (var x in currentHoudiniState.Assignment)
        assignment[x.Key.Name] = x.Value;
      currentHoudiniState.Outcome.assignment = assignment;
      return currentHoudiniState.Outcome;
    }

    protected override void HoudiniVerifyCurrent(HoudiniSession session, int stage, IEnumerable<int> completedStages)
    {
      while (true) {
        this.NotifyAssignment(currentHoudiniState.Assignment);

        //check the VC with the current assignment
        List<Counterexample> errors;
        ProverInterface.Outcome outcome = TryCatchVerify(session, stage, completedStages, out errors);
        this.NotifyOutcome(outcome);
        Console.WriteLine("***ERROR with id {0} --- {1}***", id, errors.Count);
        DebugRefutedCandidates(currentHoudiniState.Implementation, errors);

        #region Explain Houdini
        if (CommandLineOptions.Clo.ExplainHoudini && outcome == ProverInterface.Outcome.Invalid)
        {
          Contract.Assume(errors != null);
          // make a copy of this variable
          errors = new List<Counterexample>(errors);
          var refutedAnnotations = new List<RefutedAnnotation>();
          foreach (Counterexample error in errors)
          {
            RefutedAnnotation refutedAnnotation = ExtractRefutedAnnotation(error);
            if (refutedAnnotation == null || refutedAnnotation.Kind == RefutedAnnotationKind.ASSERT) continue;
            refutedAnnotations.Add(refutedAnnotation);
          }
          foreach (var refutedAnnotation in refutedAnnotations)
          {
            session.Explain(proverInterface, currentHoudiniState.Assignment, refutedAnnotation.Constant);
          }
        }
        #endregion

        if (UpdateHoudiniOutcome(currentHoudiniState.Outcome, currentHoudiniState.Implementation, outcome, errors)) { // abort
          currentHoudiniState.WorkQueue.Dequeue();
          this.NotifyDequeue();
          FlushWorkList(stage, completedStages);
          return;
        }
        else if (UpdateAssignmentWorkList(outcome, errors)) {
          if (CommandLineOptions.Clo.UseUnsatCoreForContractInfer && outcome == ProverInterface.Outcome.Valid)
            session.UpdateUnsatCore(proverInterface, currentHoudiniState.Assignment);
          currentHoudiniState.WorkQueue.Dequeue();
          this.NotifyDequeue();
          return;
        }
      } 
    }
  }
}
