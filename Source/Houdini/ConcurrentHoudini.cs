using System;
using System.IO;
using System.Collections.Generic;
using System.Collections.Concurrent;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Text.RegularExpressions;
using System.Linq;
using VC;

namespace Microsoft.Boogie.Houdini
{
  public class ConcurrentHoudini : Houdini
  {
    int id;

    private static ConcurrentDictionary<string, RefutedAnnotation> refutedSharedAnnotations;

    public static ConcurrentDictionary<string, RefutedAnnotation> RefutedSharedAnnotations { get { return refutedSharedAnnotations; } }

    public ConcurrentHoudini(int id, Program program, HoudiniSession.HoudiniStatistics stats, string cexTraceFile = "houdiniCexTrace.bpl") {
      Contract.Assert(id >= 0);

      this.id = id;
      this.program = program;
      this.cexTraceFile = cexTraceFile;

      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Collecting existential constants...");
      this.houdiniConstants = CollectExistentialConstants();

      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Building call graph...");
      this.callGraph = Program.BuildCallGraph(program);
      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Number of implementations = {0}", callGraph.Nodes.Count);

      if (CommandLineOptions.Clo.HoudiniUseCrossDependencies)
      {
        if (CommandLineOptions.Clo.Trace) Console.WriteLine("Computing procedure cross dependencies ...");
        this.crossDependencies = new CrossDependencies(this.houdiniConstants);
        this.crossDependencies.Visit(program);
      }

      Inline();

      this.vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, new List<Checker>());
      this.proverInterface = ProverInterface.CreateProver(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, CommandLineOptions.Clo.ProverKillTime, id);

      vcgenFailures = new HashSet<Implementation>();
      Dictionary<Implementation, HoudiniSession> houdiniSessions = new Dictionary<Implementation, HoudiniSession>();
      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Beginning VC generation for Houdini...");
      foreach (Implementation impl in callGraph.Nodes) {
        try {
          if (CommandLineOptions.Clo.Trace)
            Console.WriteLine("Generating VC for {0}", impl.Name);
          HoudiniSession session = new HoudiniSession(this, vcgen, proverInterface, program, impl, stats, taskID: id);
          houdiniSessions.Add(impl, session);
        }
        catch (VCGenException) {
          if (CommandLineOptions.Clo.Trace)
            Console.WriteLine("VC generation failed");
          vcgenFailures.Add(impl);
        }
      }
      this.houdiniSessions = new ReadOnlyDictionary<Implementation, HoudiniSession>(houdiniSessions);

      if (CommandLineOptions.Clo.ExplainHoudini)
      {
        // Print results of ExplainHoudini to a dotty file
        explainHoudiniDottyFile = new StreamWriter("explainHoudini.dot");
        explainHoudiniDottyFile.WriteLine("digraph explainHoudini {");
        foreach (var constant in houdiniConstants)
          explainHoudiniDottyFile.WriteLine("{0} [ label = \"{0}\" color=black ];", constant.Name);
        explainHoudiniDottyFile.WriteLine("TimeOut [label = \"TimeOut\" color=red ];");
      }
    }

    static ConcurrentHoudini()
    {
      refutedSharedAnnotations = new ConcurrentDictionary<string, RefutedAnnotation>();
    }

    private bool ExchangeRefutedAnnotations()
    {
      int count = 0;

      if (CommandLineOptions.Clo.DebugConcurrentHoudini)
        Console.WriteLine("# number of shared refuted annotations: " + refutedSharedAnnotations.Count);

      foreach (string key in refutedSharedAnnotations.Keys) {
        KeyValuePair<Variable, bool> kv = currentHoudiniState.Assignment.FirstOrDefault(entry => entry.Key.Name.Equals(key) && entry.Value);

        if (kv.Key != null) {
          RefutedAnnotation ra = null;
          Implementation refutationSite = null;

          foreach (var r in program.TopLevelDeclarations.OfType<Implementation>()) {
            if (r.Name.Equals(refutedSharedAnnotations[key].RefutationSite.Name)) {
              refutationSite = r;
              break;
            }
          }
          Debug.Assert(refutationSite != null);

          if (refutedSharedAnnotations[key].Kind == RefutedAnnotationKind.REQUIRES) {
            Procedure proc = null;
            foreach (var p in program.TopLevelDeclarations.OfType<Procedure>()) {
              if (p.Name.Equals(refutedSharedAnnotations[key].CalleeProc.Name)) {
                proc = p;
                break;
              }
            }
            Debug.Assert(proc != null);
            ra = RefutedAnnotation.BuildRefutedRequires(kv.Key, proc, refutationSite);
          } else if (refutedSharedAnnotations[key].Kind == RefutedAnnotationKind.ENSURES)
            ra = RefutedAnnotation.BuildRefutedEnsures(kv.Key, refutationSite);
          else if (refutedSharedAnnotations[key].Kind == RefutedAnnotationKind.ASSERT)
            ra = RefutedAnnotation.BuildRefutedAssert(kv.Key, refutationSite);
          Debug.Assert(ra != null);

          if (CommandLineOptions.Clo.DebugConcurrentHoudini)
            Console.WriteLine("(+) " + ra.Constant + "," + ra.Kind + "," + ra.CalleeProc + "," + ra.RefutationSite);

          AddRelatedToWorkList(ra);
          UpdateAssignment(ra);
          count++;
        }
      }

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
            refutedSharedAnnotations.TryAdd(refutedAnnotation.Constant.Name, refutedAnnotation);
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

      if (initialAssignment != null) {
        foreach (var v in currentHoudiniState.Assignment.Keys.ToList()) {
          currentHoudiniState.Assignment[v] = initialAssignment[v.Name];
        }
      }

      if (refutedSharedAnnotations.Count > 0) {
        foreach (var v in currentHoudiniState.Assignment.Keys.ToList()) {
          if (refutedSharedAnnotations.ContainsKey(v.Name)) {
            currentHoudiniState.Assignment[v] = false;
          }
        }
      }

      foreach (Implementation impl in vcgenFailures) {
        currentHoudiniState.addToBlackList(impl.Name);
      }

      while (currentHoudiniState.WorkQueue.Count > 0) {
        this.NotifyIteration();

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

    protected override ProverInterface.Outcome TryCatchVerify(HoudiniSession session, int stage, IEnumerable<int> completedStages, out List<Counterexample> errors) {
      ProverInterface.Outcome outcome;
      try {
        outcome = session.Verify(proverInterface, GetAssignmentWithStages(stage, completedStages), out errors, taskID: id);
      }
      catch (UnexpectedProverOutputException upo) {
        Contract.Assume(upo != null);
        errors = null;
        outcome = ProverInterface.Outcome.Undetermined;
      }
      return outcome;
    }
  }
}
