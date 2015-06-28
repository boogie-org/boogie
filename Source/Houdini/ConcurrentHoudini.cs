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

    protected int taskID;

    private static ConcurrentDictionary<string, RefutedAnnotation> refutedSharedAnnotations;

    public static ConcurrentDictionary<string, RefutedAnnotation> RefutedSharedAnnotations { get { return refutedSharedAnnotations; } }

    public ConcurrentHoudini(int taskId, Program program, HoudiniSession.HoudiniStatistics stats, string cexTraceFile = "houdiniCexTrace.txt") {
      Contract.Assert(taskId >= 0);
      this.program = program;
      this.cexTraceFile = cexTraceFile;
      this.taskID = taskId;
      Initialize(program, stats);
    }

    static ConcurrentHoudini()
    {
      refutedSharedAnnotations = new ConcurrentDictionary<string, RefutedAnnotation>();
    }

    protected override bool ExchangeRefutedAnnotations()
    {
      int count = 0;

      if (CommandLineOptions.Clo.DebugConcurrentHoudini)
        Console.WriteLine("# number of shared refuted annotations: " + refutedSharedAnnotations.Count);

      foreach (string key in refutedSharedAnnotations.Keys) {
        KeyValuePair<Variable, bool> kv = currentHoudiniState.Assignment.FirstOrDefault(entry => entry.Key.Name.Equals(key) && entry.Value);

        if (kv.Key != null) {
          RefutedAnnotation ra = null;
          Implementation refutationSite = null;

          foreach (var r in program.Implementations) {
            if (r.Name.Equals(refutedSharedAnnotations[key].RefutationSite.Name)) {
              refutationSite = r;
              break;
            }
          }
          Debug.Assert(refutationSite != null);

          if (refutedSharedAnnotations[key].Kind == RefutedAnnotationKind.REQUIRES) {
            Procedure proc = null;
            foreach (var p in program.Procedures) {
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

    protected override void ShareRefutedAnnotation(RefutedAnnotation refutedAnnotation) {
      refutedSharedAnnotations.TryAdd(refutedAnnotation.Constant.Name, refutedAnnotation);
    }

    protected override void ApplyRefutedSharedAnnotations() {
      if (refutedSharedAnnotations.Count > 0) {
        foreach (var v in currentHoudiniState.Assignment.Keys.ToList()) {
          if (refutedSharedAnnotations.ContainsKey(v.Name)) {
            currentHoudiniState.Assignment[v] = false;
          }
        }
      }
    }

    protected override int GetTaskID() {
      return taskID;
    }

  }
}
