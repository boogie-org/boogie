using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Threading.Tasks;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie.Houdini
{
  public class StagedHoudini
  {

    private Program program;
    private Func<string, Program> ProgramFromFile;
    private StagedHoudiniPlan plan;
    private List<Houdini>[] houdiniInstances;
    private List<StagedHoudiniTask> tasks = new List<StagedHoudiniTask>();
    private Dictionary<ScheduledStage, HoudiniOutcome> outcomes = new Dictionary<ScheduledStage,HoudiniOutcome>();

    private const string tempFilename = "__stagedHoudiniTemp.bpl";

    public StagedHoudini(Program program, Func<string, Program> ProgramFromFile) {
      this.program = program;
      this.ProgramFromFile = ProgramFromFile;
      this.houdiniInstances = new List<Houdini>[CommandLineOptions.Clo.StagedHoudiniThreads];
      for (int i = 0; i < CommandLineOptions.Clo.StagedHoudiniThreads; i++) {
        houdiniInstances[i] = new List<Houdini>();
      }

      var candidateDependenceAnalyser = new CandidateDependenceAnalyser(program);
      candidateDependenceAnalyser.Analyse();
      this.plan = candidateDependenceAnalyser.ApplyStages();
      if (CommandLineOptions.Clo.Trace)
      {
        candidateDependenceAnalyser.dump();
        EmitProgram("staged.bpl");
      }
    }

    public HoudiniOutcome PerformStagedHoudiniInference()
    {

      EmitProgram(tempFilename);

      #region Prepare the tasks, but do not launch them
      foreach (var s in plan) {
        Debug.Assert(!plan.GetDependences(s).Contains(s));
        tasks.Add(new StagedHoudiniTask(s, new Task(() => {
          ExecuteStage(s);
        }, TaskCreationOptions.LongRunning)));
      }
      #endregion

      #region Launch the tasks, and wait for them to finish
      foreach (var t in tasks) {
        t.parallelTask.Start();
      }
      Task.WaitAll(tasks.Select(Item => Item.parallelTask).ToArray());
      int count = 0;
      foreach(var h in houdiniInstances) {
        if(h.Count() > 0) {
          count++;
          System.Diagnostics.Debug.Assert(h.Count() == 1);
          h[0].Close();
        }
      }
      Console.WriteLine("Used " + count + " houdini instances");
      #endregion

      return UnifyOutcomes();

    }

    private HoudiniOutcome UnifyOutcomes()
    {
      HoudiniOutcome result = new HoudiniOutcome();
      var scheduledStages = outcomes.Keys.ToList();

      result.assignment = new Dictionary<string,bool>();
      foreach(var c in outcomes[scheduledStages[0]].assignment.Keys) {
        result.assignment[c] = outcomes.Select(Item => Item.Value).Select(Item => Item.assignment[c]).All(Item => Item);
      }

      result.implementationOutcomes = new Dictionary<string,VCGenOutcome>();
      foreach(var p in outcomes[scheduledStages[0]].implementationOutcomes.Keys) {
        var unifiedImplementationOutcome = outcomes[scheduledStages[0]].implementationOutcomes[p];
        for(int i = 1; i < scheduledStages.Count(); i++) {
          unifiedImplementationOutcome = ChooseOutcome(unifiedImplementationOutcome,
                                                        outcomes[scheduledStages[i]].implementationOutcomes[p]);
        }
        result.implementationOutcomes[p] = unifiedImplementationOutcome;
      }

      return result;
    }

    private void ExecuteStage(ScheduledStage s)
    {
      Task.WaitAll(tasks.Where(
        Item => plan.GetDependences(s).Contains(Item.stage)).
          Select(Item => Item.parallelTask).ToArray());

      List<Houdini> h = AcquireHoudiniInstance();

      if (h.Count() == 0)
      {
        h.Add(new Houdini(ProgramFromFile(tempFilename), new HoudiniSession.HoudiniStatistics(), "houdiniCexTrace_" + s.GetId() + ".bpl"));
      }

      System.Diagnostics.Debug.Assert(h.Count() == 1);

      Dictionary<string, bool> mergedAssignment = null;

      List<Dictionary<string, bool>> relevantAssignments;
      IEnumerable<int> completedStages;
      lock (outcomes)
      {
        relevantAssignments =
        outcomes.Where(Item => plan.Contains(Item.Key)).
          Select(Item => Item.Value).
            Select(Item => Item.assignment).ToList();
        //outcomes.Values.Select(Item => Item.assignment).ToList();
        completedStages = plan.GetDependences(s).Select(Item => Item.GetId());
        //completedStages = outcomes.Keys.Select(Item => Item.GetId());
      }

      if (relevantAssignments.Count() > 0)
      {
        mergedAssignment = new Dictionary<string, bool>();
        foreach (var v in relevantAssignments[0].Keys)
        {
          mergedAssignment[v] = relevantAssignments.Select(Item => Item[v]).ToList().All(Item => Item);
        }
      }

      HoudiniOutcome outcome = h[0].PerformHoudiniInference(
        s.GetId(),
        completedStages,
        mergedAssignment);

      lock (outcomes)
      {
        outcomes[s] = outcome;
      }

      ReleaseHoudiniInstance(h);

    }

    private static void ReleaseHoudiniInstance(List<Houdini> h)
    {
      Monitor.Exit(h);
    }

    private List<Houdini> AcquireHoudiniInstance()
    {
      List<Houdini> h = null;
      do
      {
        foreach (var houdini in houdiniInstances)
        {
          if (Monitor.TryEnter(houdini))
          {
            h = houdini;
            break;
          }
          else
          {
            Thread.Sleep(20);
          }
        }
      } while (h == null);
      return h;
    }

    private void EmitProgram(string filename)
    {
      using (TokenTextWriter writer = new TokenTextWriter(filename, true))
      {
        int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
        CommandLineOptions.Clo.PrintUnstructured = 2;
        program.Emit(writer);
        CommandLineOptions.Clo.PrintUnstructured = oldPrintUnstructured;
      }
    }

  
    private static VCGenOutcome ChooseOutcome(VCGenOutcome o1, VCGenOutcome o2) {
      var vcOutcome1 = o1.outcome;
      var vcOutcome2 = o2.outcome;

      if(vcOutcome1 == vcOutcome2) {
        return o1;
      }

      // Errors trump everything else
      if(vcOutcome1 == VC.ConditionGeneration.Outcome.Errors) {
        return o1;
      }
      if(vcOutcome2 == VC.ConditionGeneration.Outcome.Errors) {
        return o2;
      }

      // If one outcome is Correct, return the other in case it is "worse"
      if(vcOutcome1 == VC.ConditionGeneration.Outcome.Correct) {
        return o2;
      }
      if(vcOutcome2 == VC.ConditionGeneration.Outcome.Correct) {
        return o1;
      }

      // Neither outcome is correct, so if one outcome is ReachedBound, return the other in case it is "worse"
      if(vcOutcome1 == VC.ConditionGeneration.Outcome.ReachedBound) {
        return o2;
      }
      if(vcOutcome2 == VC.ConditionGeneration.Outcome.ReachedBound) {
        return o1;
      }

      // Both outcomes must be timeout or memout; arbitrarily choose the first
      return o1;
    }

    internal class StagedHoudiniTask {
      internal ScheduledStage stage;
      internal Task parallelTask;
      internal StagedHoudiniTask(ScheduledStage stage, Task parallelTask) {
        this.stage = stage;
        this.parallelTask = parallelTask;
      }
    }
  
  }

  public class StagedHoudiniPlan : IEnumerable<ScheduledStage> {

    private Graph<ScheduledStage> ScheduledStages;
    private Dictionary<string, ScheduledStage> CandidateToStage;

    internal StagedHoudiniPlan(Graph<ScheduledStage> ScheduledStages) {
      this.ScheduledStages = ScheduledStages;
      this.CandidateToStage = new Dictionary<string, ScheduledStage>();
      foreach(var s in this) {
        Debug.Assert(!GetDependences(s).Contains(s));
      }
    }

    public IEnumerable<ScheduledStage> GetDependences(ScheduledStage s) {
      IEnumerable<ScheduledStage> result;
      lock(ScheduledStages) {
        result = ScheduledStages.Successors(s);
      }
      return result;
    }


    private static int CompareStages(ScheduledStage s1, ScheduledStage s2) {
      if(s1.GetId() < s2.GetId()) {
        return -1;
      }
      if(s2.GetId() < s1.GetId()) {
        return 1;
      }
      return 0;
    }

    public IEnumerator<ScheduledStage> GetEnumerator() {
      List<ScheduledStage> sortedStages = ScheduledStages.Nodes.ToList();
      sortedStages.Sort(CompareStages);
      return sortedStages.GetEnumerator();
    }

    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
    {
        return this.GetEnumerator();
    }

    internal ScheduledStage StageForCandidate(string c) {
      if(CandidateToStage.ContainsKey(c)) {
        return CandidateToStage[c];
      }
      foreach(var s in ScheduledStages.Nodes) {
        if(s.ContainsCandidate(c)) {
          CandidateToStage[c] = s;
          return s;
        }
      }
      return null;
    }

    public override string ToString()
    {
      string result = "";
      foreach(ScheduledStage s in this) {
        result += "Stage " + s;
        
        result += " depends on stages: ";
        foreach(var id in GetDependences(s).Select(Item => Item.GetId())) {
          result += id + " ";
        }
        result += "\n";
      }
      return result;
    }
  }

  public class ScheduledStage {
    private int Id;
    private HashSet<string> Candidates;

    public ScheduledStage(int Id, HashSet<string> Candidates) {
      this.Id = Id;
      this.Candidates = Candidates;
    }

    internal void AddCandidate(string c) {
      Candidates.Add(c);
    }

    internal bool ContainsCandidate(string c) {
      return Candidates.Contains(c);
    }

    public int GetId() {
      return Id;
    }

    public int Count() {
      return Candidates.Count();
    }

    public override string ToString()
    {
      string result = "ID: " + Id + "{ ";
      foreach(var c in Candidates) {
        result += c + " ";
      }
      result += "}\n";
      return result;
    }
  }


}
