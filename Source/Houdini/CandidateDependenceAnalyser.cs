using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Basetypes;
using System.Diagnostics;

namespace Microsoft.Boogie.Houdini {

  public class CandidateDependenceAnalyser {

    private const string COARSE_STAGES = "COARSE";
    private const string FINE_STAGES = "FINE";
    private const string BALANCED_STAGES = "BALANCED";

    private Program prog;
    private IVariableDependenceAnalyser varDepAnalyser;
    private IEnumerable<string> candidates;
    private Dictionary<string, HashSet<VariableDescriptor>> candidateDependsOn;
    private Dictionary<VariableDescriptor, HashSet<string>> variableDirectlyReferredToByCandidates;
    private Graph<string> CandidateDependences;
    private StronglyConnectedComponents<string> SCCs;
    private Graph<SCC<string>> StagesDAG;
    private StagedHoudiniPlan Plan;

    public CandidateDependenceAnalyser(Program prog) {
      this.prog = prog;
      this.varDepAnalyser = new VariableDependenceAnalyser(prog);
      varDepAnalyser.Analyse();
    }

    public void Analyse() {
      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Candidate dependence analysis: Getting candidates");
      }

      candidates = GetCandidates();

      DetermineCandidateVariableDependences();

      ConstructCandidateDependenceGraph();

      ConstructStagesDAG();

    }

    private void ConstructStagesDAG()
    {
      if (CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Candidate dependence analysis: Computing SCCs");
      }

      Adjacency<string> next = new Adjacency<string>(CandidateDependences.Successors);
      Adjacency<string> prev = new Adjacency<string>(CandidateDependences.Predecessors);
      SCCs = new StronglyConnectedComponents<string>(
        CandidateDependences.Nodes, next, prev);
      SCCs.Compute();

      if (CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Candidate dependence analysis: Building stages DAG");
      }

      Dictionary<string, SCC<string>> rep = new Dictionary<string, SCC<string>>();
      foreach (var scc in SCCs)
      {
        foreach (var s in scc)
        {
          rep[s] = scc;
        }
      }

      StagesDAG = new Graph<SCC<string>>();

      foreach (var edge in CandidateDependences.Edges)
      {
        if (rep[edge.Item1] != rep[edge.Item2])
        {
          StagesDAG.AddEdge(rep[edge.Item1], rep[edge.Item2]);
        }
      }

      SCC<string> dummy = new SCC<string>();
      foreach (var scc in SCCs)
      {
        StagesDAG.AddEdge(scc, dummy);
      }
    }

    private void ConstructCandidateDependenceGraph()
    {
      if (CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Candidate dependence analysis: Building dependence graph");
      }

      ICandidateReachabilityChecker reachabilityChecker;
      
      if(CommandLineOptions.Clo.StagedHoudiniReachabilityAnalysis) {
        reachabilityChecker = new CandidateReachabilityChecker(prog, candidates);
      } else {
        reachabilityChecker = new DummyCandidateReachabilityChecker();
      }

      CandidateDependences = new Graph<string>();
      foreach (var c in candidates)
      {
        CandidateDependences.AddEdge(c, c);
        foreach (var vd in candidateDependsOn[c])
        {
          if (variableDirectlyReferredToByCandidates.ContainsKey(vd))
          {
            foreach (var d in variableDirectlyReferredToByCandidates[vd])
            {
              if(reachabilityChecker.MayReach(d, c))
              {
                CandidateDependences.AddEdge(c, d);
              }
            }
          }
        }
      }

      if(CommandLineOptions.Clo.StagedHoudiniMergeIgnoredCandidates) {
        MergeIgnoredCandidates();
      }

    }

    private void MergeIgnoredCandidates()
    {
      var IgnoredCandidatesToVariables = new Dictionary<string, HashSet<Variable>>();
      foreach(var c in candidates) {
        IgnoredCandidatesToVariables[c] = new HashSet<Variable>();
      }
      foreach(var ci in CandidateInstances()) {
        if(!IgnoredCandidatesToVariables.ContainsKey(ci.Candidate)) {
          continue;
        }
        VariableCollector vc = new VariableCollector();
        vc.Visit(ci.Expr);
        if(vc.usedVars.Select(Item => varDepAnalyser.VariableRelevantToAnalysis(Item, ci.Proc)).Count() != 0) {
          continue;
        }
        foreach(var v in vc.usedVars) {
          if(varDepAnalyser.Ignoring(v, ci.Proc)) {
            IgnoredCandidatesToVariables[ci.Candidate].Add(v);
          }
        }
      }
      foreach(var c in IgnoredCandidatesToVariables.Keys) {
        foreach(var d in IgnoredCandidatesToVariables.Keys) {
          if(c == d) {
            continue;
          }
          if(IgnoredCandidatesToVariables[c].Equals(IgnoredCandidatesToVariables[d])) {
            CandidateDependences.AddEdge(c, d);
          }
        }
      }
    }



    private void DetermineCandidateVariableDependences()
    {
      if (CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Candidate dependence analysis: Working out what candidates depend on");
      }
      candidateDependsOn = new Dictionary<string, HashSet<VariableDescriptor>>();
      variableDirectlyReferredToByCandidates = new Dictionary<VariableDescriptor, HashSet<string>>();
      foreach (var c in candidates)
      {
        candidateDependsOn[c] = new HashSet<VariableDescriptor>();
      }

      foreach(var candidateInstance in CandidateInstances()) {
        AddDependences(candidateInstance);
      }

    }

    private IEnumerable<CandidateInstance> CandidateInstances()
    {
      foreach (var impl in prog.TopLevelDeclarations.OfType<Implementation>())
      {
        foreach (var b in impl.Blocks) {
          foreach (Cmd cmd in b.Cmds)
          {
            var p = cmd as PredicateCmd;
            if (p != null)
            {
              string c;
              if(Houdini.MatchCandidate(p.Expr, candidates, out c)) {
                yield return new CandidateInstance(c, impl.Name, p.Expr);
              }
            }
          }
        }
      }

      foreach (var proc in prog.TopLevelDeclarations.OfType<Procedure>())
      {
        foreach (Requires r in proc.Requires)
        {
          string c;
          if(Houdini.MatchCandidate(r.Condition, candidates, out c)) {
            yield return new CandidateInstance(c, proc.Name, r.Condition);
          }
        }
        foreach (Ensures e in proc.Ensures)
        {
          string c;
          if(Houdini.MatchCandidate(e.Condition, candidates, out c)) {
            yield return new CandidateInstance(c, proc.Name, e.Condition);
          }
        }
      }
    }

    private bool FindInDAG(Graph<SCC<string>> DAG, SCC<string> toFind, SCC<string> start) {
      if (toFind == start) {
        return true;
      }
      foreach (var n in DAG.Successors(start)) {
        if (FindInDAG(DAG, toFind, n)) {
          return true;
        }
      }
      return false;
    }

    private void AddDependences(CandidateInstance ci) {
      VariableCollector vc = new VariableCollector();
      vc.VisitExpr(ci.Expr);

      foreach (var v in vc.usedVars.Where(Item => varDepAnalyser.VariableRelevantToAnalysis(Item, ci.Proc))) {
        VariableDescriptor vd =
          varDepAnalyser.MakeDescriptor(ci.Proc, v);
        if (!variableDirectlyReferredToByCandidates.ContainsKey(vd)) {
          variableDirectlyReferredToByCandidates[vd] = new HashSet<string>();
        }
        variableDirectlyReferredToByCandidates[vd].Add(ci.Candidate);

        foreach (var w in varDepAnalyser.DependsOn(vd)) {
          candidateDependsOn[ci.Candidate].Add(w);
        }
      }
    }

    private bool IsStageDependence(SCC<string> Src, SCC<string> Dst) {
      foreach (var c in Src) {
        foreach (var d in CandidateDependences.Successors(c)) {
          if (Dst.Contains(d)) {
            return true;
          }
        }
      }
      return false;
    }


    public void dump() {

      if(CommandLineOptions.Clo.DebugStagedHoudini) {
        varDepAnalyser.dump();
      }

      /*Console.WriteLine("Candidates and the variables they depend on");
      Console.WriteLine("===========================================");
      foreach (var entry in candidateDependsOn) {
        Console.WriteLine(entry.Key + " <- ");
        foreach (var vd in entry.Value) {
          Console.WriteLine("  " + vd + ", ");
        }
      }

      Console.WriteLine("");

      Console.WriteLine("Variables and the candidates that directly refer to them");
      Console.WriteLine("========================================================");
      foreach (var entry in variableDirectlyReferredToByCandidates) {
        Console.WriteLine(entry.Key + " <- ");
        foreach (var candidate in entry.Value) {
          Console.WriteLine("  " + candidate + ", ");
        }
      }

      Console.WriteLine("");*/

      /*
      Console.WriteLine("Candidate dependence graph");
      Console.WriteLine("==========================");
      foreach (var c in CandidateDependences.Nodes) {
        Console.WriteLine(c + " <- ");
        foreach (var d in CandidateDependences.Successors(c)) {
          Console.WriteLine("  " + d);
        }
      }*/

      Console.WriteLine("");

      Console.WriteLine("Strongly connected components");
      Console.WriteLine("=============================");

      List<SCC<string>> Components = StagesDAG.TopologicalSort().ToList();

      for (int i = 0; i < Components.Count(); i++) {
        Console.Write(i + ": ");
        DumpSCC(Components[i]);
        Console.WriteLine(); Console.WriteLine();
      }

      Console.WriteLine("Stages DAG");
      Console.WriteLine("==========");
      for (int i = 0; i < Components.Count(); i++) {
        Console.Write(i + " -> { ");
        bool first = true;
        foreach (var d in StagesDAG.Successors(Components[i])) {
          if (first) {
            first = false;
          }
          else {
            Console.Write(", ");
          }
          Console.Write(Components.IndexOf(d));
        }
        Console.WriteLine(" }");
      }
    
    }

    private static void DumpSCC(SCC<string> component) {
      var sortedComponent = component.ToList();
      sortedComponent.Sort();
      Console.Write("{ ");
      bool first = true;
      foreach (var s in sortedComponent) {
        if (first) {
          first = false;
        }
        else {
          Console.Write(", ");
        }
        Console.Write(s);
      }
      Console.Write(" }");
    }

    private IEnumerable<string> GetCandidates() {
      return prog.TopLevelDeclarations.OfType<Variable>().Where(Item =>
        QKeyValue.FindBoolAttribute(Item.Attributes, "existential")).Select(Item => Item.Name);
    }


    public StagedHoudiniPlan ApplyStages() {

        if (NoStages())
        {
            return null;
        }

        #region Assign candidates to stages at a given level of granularity
      
        switch(CommandLineOptions.Clo.StagedHoudini) {
          case COARSE_STAGES:
            Plan = ComputeCoarseStages();
            break;
          case FINE_STAGES:
            Plan = ComputeFineStages();
            break;
          case BALANCED_STAGES:
            Plan = ComputeBalancedStages();
            break;
          default:
            Debug.Assert(false);
            Plan = null;
            break;
        }
        
        foreach(var c in candidates) {
          Debug.Assert(Plan.StageForCandidate(c) != null);
        }
        #endregion

        #region Generate boolean variables to control stages
        var stageToActiveBoolean = new Dictionary<int, Constant>();
        var stageToCompleteBoolean = new Dictionary<int, Constant>();

        foreach (var stage in Plan)
        {
            var stageActive = new Constant(Token.NoToken,
                new TypedIdent(Token.NoToken, "_stage_" + stage.GetId() + "_active", Type.Bool),
                false);
            stageActive.AddAttribute("stage_active", new object[] { new LiteralExpr(Token.NoToken, BigNum.FromInt(stage.GetId())) });
            prog.TopLevelDeclarations.Add(stageActive);
            stageToActiveBoolean[stage.GetId()] = stageActive;

            var stageComplete = new Constant(Token.NoToken, 
                new TypedIdent(Token.NoToken, "_stage_" + stage.GetId() + "_complete", Type.Bool),
                false);
            stageComplete.AddAttribute("stage_complete", new object[] { new LiteralExpr(Token.NoToken, BigNum.FromInt(stage.GetId())) });
            prog.TopLevelDeclarations.Add(stageComplete);
            stageToCompleteBoolean[stage.GetId()] = stageComplete;
        }
        #endregion

        #region Adapt candidate assertions to take account of stages
        foreach (var b in prog.TopLevelDeclarations.OfType<Implementation>().Select(Item => Item.Blocks).SelectMany(Item => Item))
        {
            List<Cmd> newCmds = new List<Cmd>();
            foreach (var cmd in b.Cmds)
            {
                var a = cmd as AssertCmd;
                string c;
                if (a != null && (Houdini.MatchCandidate(a.Expr, candidates, out c)))
                {
                    newCmds.Add(new AssertCmd(a.tok, Houdini.AddConditionToCandidate(a.Expr,
                        new IdentifierExpr(Token.NoToken, stageToActiveBoolean[Plan.StageForCandidate(c).GetId()]), c), a.Attributes));
                    newCmds.Add(new AssumeCmd(a.tok, Houdini.AddConditionToCandidate(a.Expr,
                        new IdentifierExpr(Token.NoToken, stageToCompleteBoolean[Plan.StageForCandidate(c).GetId()]), c), a.Attributes));
                }
                else
                {
                    newCmds.Add(cmd);
                }
            }
            b.Cmds = newCmds;
        }
        #endregion

        #region Adapt candidate pre/postconditions to take account of stages
        foreach (var p in prog.TopLevelDeclarations.OfType<Procedure>())
        {

          #region Handle the preconditions
          List<Requires> newRequires = new List<Requires>();
          foreach(Requires r in p.Requires) {
            string c;
            if (Houdini.MatchCandidate(r.Condition, candidates, out c)) {
              newRequires.Add(new Requires(r.tok, false, 
                Houdini.AddConditionToCandidate(r.Condition,
                new IdentifierExpr(Token.NoToken, stageToActiveBoolean[Plan.StageForCandidate(c).GetId()]), c),
                r.Comment, r.Attributes));
              newRequires.Add(new Requires(r.tok, true, 
                Houdini.AddConditionToCandidate(r.Condition,
                new IdentifierExpr(Token.NoToken, stageToCompleteBoolean[Plan.StageForCandidate(c).GetId()]), c),
                r.Comment, r.Attributes));
            } else {
              newRequires.Add(r);
            }
          }
          p.Requires = newRequires;
          #endregion

          #region Handle the postconditions
          List<Ensures> newEnsures = new List<Ensures>();
          foreach(Ensures e in p.Ensures) {
            string c;
            if (Houdini.MatchCandidate(e.Condition, candidates, out c)) {
              int stage = Plan.StageForCandidate(c).GetId();
              Constant activeBoolean = stageToActiveBoolean[stage];
              newEnsures.Add(new Ensures(e.tok, false, 
                Houdini.AddConditionToCandidate(e.Condition,
                new IdentifierExpr(Token.NoToken, activeBoolean), c),
                e.Comment, e.Attributes));
              newEnsures.Add(new Ensures(e.tok, true, 
                Houdini.AddConditionToCandidate(e.Condition,
                new IdentifierExpr(Token.NoToken, stageToCompleteBoolean[stage]), c),
                e.Comment, e.Attributes));
            } else {
              newEnsures.Add(e);
            }
          }
          p.Ensures = newEnsures;
          #endregion

        }
        #endregion

        return Plan;

    }

    private int FindLargestStage() {
      return StagesDAG.Nodes.Select(Item => Item.Count()).Max();
    }


    private StagedHoudiniPlan ComputeCoarseStages()
    {
        foreach(var n in StagesDAG.Nodes) {
          Debug.Assert(!StagesDAG.Successors(n).Contains(n));
        }

        Graph<ScheduledStage> Dependences = new Graph<ScheduledStage>();

        var done = new Dictionary<SCC<string>, ScheduledStage>();
        done[GetStartNodeOfStagesDAG()] = new ScheduledStage(0, new HashSet<string>());

        for(int stageId = 1; done.Count() != StagesDAG.Nodes.Count(); stageId++)
        {
            var Stage = new ScheduledStage(stageId, new HashSet<string>());
            HashSet<SCC<string>> AssignedToThisStage = new HashSet<SCC<string>>();

            foreach (var n in StagesDAG.Nodes.Where(Item => !done.ContainsKey(Item)))
            {
              if(StagesDAG.Successors(n).Where(Item => !done.ContainsKey(Item)).Count() == 0) {
                foreach(var s in StagesDAG.Successors(n)) {
                  Debug.Assert(s != n);
                  Debug.Assert(Stage != done[s]);
                  Dependences.AddEdge(Stage, done[s]);
                }
                foreach (var c in n)
                {
                  Stage.AddCandidate(c);
                }
                Console.Write(n.Count() + ", ");
                AssignedToThisStage.Add(n);
              }
            }

            Console.WriteLine("total: " + Stage.Count());

            foreach(var n in AssignedToThisStage) {
              done[n] = Stage;
            }
        }
        return new StagedHoudiniPlan(Dependences);
    }

    private StagedHoudiniPlan ComputeBalancedStages()
    {
      Graph<ScheduledStage> Dependences = new Graph<ScheduledStage>();
      var done = new Dictionary<SCC<string>, ScheduledStage>();
      done[GetStartNodeOfStagesDAG()] = new ScheduledStage(0, new HashSet<string>());

      int maxStageSize = 200;

      for(int stageId = 1; done.Count() != StagesDAG.Nodes.Count(); stageId++)
      {
        int stageSize = 0;
        ScheduledStage Stage = new ScheduledStage(stageId, new HashSet<string>());
        HashSet<SCC<string>> AddedToThisStage = new HashSet<SCC<string>>();

        foreach (var n in StagesDAG.Nodes.Where(Item => !done.ContainsKey(Item)))
        {
          if(stageSize + n.Count() > maxStageSize) {
            continue;
          }
          if(StagesDAG.Successors(n).Where(Item => !done.ContainsKey(Item)).Count() == 0) {
            foreach (var c in n)
            {
              Stage.AddCandidate(c);
              stageSize++;
            }
            foreach(var s in StagesDAG.Successors(n)) {
              Dependences.AddEdge(Stage, done[s]);
            }
            AddedToThisStage.Add(n);
          }
        }
        foreach(var n in AddedToThisStage) {
          done[n] = Stage;
        }
        if(stageSize == 0) {
          maxStageSize *= 2;
        }
      }
      return new StagedHoudiniPlan(Dependences);
    }

    private StagedHoudiniPlan ComputeFineStages()
    {
      Graph<ScheduledStage> Dependences = new Graph<ScheduledStage>();
      var done = new Dictionary<SCC<string>, ScheduledStage>();

      List<SCC<string>> components = StagesDAG.TopologicalSort().ToList();
      components.Reverse();

      for (int i = 0; i < components.Count(); i++)
      {
        ScheduledStage Stage = new ScheduledStage(i, new HashSet<string>());
        done[components[i]] = Stage;
        foreach (var c in components[i])
        {
          Stage.AddCandidate(c);
        }
        foreach(var s in StagesDAG.Successors(components[i])) {
          Dependences.AddEdge(Stage, done[s]);
        }
      }
      return new StagedHoudiniPlan(Dependences);
    }

    private SCC<string> GetStartNodeOfStagesDAG()
    {
      return StagesDAG.Nodes.Where(Item => StagesDAG.Successors(Item).Count() == 0).
        ToList()[0];
    }

    private bool NoStages()
    {
        return candidates.Count() == 0 || StagesDAG.Nodes.Count() == 0;
    }
  }

  interface ICandidateReachabilityChecker {
    bool MayReach(string c, string d);
  }

  class DummyCandidateReachabilityChecker : ICandidateReachabilityChecker {
    public bool MayReach(string c, string d) {
      return true;
    }
  }

  class CandidateReachabilityChecker : ICandidateReachabilityChecker {

    private enum PrePost {
      PRE, POST
    }

    private Program prog;
    private IEnumerable<string> candidates;
    private IInterproceduralReachabilityGraph reachabilityGraph;
    private Dictionary<string, HashSet<object>> candidateToOccurences;

    internal CandidateReachabilityChecker(Program prog, IEnumerable<string> candidates) {
      this.prog = prog;
      this.candidates = candidates;
      this.reachabilityGraph = new InterproceduralReachabilityGraph(prog);
      this.candidateToOccurences = new Dictionary<string,HashSet<object>>();

      // Add all candidate occurrences in blocks
      foreach(Block b in prog.TopLevelDeclarations.OfType<Implementation>().Select(Item => Item.Blocks).SelectMany(Item => Item)) {
        foreach(Cmd cmd in b.Cmds) {
          AssertCmd assertCmd = cmd as AssertCmd;
          if(assertCmd != null) {
            string c;
            if(Houdini.MatchCandidate(assertCmd.Expr, candidates, out c)) {
              AddCandidateOccurrence(c, b);
            }
          }
        }
      }

      // Add all candidate occurrences in preconditions
      foreach(var proc in prog.TopLevelDeclarations.OfType<Procedure>()) {
        foreach(Requires r in proc.Requires) {
          string c;
          if(Houdini.MatchCandidate(r.Condition, candidates, out c)) {
            AddCandidateOccurrence(c, new Tuple<string, PrePost>(proc.Name, PrePost.PRE));
          }
        }
      }

      // Add all candidate occurrences in preconditions
      foreach(var proc in prog.TopLevelDeclarations.OfType<Procedure>()) {
        foreach(Ensures e in proc.Ensures) {
          string c;
          if(Houdini.MatchCandidate(e.Condition, candidates, out c)) {
            AddCandidateOccurrence(c, new Tuple<string, PrePost>(proc.Name, PrePost.POST));
          }
        }
      }
      
    }

    private void AddCandidateOccurrence(string c, object o) {
      Debug.Assert(o is Block || o is Tuple<string, PrePost>);
      if(!candidateToOccurences.ContainsKey(c)) {
        candidateToOccurences[c] = new HashSet<object>();
      }
      candidateToOccurences[c].Add(o);
    }

    public bool MayReach(string c, string d) {
      foreach(object cOccurrence in candidateToOccurences[c]) {
        foreach(object dOccurrence in candidateToOccurences[d]) {
          if(OccurrencesMayReach(cOccurrence, dOccurrence)) {
            return true;
          }
        }
      }
      return false;
    }

    private bool OccurrencesMayReach(object cOccurrence, object dOccurrence) {
      Debug.Assert(cOccurrence is Block || cOccurrence is Tuple<string, PrePost>);
      Debug.Assert(dOccurrence is Block || dOccurrence is Tuple<string, PrePost>);

      Block cInterproceduralBlock = GetInterproceduralBlock(cOccurrence);
      Block dInterproceduralBlock = GetInterproceduralBlock(dOccurrence);

      return reachabilityGraph.MayReach(cInterproceduralBlock, dInterproceduralBlock);

      throw new NotImplementedException();
    }

    private Block GetInterproceduralBlock(object cOccurrence)
    {
      Debug.Assert(cOccurrence is Block || cOccurrence is Tuple<string, PrePost>);

      var stringPrePostPair = cOccurrence as Tuple<string, PrePost>;
      if(stringPrePostPair != null) {
        if(stringPrePostPair.Item2 == PrePost.PRE) {
          return reachabilityGraph.GetNewEntryBlock(stringPrePostPair.Item1);
        } else {
          return reachabilityGraph.GetNewExitBlock(stringPrePostPair.Item1);
        }
      }

      return reachabilityGraph.GetNewBlock((Block)cOccurrence);

    }
  }

  class CandidateInstance {
    public string Candidate;
    public string Proc;
    public Expr Expr;

    internal CandidateInstance(string Candidate, string Proc, Expr Expr) {
      this.Candidate = Candidate;
      this.Proc = Proc;
      this.Expr = Expr;
    }
  }

}
