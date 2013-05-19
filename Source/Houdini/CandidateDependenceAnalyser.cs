using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Basetypes;
using System.Diagnostics;

namespace Microsoft.Boogie {

  public class CandidateDependenceAnalyser {

    private const int COARSE_STAGES = 1;
    private const int FINE_STAGES = 2;

    private Program prog;
    private IVariableDependenceAnalyser varDepAnalyser;
    private IEnumerable<string> candidates;
    private Dictionary<string, HashSet<VariableDescriptor>> candidateDependsOn;
    private Dictionary<VariableDescriptor, HashSet<string>> variableDirectlyReferredToByCandidates;
    private Graph<string> CandidateDependences;
    private StronglyConnectedComponents<string> SCCs;
    private Graph<SCC<string>> StagesDAG;

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

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Candidate dependence analysis: Working out what candidates depend on");
      }
      candidateDependsOn = new Dictionary<string, HashSet<VariableDescriptor>>();
      variableDirectlyReferredToByCandidates = new Dictionary<VariableDescriptor, HashSet<string>>();
      foreach (var c in candidates) {
        candidateDependsOn[c] = new HashSet<VariableDescriptor>();
      }

      // Candidate loop invariants
      foreach(var impl in prog.TopLevelDeclarations.OfType<Implementation>()) {
        foreach(var b in impl.Blocks) {
          foreach (Cmd c in b.Cmds) {
            var p = c as PredicateCmd;
            if (p != null) {
              CheckExpr(impl.Name, p.Expr);
            }
          }
        }
      }

      foreach (var proc in prog.TopLevelDeclarations.OfType<Procedure>()) {
        foreach (Requires r in proc.Requires) {
          CheckExpr(proc.Name, r.Condition);
        }
        foreach (Ensures e in proc.Ensures) {
          CheckExpr(proc.Name, e.Condition);
        }
      }

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Candidate dependence analysis: Building dependence graph");
      }

      CandidateDependences = new Graph<string>();

      foreach (var c in candidates) {
        foreach (var vd in candidateDependsOn[c]) {
          if (variableDirectlyReferredToByCandidates.ContainsKey(vd)) {
            foreach (var d in variableDirectlyReferredToByCandidates[vd]) {
              CandidateDependences.AddEdge(c, d);
            }
          }
        }
      }

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Candidate dependence analysis: Computing SCCs");
      }

      Adjacency<string> next = new Adjacency<string>(CandidateDependences.Successors);
      Adjacency<string> prev = new Adjacency<string>(CandidateDependences.Predecessors);
      SCCs = new StronglyConnectedComponents<string>(
        CandidateDependences.Nodes, next, prev);
      SCCs.Compute();

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Candidate dependence analysis: Building stages DAG");
      }

      Dictionary<string, SCC<string>> rep = new Dictionary<string, SCC<string>>();
      foreach (var scc in SCCs) {
        foreach (var s in scc) {
          rep[s] = scc;
        }
      }

      StagesDAG = new Graph<SCC<string>>();

      foreach (var edge in CandidateDependences.Edges) {
        if (rep[edge.Item1] != rep[edge.Item2]) {
          StagesDAG.AddEdge(rep[edge.Item1], rep[edge.Item2]);
        }
      }

      SCC<string> dummy = new SCC<string>();
      foreach (var scc in SCCs) {
        StagesDAG.AddEdge(scc, dummy);
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

    private void CheckExpr(string proc, Expr e) {
      string candidate;
      Houdini.Houdini.MatchCandidate(e, candidates, out candidate);
      if (candidate != null) {
        VariableCollector vc = new VariableCollector();
        vc.VisitExpr(e);

        foreach (var v in vc.usedVars.Where(Item => !(Item is Constant))) {
          VariableDescriptor vd =
            varDepAnalyser.MakeDescriptor(proc, v);
          if (!variableDirectlyReferredToByCandidates.ContainsKey(vd)) {
            variableDirectlyReferredToByCandidates[vd] = new HashSet<string>();
          }
          variableDirectlyReferredToByCandidates[vd].Add(candidate);

          foreach (var w in varDepAnalyser.DependsOn(vd)) {
            candidateDependsOn[candidate].Add(w);
          }
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

      varDepAnalyser.dump();

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
        Console.WriteLine("\n");
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


    public void ApplyStages() {

        if (NoStages())
        {
            return;
        }

        #region Assign candidates to stages at a given level of granularity
        Debug.Assert(CommandLineOptions.Clo.StagedHoudini == COARSE_STAGES ||
                   CommandLineOptions.Clo.StagedHoudini == FINE_STAGES);
        Dictionary<string, int> candidateToStage =
            (CommandLineOptions.Clo.StagedHoudini == COARSE_STAGES) ? ComputeCoarseStages()
            : ComputeFineStages();
        #endregion

        #region Generate boolean variables to control stages
        var stageToActiveBoolean = new Dictionary<int, Constant>();
        var stageToCompleteBoolean = new Dictionary<int, Constant>();

        foreach (var stage in new HashSet<int>(candidateToStage.Values))
        {
            var stageActive = new Constant(Token.NoToken,
                new TypedIdent(Token.NoToken, "_stage_" + stage + "_active", Type.Bool),
                false);
            stageActive.AddAttribute("stage_active", new object[] { new LiteralExpr(Token.NoToken, BigNum.FromInt(stage)) });
            prog.TopLevelDeclarations.Add(stageActive);
            stageToActiveBoolean[stage] = stageActive;

            var stageComplete = new Constant(Token.NoToken, 
                new TypedIdent(Token.NoToken, "_stage_" + stage + "_complete", Type.Bool),
                false);
            stageComplete.AddAttribute("stage_complete", new object[] { new LiteralExpr(Token.NoToken, BigNum.FromInt(stage)) });
            prog.TopLevelDeclarations.Add(stageComplete);
            stageToCompleteBoolean[stage] = stageComplete;
        }
        #endregion

        #region Adapt candidate assertions to take account of stages
        foreach (var b in prog.TopLevelDeclarations.OfType<Implementation>().Select(Item => Item.Blocks).SelectMany(Item => Item))
        {
            CmdSeq newCmds = new CmdSeq();
            foreach (var cmd in b.Cmds)
            {
                var a = cmd as AssertCmd;
                string c;
                if (a != null && (Houdini.Houdini.MatchCandidate(a.Expr, candidates, out c)))
                {
                    newCmds.Add(new AssertCmd(a.tok, Houdini.Houdini.AddConditionToCandidate(a.Expr,
                        new IdentifierExpr(Token.NoToken, stageToActiveBoolean[candidateToStage[c]]), c), a.Attributes));
                    newCmds.Add(new AssumeCmd(a.tok, Houdini.Houdini.AddConditionToCandidate(a.Expr,
                        new IdentifierExpr(Token.NoToken, stageToCompleteBoolean[candidateToStage[c]]), c), a.Attributes));
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
          RequiresSeq newRequires = new RequiresSeq();
          foreach(Requires r in p.Requires) {
            string c;
            if (Houdini.Houdini.MatchCandidate(r.Condition, candidates, out c)) {
              newRequires.Add(new Requires(r.tok, false, 
                Houdini.Houdini.AddConditionToCandidate(r.Condition,
                new IdentifierExpr(Token.NoToken, stageToActiveBoolean[candidateToStage[c]]), c),
                r.Comment, r.Attributes));
              newRequires.Add(new Requires(r.tok, true, 
                Houdini.Houdini.AddConditionToCandidate(r.Condition,
                new IdentifierExpr(Token.NoToken, stageToCompleteBoolean[candidateToStage[c]]), c),
                r.Comment, r.Attributes));
            } else {
              newRequires.Add(r);
            }
          }
          p.Requires = newRequires;
          #endregion

          #region Handle the postconditions
          EnsuresSeq newEnsures = new EnsuresSeq();
          foreach(Ensures e in p.Ensures) {
            string c;
            if (Houdini.Houdini.MatchCandidate(e.Condition, candidates, out c)) {
              newEnsures.Add(new Ensures(e.tok, false, 
                Houdini.Houdini.AddConditionToCandidate(e.Condition,
                new IdentifierExpr(Token.NoToken, stageToActiveBoolean[candidateToStage[c]]), c),
                e.Comment, e.Attributes));
              newEnsures.Add(new Ensures(e.tok, true, 
                Houdini.Houdini.AddConditionToCandidate(e.Condition,
                new IdentifierExpr(Token.NoToken, stageToCompleteBoolean[candidateToStage[c]]), c),
                e.Comment, e.Attributes));
            } else {
              newRequires.Add(e);
            }
          }
          p.Ensures = newEnsures;
          #endregion

        }
        #endregion

    }

    private Dictionary<string, int> ComputeFineStages()
    {
        var result = new Dictionary<string, int>();
        List<SCC<string>> components = StagesDAG.TopologicalSort().ToList();
        components.Reverse();

        System.Diagnostics.Debug.Assert(components[0].Count() == 0);
        for (int i = 1; i < components.Count(); i++)
        {
            foreach (var c in components[i])
            {
                result[c] = i - 1;
            }

        }
        return result;

    }

    private Dictionary<string, int> ComputeCoarseStages()
    {
        var result = new Dictionary<string, int>();
        SCC<string> start = null;
        foreach (var n in StagesDAG.Nodes)
        {
            if (StagesDAG.Successors(n).Count() == 0)
            {
                start = n;
                break;
            }
        }
        System.Diagnostics.Debug.Assert(start != null);

        HashSet<SCC<string>> done = new HashSet<SCC<string>>();
        done.Add(start);

        bool finished = false;
        int stageId = 0;
        while (!finished)
        {
            finished = true;
            HashSet<SCC<string>> stage = new HashSet<SCC<string>>();
            foreach (var n in StagesDAG.Nodes)
            {
                if (!done.Contains(n))
                {
                    finished = false;
                    bool ready = true;
                    foreach (var m in StagesDAG.Successors(n))
                    {
                        if (!done.Contains(m))
                        {
                            ready = false;
                            break;
                        }
                    }
                    if (ready)
                    {
                        stage.Add(n);
                        done.Add(n);
                    }
                }
            }

            foreach (var scc in stage)
            {
                foreach (var c in scc)
                {
                    result[c] = stageId;
                }
            }

            stageId++;
        }
        return result;
    }

    private bool NoStages()
    {
        return candidates.Count() == 0 || StagesDAG.Nodes.Count() == 0;
    }
  }

}
