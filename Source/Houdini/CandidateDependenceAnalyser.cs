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

      DetermineCandidateVariableDependences();

      //ConstructCandidateReachabilityGraph();

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
              if (MayReach(c, d))
              {
                CandidateDependences.AddEdge(c, d);
              }
            }
          }
        }
      }
    }

    private void ConstructCandidateReachabilityGraph()
    {
      Dictionary<string, List<Block>> procedureCFGs = new Dictionary<string, List<Block>>();
      Dictionary<string, HashSet<Block>> candidateToUse = new Dictionary<string, HashSet<Block>>();

      #region Prepare implementations
      foreach (var impl in prog.TopLevelDeclarations.OfType<Implementation>()) {
        procedureCFGs[impl.Name] = PrepareImplementationForCandidateReachability(impl);
      }
      #endregion

      #region Prepare any procedures that do not have implementations
      foreach (var proc in prog.TopLevelDeclarations.OfType<Procedure>()) {
        if(!procedureCFGs.ContainsKey(proc.Name)) {
          procedureCFGs[proc.Name] = PrepareProcedureForCandidateReachability(proc);
        }
      }
      #endregion

      #region Transform prepared CFGs so that every call is in its own basic block
      foreach(var proc in procedureCFGs.Keys) {
        List<Block> newCFG = new List<Block>();
        Dictionary<Block, Block> oldToNew = new Dictionary<Block, Block>();

        foreach(var bb in procedureCFGs[proc]) {
          List<List<Cmd>> partition = new List<List<Cmd>>();
          List<Cmd> current = new List<Cmd>();
          partition.Add(current);
          foreach(Cmd cmd in bb.Cmds) {
            if(cmd is CallCmd && current.Count > 0) {
              current = new List<Cmd>();
              partition.Add(current);
            }
            current.Add(cmd);
          }

          if(partition.Count > 1) {
            Block last = null;
            int i = 0;
            foreach(var cmdList in partition) {
              Block newBB = new Block(bb.tok, bb.Label + "_" + i, new CmdSeq(cmdList.ToArray()), null);
              newCFG.Add(newBB);
              if(last == null) {
                oldToNew[bb] = newBB;
              } else {
                oldToNew[newBB] = newBB;
                last.TransferCmd = new GotoCmd(last.tok, new BlockSeq { newBB });
              }
              last = newBB;
              i++;
            }
            Debug.Assert(last != null);
            Debug.Assert(last.TransferCmd == null);
            last.TransferCmd = bb.TransferCmd;
          } else {
            newCFG.Add(bb);
            oldToNew[bb] = bb;
          }

        }

        ApplyPatchupMap(newCFG, oldToNew);
        procedureCFGs[proc] = newCFG;

      }
      #endregion

      #region Replace calls with inter-procedural edges
      foreach(var bb in procedureCFGs.Values.SelectMany(Item => Item)) {
        if(bb.Cmds.Length == 1 && bb.Cmds[0] is CallCmd) {
          Debug.Assert(bb.TransferCmd is GotoCmd);
          string proc = (bb.Cmds[0] as CallCmd).callee;

          Block returnBB = procedureCFGs[proc].Last();
          if(returnBB.TransferCmd is ReturnCmd) {
            returnBB.TransferCmd = bb.TransferCmd;
          } else {
            Debug.Assert(returnBB.TransferCmd is GotoCmd);
            GotoCmd gotoCmd = returnBB.TransferCmd as GotoCmd;
            gotoCmd.labelTargets.AddRange(((GotoCmd)bb.TransferCmd).labelTargets);
          }

          Block entryBB = procedureCFGs[proc].First();
          bb.TransferCmd = new GotoCmd(Token.NoToken, new BlockSeq { entryBB });
        }
      }
      #endregion

      throw new NotImplementedException();

    }

    private static List<Block> PrepareProcedureForCandidateReachability(Procedure proc)
    {
      Block ensuresBlock = new Block(proc.tok, "postconditions",
        EnsuresToAssertSequence(proc.Ensures),
          new ReturnCmd(Token.NoToken));
      Block requiresBlock = new Block(proc.tok, "preconditions",
        RequiresToAssertSequence(proc.Requires),
          new GotoCmd(Token.NoToken, new BlockSeq { ensuresBlock }));
      return new List<Block> { requiresBlock, ensuresBlock };
    }

    private static List<Block> PrepareImplementationForCandidateReachability(Implementation impl)
    {
      // Clone the BBs and keep patchup map
      List<Block> newBBs = new List<Block>();
      Dictionary<Block, Block> oldToNew = new Dictionary<Block, Block>();
      foreach (var bb in impl.Blocks)
      {
        Block newBB = new Block(bb.tok, bb.Label, bb.Cmds, bb.TransferCmd);
        oldToNew[bb] = newBB;
        newBBs.Add(newBB);
      }
      ApplyPatchupMap(newBBs, oldToNew);
      Block newEntry = new Block(Token.NoToken, "preconditions",
        RequiresToAssertSequence(impl.Proc.Requires),
        new GotoCmd(Token.NoToken, new BlockSeq { newBBs[0] }));

      Block newExit = new Block(Token.NoToken, "postconditions",
        EnsuresToAssertSequence(impl.Proc.Ensures),
        new ReturnCmd(Token.NoToken));

      foreach (var newBB in newBBs)
      {
        if (newBB.TransferCmd is ReturnCmd ||
           (newBB.TransferCmd is GotoCmd && ((GotoCmd)newBB.TransferCmd).labelTargets.Length == 0))
        {
          newBB.TransferCmd = new GotoCmd(Token.NoToken, new BlockSeq { newExit });
        }
      }

      newBBs.Insert(0, newEntry);
      newBBs.Add(newExit);
      return newBBs;
    }

    private static void ApplyPatchupMap(List<Block> newBBs, Dictionary<Block, Block> oldToNew)
    {
      foreach (var newBB in newBBs)
      {
        GotoCmd gotoCmd = newBB.TransferCmd as GotoCmd;
        if (gotoCmd != null)
        {
          gotoCmd.labelTargets = new BlockSeq(((Block[])gotoCmd.labelTargets.ToArray()).
            Select(Item => oldToNew[Item]).ToArray());
        }
      }
    }

    private static CmdSeq RequiresToAssertSequence(RequiresSeq Requires)
    {
      return new CmdSeq(((Requires[])Requires.ToArray()).Select(
                Item => new AssertCmd(Item.tok, Item.Condition)).ToArray());
    }

    private static CmdSeq EnsuresToAssertSequence(EnsuresSeq Ensures)
    {
      return new CmdSeq(((Ensures[])Ensures.ToArray()).Select(
                Item => new AssertCmd(Item.tok, Item.Condition)).ToArray());
    }

    private bool MayReach(string c, string d)
    {
      return true;
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

      // Candidate loop invariants
      foreach (var impl in prog.TopLevelDeclarations.OfType<Implementation>())
      {
        foreach (var b in impl.Blocks)
        {
          foreach (Cmd c in b.Cmds)
          {
            var p = c as PredicateCmd;
            if (p != null)
            {
              CheckExpr(impl.Name, p.Expr);
            }
          }
        }
      }

      foreach (var proc in prog.TopLevelDeclarations.OfType<Procedure>())
      {
        foreach (Requires r in proc.Requires)
        {
          CheckExpr(proc.Name, r.Condition);
        }
        foreach (Ensures e in proc.Ensures)
        {
          CheckExpr(proc.Name, e.Condition);
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

    private void CheckExpr(string proc, Expr e) {
      string candidate;
      Houdini.Houdini.MatchCandidate(e, candidates, out candidate);
      if (candidate != null) {
        VariableCollector vc = new VariableCollector();
        vc.VisitExpr(e);

        foreach (var v in vc.usedVars.Where(Item => varDepAnalyser.VariableRelevantToAnalysis(Item, proc))) {
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
        
        foreach(var c in candidates) {
          Debug.Assert(candidateToStage.ContainsKey(c));
        }
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
              int stage = candidateToStage[c];
              Constant activeBoolean = stageToActiveBoolean[stage];
              newEnsures.Add(new Ensures(e.tok, false, 
                Houdini.Houdini.AddConditionToCandidate(e.Condition,
                new IdentifierExpr(Token.NoToken, activeBoolean), c),
                e.Comment, e.Attributes));
              newEnsures.Add(new Ensures(e.tok, true, 
                Houdini.Houdini.AddConditionToCandidate(e.Condition,
                new IdentifierExpr(Token.NoToken, stageToCompleteBoolean[candidateToStage[c]]), c),
                e.Comment, e.Attributes));
            } else {
              newEnsures.Add(e);
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

        foreach(var c in candidates) {
          Debug.Assert(result.ContainsKey(c));
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
