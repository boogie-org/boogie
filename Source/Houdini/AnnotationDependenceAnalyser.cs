using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Basetypes;
using System.Diagnostics;

namespace Microsoft.Boogie.Houdini {

  public class AnnotationDependenceAnalyser {

    private const string COARSE_STAGES = "COARSE";
    private const string FINE_STAGES = "FINE";
    private const string BALANCED_STAGES = "BALANCED";

    private Program prog;
    private IVariableDependenceAnalyser varDepAnalyser;
    private IEnumerable<string> CandidateIdentifiers; // Candidate Boolean names
    private IEnumerable<string> NonCandidateIdentifiers; // Additional names introduced for non-candidate annotations
    private Dictionary<string, HashSet<VariableDescriptor>> annotationDependsOn;
    private Dictionary<VariableDescriptor, HashSet<string>> variableDirectlyReferredToByAnnotations;
    private Graph<string> AnnotationDependences;
    private StronglyConnectedComponents<string> SCCs;
    private Graph<SCC<string>> StagesDAG;
    private StagedHoudiniPlan Plan;

    public AnnotationDependenceAnalyser(Program prog) {
      this.prog = prog;
      this.varDepAnalyser = new VariableDependenceAnalyser(prog);
      varDepAnalyser.Analyse();
    }

    public void Analyse() {
      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Annotation dependence analysis: Getting annotations");
      }

      CandidateIdentifiers = GetCandidates();
      NonCandidateIdentifiers = GetNonCandidateAnnotations();

      DetermineAnnotationVariableDependences();

      ConstructAnnotationDependenceGraph();

      ConstructStagesDAG();

    }

    private IEnumerable<string> AllAnnotationIdentifiers() {
      HashSet<string> Result = new HashSet<string>();
      foreach (var c in CandidateIdentifiers) {
        Result.Add(c);
      }
      foreach (var a in NonCandidateIdentifiers) {
        Result.Add(a);
      }
      return Result;
    }

    private void ConstructStagesDAG()
    {
      if (CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Annotation dependence analysis: Computing SCCs");
      }

      Adjacency<string> next = new Adjacency<string>(AnnotationDependences.Successors);
      Adjacency<string> prev = new Adjacency<string>(AnnotationDependences.Predecessors);
      SCCs = new StronglyConnectedComponents<string>(
        AnnotationDependences.Nodes, next, prev);
      SCCs.Compute();

      if (CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Annotation dependence analysis: Building stages DAG");
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

      foreach (var edge in AnnotationDependences.Edges)
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

    private void ConstructAnnotationDependenceGraph()
    {
      if (CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Annotation dependence analysis: Building dependence graph");
      }

      IAnnotationReachabilityChecker reachabilityChecker;
      
      if(CommandLineOptions.Clo.StagedHoudiniReachabilityAnalysis) {
        reachabilityChecker = new AnnotationReachabilityChecker(prog, AllAnnotationIdentifiers());
      } else {
        reachabilityChecker = new DummyAnnotationReachabilityChecker();
      }

      AnnotationDependences = new Graph<string>();
      foreach (var c in AllAnnotationIdentifiers())
      {
        AnnotationDependences.AddEdge(c, c);
        foreach (var vd in annotationDependsOn[c])
        {
          if (variableDirectlyReferredToByAnnotations.ContainsKey(vd))
          {
            foreach (var d in variableDirectlyReferredToByAnnotations[vd])
            {
              if(reachabilityChecker.MayReach(d, c))
              {
                AnnotationDependences.AddEdge(c, d);
              }
            }
          }
        }
      }

      if(CommandLineOptions.Clo.StagedHoudiniMergeIgnoredAnnotations) {
        MergeIgnoredAnnotations();
      }

    }

    private void MergeIgnoredAnnotations()
    {
      var IgnoredAnnotationsToVariables = new Dictionary<string, HashSet<Variable>>();
      foreach(var c in AllAnnotationIdentifiers()) {
        IgnoredAnnotationsToVariables[c] = new HashSet<Variable>();
      }
      foreach(var ci in AnnotationInstances()) {
        if(!IgnoredAnnotationsToVariables.ContainsKey(ci.AnnotationIdentifier)) {
          continue;
        }
        VariableCollector vc = new VariableCollector();
        vc.Visit(ci.Expr);
        if(vc.usedVars.Select(Item => varDepAnalyser.VariableRelevantToAnalysis(Item, ci.Proc)).Count() != 0) {
          continue;
        }
        foreach(var v in vc.usedVars) {
          if(varDepAnalyser.Ignoring(v, ci.Proc)) {
            IgnoredAnnotationsToVariables[ci.AnnotationIdentifier].Add(v);
          }
        }
      }
      foreach(var c in IgnoredAnnotationsToVariables.Keys) {
        foreach(var d in IgnoredAnnotationsToVariables.Keys) {
          if(c == d) {
            continue;
          }
          if(IgnoredAnnotationsToVariables[c].Equals(IgnoredAnnotationsToVariables[d])) {
            AnnotationDependences.AddEdge(c, d);
          }
        }
      }
    }



    private void DetermineAnnotationVariableDependences()
    {
      if (CommandLineOptions.Clo.Trace)
      {
        Console.WriteLine("Annotation dependence analysis: Working out what annotations depend on");
      }
      annotationDependsOn = new Dictionary<string, HashSet<VariableDescriptor>>();
      variableDirectlyReferredToByAnnotations = new Dictionary<VariableDescriptor, HashSet<string>>();
      foreach (var c in AllAnnotationIdentifiers())
      {
        annotationDependsOn[c] = new HashSet<VariableDescriptor>();
      }

      foreach(var annotationInstance in AnnotationInstances()) {
        AddDependences(annotationInstance);
      }

    }

    private IEnumerable<AnnotationInstance> AnnotationInstances()
    {
      foreach (var impl in prog.Implementations)
      {
        foreach (PredicateCmd p in impl.Blocks.SelectMany(Item => Item.Cmds).OfType<PredicateCmd>())
        {
          string c;
          if(Houdini.MatchCandidate(p.Expr, CandidateIdentifiers, out c)) {
            yield return new AnnotationInstance(c, impl.Name, p.Expr);
          } else if((p is AssertCmd) && QKeyValue.FindBoolAttribute(p.Attributes, "originated_from_invariant")) {
            var tag = GetTagFromNonCandidateAttributes(p.Attributes);
            if (tag != null) {
              yield return new AnnotationInstance(tag, impl.Name, p.Expr);
            }
          }
        }
      }

      foreach (var proc in prog.NonInlinedProcedures())
      {
        foreach (Requires r in proc.Requires)
        {
          string c;
          if(Houdini.MatchCandidate(r.Condition, CandidateIdentifiers, out c)) {
            yield return new AnnotationInstance(c, proc.Name, r.Condition);
          } else {
            var tag = GetTagFromNonCandidateAttributes(r.Attributes);
            if (tag != null) {
              yield return new AnnotationInstance(tag, proc.Name, r.Condition);
            }
          }
        }
        foreach (Ensures e in proc.Ensures)
        {
          string c;
          if(Houdini.MatchCandidate(e.Condition, CandidateIdentifiers, out c)) {
            yield return new AnnotationInstance(c, proc.Name, e.Condition);
          } else {
            var tag = GetTagFromNonCandidateAttributes(e.Attributes);
            if (tag != null) {
              yield return new AnnotationInstance(tag, proc.Name, e.Condition);
            }
          }
        }
      }
    }

    internal static string GetTagFromNonCandidateAttributes(QKeyValue Attributes)
    {
      string tag = QKeyValue.FindStringAttribute(Attributes, "staged_houdini_tag");
      return tag;
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

    private void AddDependences(AnnotationInstance ci) {
      VariableCollector vc = new VariableCollector();
      vc.VisitExpr(ci.Expr);

      foreach (var v in vc.usedVars.Where(Item => varDepAnalyser.VariableRelevantToAnalysis(Item, ci.Proc))) {
        VariableDescriptor vd =
          varDepAnalyser.MakeDescriptor(ci.Proc, v);
        if (!variableDirectlyReferredToByAnnotations.ContainsKey(vd)) {
          variableDirectlyReferredToByAnnotations[vd] = new HashSet<string>();
        }
        variableDirectlyReferredToByAnnotations[vd].Add(ci.AnnotationIdentifier);

        foreach (var w in varDepAnalyser.DependsOn(vd)) {
          annotationDependsOn[ci.AnnotationIdentifier].Add(w);
        }
      }
    }

    private bool IsStageDependence(SCC<string> Src, SCC<string> Dst) {
      foreach (var c in Src) {
        foreach (var d in AnnotationDependences.Successors(c)) {
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

        Console.WriteLine("Annotations and the variables they depend on");
        Console.WriteLine("============================================");
        foreach (var entry in annotationDependsOn) {
          Console.WriteLine(entry.Key + " <- ");
          foreach (var vd in entry.Value) {
            Console.WriteLine("  " + vd + ", ");
          }
        }

        Console.WriteLine("");

        Console.WriteLine("Variables and the annotations that directly refer to them");
        Console.WriteLine("========================================================");
        foreach (var entry in variableDirectlyReferredToByAnnotations) {
          Console.WriteLine(entry.Key + " <- ");
          foreach (var annotation in entry.Value) {
            Console.WriteLine("  " + annotation + ", ");
          }
        }

        Console.WriteLine("");

        Console.WriteLine("Annotation dependence graph");
        Console.WriteLine("==========================");
        foreach (var c in AnnotationDependences.Nodes) {
          Console.WriteLine(c + " <- ");
          foreach (var d in AnnotationDependences.Successors(c)) {
            Console.WriteLine("  " + d);
          }
        }
      }

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

    private bool OnlyRefersToConstants(Expr e) {
      VariableCollector vc = new VariableCollector();
      vc.Visit(e);
      return vc.usedVars.OfType<Constant>().Count() == vc.usedVars.Count();
    }

    private IEnumerable<string> GetNonCandidateAnnotations() {
      var Result = new HashSet<string>();
      int Counter = 0;
      foreach(var Assertion in prog.Blocks().SelectMany(Item => Item.Cmds).
        OfType<AssertCmd>()) {

        string unused;
        if (Houdini.MatchCandidate(Assertion.Expr, CandidateIdentifiers, out unused)) {
          continue;
        }

        if (!QKeyValue.FindBoolAttribute(Assertion.Attributes, "originated_from_invariant")) {
          continue;
        }

        if (OnlyRefersToConstants(Assertion.Expr)) {
          continue;
        }

        string Tag = "staged_houdini_tag_" + Counter;
        Result.Add(Tag);
        Assertion.Attributes = new QKeyValue(Token.NoToken, "staged_houdini_tag", 
          new List<object> { Tag }, Assertion.Attributes);
        Counter++;
      }
      
      foreach(var Req in prog.NonInlinedProcedures().SelectMany(Item => Item.Requires)) {

        string unused;
        if (Houdini.MatchCandidate(Req.Condition, CandidateIdentifiers, out unused)) {
          continue;
        }

        if (OnlyRefersToConstants(Req.Condition)) {
          continue;
        }

        string Tag = "staged_houdini_tag_" + Counter;
        Result.Add(Tag);
        Req.Attributes = new QKeyValue(Token.NoToken, "staged_houdini_tag", 
          new List<object> { Tag }, Req.Attributes);
        Counter++;

      }

      foreach(var Ens in prog.NonInlinedProcedures().SelectMany(Item => Item.Ensures)) {

        string unused;
        if (Houdini.MatchCandidate(Ens.Condition, CandidateIdentifiers, out unused)) {
          continue;
        }

        if (OnlyRefersToConstants(Ens.Condition)) {
          continue;
        }

        string Tag = "staged_houdini_tag_" + Counter;
        Result.Add(Tag);
        Ens.Attributes = new QKeyValue(Token.NoToken, "staged_houdini_tag", 
          new List<object> { Tag }, Ens.Attributes);
        Counter++;

      }

      return Result;
    }

    private IEnumerable<string> GetCandidates() {
      return prog.Variables.Where(Item =>
        QKeyValue.FindBoolAttribute(Item.Attributes, "existential")).Select(Item => Item.Name);
    }


    public StagedHoudiniPlan ApplyStages() {

        if (NoStages())
        {
          Debug.Assert(false);
          var TrivialGraph = new Graph<ScheduledStage>();
          TrivialGraph.AddSource(new ScheduledStage(0, new HashSet<string>()));
          return new StagedHoudiniPlan(TrivialGraph);
        }

        #region Assign annotations to stages at a given level of granularity
      
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

        foreach(var c in AllAnnotationIdentifiers()) {
          Debug.Assert(Plan.StageForAnnotation(c) != null);
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
            prog.AddTopLevelDeclaration(stageActive);
            stageToActiveBoolean[stage.GetId()] = stageActive;

            var stageComplete = new Constant(Token.NoToken, 
                new TypedIdent(Token.NoToken, "_stage_" + stage.GetId() + "_complete", Type.Bool),
                false);
            stageComplete.AddAttribute("stage_complete", new object[] { new LiteralExpr(Token.NoToken, BigNum.FromInt(stage.GetId())) });
            prog.AddTopLevelDeclaration(stageComplete);
            stageToCompleteBoolean[stage.GetId()] = stageComplete;
        }
        #endregion

        #region Adapt annotation assertions to take account of stages
        foreach (var b in prog.Implementations.Select(Item => Item.Blocks).SelectMany(Item => Item))
        {
            List<Cmd> newCmds = new List<Cmd>();
            foreach (var cmd in b.Cmds)
            {
                var a = cmd as AssertCmd;
                string c;
                if (a != null) {
                    if (Houdini.MatchCandidate(a.Expr, CandidateIdentifiers, out c))
                    {
                        newCmds.Add(new AssertCmd(a.tok, Houdini.AddConditionToCandidate(a.Expr,
                            Expr.Ident(stageToActiveBoolean[Plan.StageForAnnotation(c).GetId()]), c), a.Attributes));
                        newCmds.Add(new AssumeCmd(a.tok, Houdini.AddConditionToCandidate(a.Expr,
                            Expr.Ident(stageToCompleteBoolean[Plan.StageForAnnotation(c).GetId()]), c), a.Attributes));
                    } else if (QKeyValue.FindBoolAttribute(a.Attributes, "originated_from_invariant")) {
                        string tag = GetTagFromNonCandidateAttributes(a.Attributes);
                        if (tag == null) {
                          newCmds.Add(a);
                        } else {
                          newCmds.Add(new AssertCmd(a.tok, Expr.Imp(
                              Expr.Ident(stageToActiveBoolean[Plan.StageForAnnotation(tag).GetId()]), a.Expr),
                              a.Attributes));
                          newCmds.Add(new AssumeCmd(a.tok, Expr.Imp(
                              Expr.Ident(stageToCompleteBoolean[Plan.StageForAnnotation(tag).GetId()]), a.Expr),
                              a.Attributes));
                        }
                    }
                }
                else
                {
                    newCmds.Add(cmd);
                }
            }
            b.Cmds = newCmds;
        }
        #endregion

        #region Adapt pre/postconditions to take account of stages
        foreach (var p in prog.NonInlinedProcedures())
        {

          #region Handle the preconditions
          {
            List<Requires> newRequires = new List<Requires>();
            foreach(Requires r in p.Requires) {
              string c;
              if (Houdini.MatchCandidate(r.Condition, CandidateIdentifiers, out c)) {
                newRequires.Add(new Requires(r.tok, false, 
                  Houdini.AddConditionToCandidate(r.Condition,
                  Expr.Ident(stageToActiveBoolean[Plan.StageForAnnotation(c).GetId()]), c),
                  r.Comment, r.Attributes));
                newRequires.Add(new Requires(r.tok, true, 
                  Houdini.AddConditionToCandidate(r.Condition,
                  Expr.Ident(stageToCompleteBoolean[Plan.StageForAnnotation(c).GetId()]), c),
                  r.Comment, r.Attributes));
              } else {
                string tag = GetTagFromNonCandidateAttributes(r.Attributes);
                if (tag == null) {
                  newRequires.Add(r);
                } else {
                  newRequires.Add(new Requires(r.tok, false, 
                    Expr.Imp(Expr.Ident(stageToActiveBoolean[Plan.StageForAnnotation(tag).GetId()]), r.Condition),
                    r.Comment, r.Attributes));
                  newRequires.Add(new Requires(r.tok, true, 
                    Expr.Imp(Expr.Ident(stageToCompleteBoolean[Plan.StageForAnnotation(tag).GetId()]), r.Condition),
                    r.Comment, r.Attributes));
                }
              }
            }
            p.Requires = newRequires;
          }
          #endregion

          #region Handle the postconditions
          {
            List<Ensures> newEnsures = new List<Ensures>();
            foreach(Ensures e in p.Ensures) {
              string c;
              if (Houdini.MatchCandidate(e.Condition, CandidateIdentifiers, out c)) {
                int stage = Plan.StageForAnnotation(c).GetId();
                newEnsures.Add(new Ensures(e.tok, false, 
                  Houdini.AddConditionToCandidate(e.Condition,
                  Expr.Ident(stageToActiveBoolean[stage]), c),
                  e.Comment, e.Attributes));
                newEnsures.Add(new Ensures(e.tok, true, 
                  Houdini.AddConditionToCandidate(e.Condition,
                  Expr.Ident(stageToCompleteBoolean[stage]), c),
                  e.Comment, e.Attributes));
              } else {
                string tag = GetTagFromNonCandidateAttributes(e.Attributes);
                if (tag == null) {
                  newEnsures.Add(e);
                } else {
                  newEnsures.Add(new Ensures(e.tok, false, 
                    Expr.Imp(Expr.Ident(stageToActiveBoolean[Plan.StageForAnnotation(tag).GetId()]), e.Condition),
                    e.Comment, e.Attributes));
                  newEnsures.Add(new Ensures(e.tok, true, 
                    Expr.Imp(Expr.Ident(stageToCompleteBoolean[Plan.StageForAnnotation(tag).GetId()]), e.Condition),
                    e.Comment, e.Attributes));
                }
              }
            }
            p.Ensures = newEnsures;
          }
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
                foreach (var a in n)
                {
                  Stage.AddAnnotation(a);
                }
                AssignedToThisStage.Add(n);
              }
            }

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
              Stage.AddAnnotation(c);
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
          Stage.AddAnnotation(c);
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
        return AllAnnotationIdentifiers().Count() == 0 || StagesDAG.Nodes.Count() == 0;
    }
  }

  interface IAnnotationReachabilityChecker {
    bool MayReach(string c, string d);
  }

  class DummyAnnotationReachabilityChecker : IAnnotationReachabilityChecker {
    public bool MayReach(string c, string d) {
      return true;
    }
  }

  class AnnotationReachabilityChecker : IAnnotationReachabilityChecker {

    private enum PrePost {
      PRE, POST
    }

    private Program prog;
    private IEnumerable<string> AnnotationIdentifiers;
    private IInterproceduralReachabilityGraph reachabilityGraph;
    private Dictionary<string, HashSet<object>> annotationToOccurences;

    internal AnnotationReachabilityChecker(Program prog, IEnumerable<string> AnnotationIdentifiers) {
      this.prog = prog;
      this.AnnotationIdentifiers = AnnotationIdentifiers;
      this.reachabilityGraph = new InterproceduralReachabilityGraph(prog);
      this.annotationToOccurences = new Dictionary<string,HashSet<object>>();

      // Add all annotation occurrences in blocks
      foreach(Block b in prog.Blocks()) {
        foreach(var assertCmd in b.Cmds.OfType<AssertCmd>()) {
          string c;
          if(Houdini.MatchCandidate(assertCmd.Expr, AnnotationIdentifiers, out c)) {
            AddAnnotationOccurrence(c, b);
          } else {
            var tag = AnnotationDependenceAnalyser.GetTagFromNonCandidateAttributes(assertCmd.Attributes);
            if (tag != null) {
              AddAnnotationOccurrence(tag, b);
            }
          }
        }
      }

      // Add all annotation occurrences in pre and post conditions
      foreach(var proc in prog.NonInlinedProcedures()) {
        foreach(Requires r in proc.Requires) {
          string c;
          if(Houdini.MatchCandidate(r.Condition, AnnotationIdentifiers, out c)) {
            AddAnnotationOccurrence(c, new Tuple<string, PrePost>(proc.Name, PrePost.PRE));
          } else {
            string tag = AnnotationDependenceAnalyser.GetTagFromNonCandidateAttributes(r.Attributes);
            if(tag != null) {
              AddAnnotationOccurrence(tag, new Tuple<string, PrePost>(proc.Name, PrePost.PRE));
            }
          }
        }
        foreach(Ensures e in proc.Ensures) {
          string c;
          if(Houdini.MatchCandidate(e.Condition, AnnotationIdentifiers, out c)) {
            AddAnnotationOccurrence(c, new Tuple<string, PrePost>(proc.Name, PrePost.POST));
          } else {
            string tag = AnnotationDependenceAnalyser.GetTagFromNonCandidateAttributes(e.Attributes);
            if(tag != null) {
              AddAnnotationOccurrence(tag, new Tuple<string, PrePost>(proc.Name, PrePost.PRE));
            }
          }
        }
      }
      
    }

    private void AddAnnotationOccurrence(string c, object o) {
      Debug.Assert(o is Block || o is Tuple<string, PrePost>);
      if(!annotationToOccurences.ContainsKey(c)) {
        annotationToOccurences[c] = new HashSet<object>();
      }
      annotationToOccurences[c].Add(o);
    }

    public bool MayReach(string c, string d) {
      foreach(object cOccurrence in annotationToOccurences[c]) {
        foreach(object dOccurrence in annotationToOccurences[d]) {
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

  class AnnotationInstance {
    public string AnnotationIdentifier;
    public string Proc;
    public Expr Expr;

    internal AnnotationInstance(string AnnotationIdentifier, string Proc, Expr Expr) {
      this.AnnotationIdentifier = AnnotationIdentifier;
      this.Proc = Proc;
      this.Expr = Expr;
    }
  }

}
