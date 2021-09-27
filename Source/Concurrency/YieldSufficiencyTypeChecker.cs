using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics;
using System.ComponentModel;

namespace Microsoft.Boogie
{
  public static class YieldSufficiencyTypeChecker
  {
    // Edge labels for the automata that abstract the code of a procedure
    private const string Y = "Y"; // yield
    private const string B = "B"; // both mover action
    private const string L = "L"; // left mover action
    private const string R = "R"; // right mover action
    private const string N = "N"; // non mover action
    private const string P = "P"; // private access (local variable, introduction action, lemma, ...)
    private const string M = "M"; // modification of global variables
    private const string A = "A"; // async call
    
    // States of Atomicity Automaton (check that transactions are separated by yields)
    private const int RM = 0;
    private const int LM = 1;

    // Transitions of Atomicity Automaton
    static List<Tuple<int, string, int>> AtomicitySpec = new List<Tuple<int, string, int>>
    {
      // initial: {RM, LM}, final: {RM, LM}
      Tuple.Create(RM, P, RM),
      Tuple.Create(RM, B, RM),
      Tuple.Create(RM, R, RM),
      Tuple.Create(RM, Y, RM),
      Tuple.Create(RM, L, LM),
      Tuple.Create(RM, N, LM),
      Tuple.Create(LM, P, LM),
      Tuple.Create(LM, B, LM),
      Tuple.Create(LM, L, LM),
      Tuple.Create(LM, Y, RM),
    };

    // States of Async Automaton (check that there is no global update between async and next yield)
    private const int BEFORE = 0;
    private const int AFTER = 1;

    // Transitions of Async Automaton
    static List<Tuple<int, string, int>> AsyncSpec = new List<Tuple<int, string, int>>
    {
      Tuple.Create(BEFORE, P, BEFORE),
      Tuple.Create(BEFORE, M, BEFORE),
      Tuple.Create(BEFORE, Y, BEFORE),
      Tuple.Create(BEFORE, A, AFTER),
      Tuple.Create(AFTER, P, AFTER),
      Tuple.Create(AFTER, A, AFTER),
      Tuple.Create(AFTER, Y, BEFORE),
    };

    private static string MoverTypeToLabel(MoverType moverType)
    {
      switch (moverType)
      {
        case MoverType.Non:
          return N;
        case MoverType.Both:
          return B;
        case MoverType.Left:
          return L;
        case MoverType.Right:
          return R;
        default:
          throw new InvalidEnumArgumentException();
      }
    }

    public static void TypeCheck(CivlTypeChecker civlTypeChecker)
    {
      // Mover procedures can only call other mover procedures on the same layer.
      // Thus, the constructed call graph naturally forms disconnected components
      // w.r.t. layers and we can keep a single graph instead of one for each layer.
      var moverProcedureCallGraph = ConstructMoverProcedureCallGraph(civlTypeChecker);

      foreach (var impl in civlTypeChecker.program.Implementations.Where(impl =>
        civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc)))
      {
        var yieldingProc = civlTypeChecker.procToYieldingProc[impl.Proc];

        impl.PruneUnreachableBlocks();
        Graph<Block> implGraph = Program.GraphFromImpl(impl);
        implGraph.ComputeLoops();

        foreach (int layerNum in civlTypeChecker.allRefinementLayers.Where(l => l <= yieldingProc.upperLayer))
        {
          new PerLayerYieldSufficiencyTypeChecker(civlTypeChecker, yieldingProc, impl, layerNum, implGraph, moverProcedureCallGraph)
            .TypeCheckLayer();
        }
      }
    }

    private static Graph<MoverProc> ConstructMoverProcedureCallGraph(CivlTypeChecker civlTypeChecker)
    {
      var moverProcedureCallGraph = new Graph<MoverProc>();
      
      foreach (var impl in civlTypeChecker.program.Implementations.Where(impl =>
        civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc)))
      {
        MoverProc callerProc = civlTypeChecker.procToYieldingProc[impl.Proc] as MoverProc;
        if (callerProc == null)
        {
          continue;
        }

        foreach (var callCmd in impl.Blocks.SelectMany(b => b.Cmds).OfType<CallCmd>())
        {
          if (civlTypeChecker.procToYieldingProc.ContainsKey(callCmd.Proc))
          {
            MoverProc calleeProc = civlTypeChecker.procToYieldingProc[callCmd.Proc] as MoverProc;
            if (calleeProc == null)
            {
              continue;
            }

            Debug.Assert(callerProc.upperLayer == calleeProc.upperLayer);
            moverProcedureCallGraph.AddEdge(callerProc, calleeProc);
          }
        }
      }

      return moverProcedureCallGraph;
    }

    private class PerLayerYieldSufficiencyTypeChecker
    {
      private CivlTypeChecker civlTypeChecker;
      private YieldingProc yieldingProc;
      private Implementation impl;
      private int currLayerNum;
      private Graph<Block> implGraph;
      private Graph<MoverProc> moverProcedureCallGraph;

      private Dictionary<Tuple<Absy, Absy>, string> atomicityLabels;
      private Dictionary<Tuple<Absy, Absy>, string> asyncLabels;
      private Absy initialState;
      private HashSet<Absy> finalStates;

      public PerLayerYieldSufficiencyTypeChecker(CivlTypeChecker civlTypeChecker, YieldingProc yieldingProc,
        Implementation impl, int currLayerNum, Graph<Block> implGraph, Graph<MoverProc> moverProcedureCallGraph)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.yieldingProc = yieldingProc;
        this.impl = impl;
        this.currLayerNum = currLayerNum;
        this.implGraph = implGraph;
        this.moverProcedureCallGraph = moverProcedureCallGraph;
      }

      public void TypeCheckLayer()
      {
        ComputeGraph();
        LoopCheck();
        AtomicityCheck();
        AsyncCheck();
      }

      private void LoopCheck()
      {
        var graph = new Graph<Absy>(new HashSet<Tuple<Absy,Absy>>(atomicityLabels.Keys));
        graph.AddSource(initialState);
        graph.ComputeLoops();

        var edgeToLoopHeader = new Dictionary<Tuple<Absy, Absy>, Block>();
        foreach (Block header in graph.SortHeadersByDominance())
        {
          foreach (var source in graph.BackEdgeNodes(header))
          {
            edgeToLoopHeader[new Tuple<Absy, Absy>(source, header)] = header;
            foreach (var node in graph.NaturalLoops(header, source))
            {
              if (node == header)
              {
                continue;
              }

              foreach (var pred in graph.Predecessors(node))
              {
                var edge = new Tuple<Absy, Absy>(pred, node);
                if (edgeToLoopHeader.ContainsKey(edge))
                {
                  continue;
                }

                edgeToLoopHeader[edge] = header;
              }
            }
          }
        }

        var parentLoopHeader = new Dictionary<Block, Block>();
        foreach (Block header in graph.Headers)
        {
          foreach (var pred in graph.Predecessors(header).Except(graph.BackEdgeNodes(header)))
          {
            var edge = new Tuple<Absy, Absy>(pred, header);
            if (edgeToLoopHeader.ContainsKey(edge))
            {
              parentLoopHeader[header] = edgeToLoopHeader[edge];
              break;
            }
          }
        }

        var yieldingLoopHeaders = new HashSet<Block>(graph.Headers.OfType<Block>()
          .Where(header => civlTypeChecker.IsYieldingLoopHeader(header, currLayerNum)));
        foreach (var header in parentLoopHeader.Keys)
        {
          var parentHeader = parentLoopHeader[header];
          if (yieldingLoopHeaders.Contains(header) && !yieldingLoopHeaders.Contains(parentHeader))
          {
            civlTypeChecker.Error(parentHeader,
              $"Loop header must be yielding at layer {currLayerNum}");
          }
        }

        foreach (var edge in edgeToLoopHeader.Keys)
        {
          var header = edgeToLoopHeader[edge];
          if (yieldingLoopHeaders.Contains(header))
          {
            continue;
          }

          if (atomicityLabels[edge] == Y)
          {
            civlTypeChecker.Error(header,
              $"Loop header must be yielding at layer {currLayerNum}");
          }
        }
      }

      private void AsyncCheck()
      {
        var simulationRelation =
          new SimulationRelation<Absy, int, string>(LabelsToLabeledEdges(asyncLabels), AsyncSpec, new Dictionary<Absy, HashSet<int>>())
            .ComputeSimulationRelation();

        if (simulationRelation[initialState].Count == 0)
        {
          civlTypeChecker.Error(impl,
            $"Implementation {impl.Name} fails async check at layer {currLayerNum}.");
        }
      }

      private void AtomicityCheck()
      {
        var initialConstraints = new Dictionary<Absy, HashSet<int>>();

        foreach (Block header in implGraph.Headers)
        {
          if (civlTypeChecker.IsYieldingLoopHeader(header, currLayerNum) ||
              civlTypeChecker.IsCooperatingLoopHeader(header, currLayerNum))
          {
            continue;
          }

          initialConstraints[header] = new HashSet<int> {RM};
        }

        if (IsMoverProcedure)
        {
          foreach (var call in impl.Blocks.SelectMany(b => b.cmds).OfType<CallCmd>())
          {
            if (!IsCooperatingCall(call))
            {
              initialConstraints[call] = new HashSet<int> {RM};
            }
          }
        }

        var simulationRelation =
          new SimulationRelation<Absy, int, string>(LabelsToLabeledEdges(atomicityLabels), AtomicitySpec, initialConstraints)
            .ComputeSimulationRelation();

        if (IsMoverProcedure)
        {
          if (!CheckAtomicity(simulationRelation))
          {
            civlTypeChecker.Error(impl, "The atomicity declared for mover procedure is not valid");
          }
        }
        else if (simulationRelation[initialState].Count == 0)
        {
          civlTypeChecker.Error(impl,
            $"Implementation {impl.Name} fails atomicity check at layer {currLayerNum}. Transactions must be separated by yields.");
        }
      }

      private bool IsMoverProcedure
      {
        get { return yieldingProc is MoverProc && yieldingProc.upperLayer == currLayerNum; }
      }

      private bool IsCooperatingCall(CallCmd call)
      {
        return !IsRecursiveMoverProcedureCall(call) || civlTypeChecker.IsCooperatingProcedure(call.Proc);
      }

      private bool CheckAtomicity(Dictionary<Absy, HashSet<int>> simulationRelation)
      {
        if (yieldingProc.moverType == MoverType.Non && simulationRelation[initialState].Count == 0)
        {
          return false;
        }

        if (yieldingProc.IsRightMover && (!simulationRelation[initialState].Contains(RM) ||
                                          finalStates.Any(f => !simulationRelation[f].Contains(RM))))
        {
          return false;
        }

        if (yieldingProc.IsLeftMover && !simulationRelation[initialState].Contains(LM))
        {
          return false;
        }

        return true;
      }

      private bool IsRecursiveMoverProcedureCall(CallCmd call)
      {
        MoverProc source = null;
        if (civlTypeChecker.procToYieldingProc.ContainsKey(call.Proc))
        {
          source = civlTypeChecker.procToYieldingProc[call.Proc] as MoverProc;
        }

        if (source == null)
        {
          return false;
        }

        MoverProc target = (MoverProc) yieldingProc;

        HashSet<MoverProc> frontier = new HashSet<MoverProc> {source};
        HashSet<MoverProc> visited = new HashSet<MoverProc>();

        while (frontier.Count > 0)
        {
          var curr = frontier.First();
          frontier.Remove(curr);
          visited.Add(curr);

          if (curr == target)
          {
            return true;
          }

          frontier.UnionWith(moverProcedureCallGraph.Successors(curr).Except(visited));
        }

        return false;
      }

      private void ComputeGraph()
      {
        atomicityLabels = new Dictionary<Tuple<Absy, Absy>, string>();
        asyncLabels = new Dictionary<Tuple<Absy, Absy>, string>();
        initialState = impl.Blocks[0];
        finalStates = new HashSet<Absy>();

        foreach (Block block in impl.Blocks)
        {
          // Block entry edge
          Absy blockEntry = block.Cmds.Count == 0 ? (Absy) block.TransferCmd : (Absy) block.Cmds[0];
          var entryEdge = new Tuple<Absy, Absy>(block, blockEntry);
          var entryLabel = civlTypeChecker.IsYieldingLoopHeader(block, currLayerNum) ? Y : P;
          atomicityLabels[entryEdge] = entryLabel;
          asyncLabels[entryEdge] = entryLabel;

          // Block exit edges
          if (block.TransferCmd is GotoCmd gotoCmd)
          {
            foreach (Block successor in gotoCmd.labelTargets)
            {
              var edge = new Tuple<Absy, Absy>(block.TransferCmd, successor);
              atomicityLabels[edge] = P;
              asyncLabels[edge] = P;
            }
          }
          else if (block.TransferCmd is ReturnCmd)
          {
            finalStates.Add(block.TransferCmd);
          }

          // Block internal edges
          for (int i = 0; i < block.Cmds.Count; i++)
          {
            Cmd cmd = block.Cmds[i];
            Absy next = (i + 1 == block.Cmds.Count) ? (Absy) block.TransferCmd : block.Cmds[i + 1];
            var edge = new Tuple<Absy, Absy>(cmd, next);

            if (cmd is CallCmd callCmd)
            {
              atomicityLabels[edge] = CallCmdLabel(callCmd);
              asyncLabels[edge] = CallCmdLabelAsync(callCmd);
            }
            else if (cmd is ParCallCmd parCallCmd)
            {
              CheckParCallCmd(parCallCmd);
              AddParCallCmdLabels(atomicityLabels, parCallCmd, next);
              AddParCallCmdLabelsAsync(asyncLabels, parCallCmd, next);
            }
            else if (cmd is YieldCmd)
            {
              atomicityLabels[edge] = Y;
              asyncLabels[edge] = Y;
            }
            else
            {
              atomicityLabels[edge] = P;
              asyncLabels[edge] = P;
            }
          }
        }
      }

      private static List<Tuple<Absy, string, Absy>> LabelsToLabeledEdges(Dictionary<Tuple<Absy, Absy>, string> labels)
      {
        var edges = new List<Tuple<Absy, string, Absy>>();
        foreach (Tuple<Absy, Absy> e in labels.Keys)
        {
          edges.Add(new Tuple<Absy, string, Absy>(e.Item1, labels[e], e.Item2));
        }
        return edges;
      }

      private string CallCmdLabel(CallCmd callCmd)
      {
        if (civlTypeChecker.procToIntroductionAction.ContainsKey(callCmd.Proc) ||
            civlTypeChecker.procToLemmaProc.ContainsKey(callCmd.Proc))
        {
          return P;
        }

        if (civlTypeChecker.procToYieldInvariant.ContainsKey(callCmd.Proc))
        {
          return civlTypeChecker.procToYieldInvariant[callCmd.Proc].LayerNum == currLayerNum ? Y : P;
        }

        YieldingProc callee = civlTypeChecker.procToYieldingProc[callCmd.Proc];
        if (callCmd.IsAsync)
        {
          if (callee is MoverProc && callee.upperLayer == currLayerNum)
          {
            return MoverTypeToLabel(callee.moverType);
          }

          if (callee is ActionProc actionProc && callee.upperLayer < currLayerNum && callCmd.HasAttribute(CivlAttributes.SYNC))
          {
            return MoverTypeToLabel(actionProc.RefinedActionAtLayer(currLayerNum).moverType);
          }

          return L;
        }
        else
        {
          if (callee is MoverProc && callee.upperLayer == currLayerNum)
          {
            return MoverTypeToLabel(callee.moverType);
          }

          if (callee is ActionProc actionProc && callee.upperLayer < currLayerNum)
          {
            return MoverTypeToLabel(actionProc.RefinedActionAtLayer(currLayerNum).moverType);
          }

          return Y;
        }
      }

      private void AddParCallCmdLabels(Dictionary<Tuple<Absy, Absy>, string> edgeLabels, ParCallCmd parCallCmd,
        Absy next)
      {
        edgeLabels[new Tuple<Absy, Absy>(parCallCmd, parCallCmd.CallCmds[0])] = P;
        for (int i = 0; i < parCallCmd.CallCmds.Count; i++)
        {
          var callCmd = parCallCmd.CallCmds[i];
          var edge = new Tuple<Absy, Absy>(callCmd,
            i + 1 < parCallCmd.CallCmds.Count ? parCallCmd.CallCmds[i + 1] : next);
          var label = CallCmdLabel(callCmd);
          edgeLabels[edge] = label;
        }
      }

      public static string ModifiesGlobalLabel<T>(IEnumerable<T> modifiedGlobalVars)
      {
        if (modifiedGlobalVars.Any())
        {
          return M;
        }
        else
        {
          return P;
        }
      }

      private string CallCmdLabelAsync(CallCmd callCmd)
      {
        if (civlTypeChecker.procToIntroductionAction.ContainsKey(callCmd.Proc) ||
            civlTypeChecker.procToLemmaProc.ContainsKey(callCmd.Proc))
        {
          return P;
        }

        if (civlTypeChecker.procToYieldInvariant.ContainsKey(callCmd.Proc))
        {
          return civlTypeChecker.procToYieldInvariant[callCmd.Proc].LayerNum == currLayerNum ? Y : P;
        }

        YieldingProc callee = civlTypeChecker.procToYieldingProc[callCmd.Proc];
        if (callCmd.IsAsync)
        {
          if (callee is MoverProc && callee.upperLayer == currLayerNum)
          {
            return ModifiesGlobalLabel(callee.proc.Modifies);
          }

          if (callee is ActionProc actionProc && callee.upperLayer < currLayerNum)
          {
            if (callCmd.HasAttribute(CivlAttributes.SYNC))
            {
              return ModifiesGlobalLabel(actionProc.RefinedActionAtLayer(currLayerNum).modifiedGlobalVars);
            }
            else
            {
              return P;
            }
          }

          return A;
        }
        else
        {
          if (callee is MoverProc && callee.upperLayer == currLayerNum)
          {
            return ModifiesGlobalLabel(callee.proc.Modifies);
          }

          if (callee is ActionProc actionProc && callee.upperLayer < currLayerNum)
          {
            return ModifiesGlobalLabel(actionProc.RefinedActionAtLayer(currLayerNum).modifiedGlobalVars);
          }

          return Y;
        }
      }

      private void AddParCallCmdLabelsAsync(Dictionary<Tuple<Absy, Absy>, string> edgeLabels, ParCallCmd parCallCmd,
        Absy next)
      {
        edgeLabels[new Tuple<Absy, Absy>(parCallCmd, parCallCmd.CallCmds[0])] = P;
        for (int i = 0; i < parCallCmd.CallCmds.Count; i++)
        {
          var callCmd = parCallCmd.CallCmds[i];
          var edge = new Tuple<Absy, Absy>(callCmd,
            i + 1 < parCallCmd.CallCmds.Count ? parCallCmd.CallCmds[i + 1] : next);
          var label = CallCmdLabelAsync(callCmd);
          edgeLabels[edge] = label;
        }
      }

      private void CheckParCallCmd(ParCallCmd parCallCmd)
      {
        CheckNonMoverCondition(parCallCmd);
        if (parCallCmd.CallCmds.Any(callCmd => CallCmdLabel(callCmd) == Y &&
                                               !civlTypeChecker.procToYieldInvariant.ContainsKey(
                                                 callCmd.Proc)))
        {
          if (parCallCmd.CallCmds.Any(callCmd => CallCmdLabel(callCmd) == N))
          {
            civlTypeChecker.Error(parCallCmd,
              $"Parallel call contains both non-mover and yielding procedure at layer {currLayerNum}");
          }
          else
          {
            CheckYieldingProcCondition(parCallCmd);
          }
        }
      }

      private enum ParallelCallPhase
      {
        BEFORE,
        MIDDLE,
        AFTER,
      }

      // Check pattern (left)*(non)?(right)*
      private void CheckNonMoverCondition(ParCallCmd parCallCmd)
      {
        ParallelCallPhase phase = ParallelCallPhase.BEFORE;
        foreach (var callCmd in parCallCmd.CallCmds)
        {
          var label = CallCmdLabel(callCmd);
          if (label == P || label == Y || label == B)
          {
            continue;
          }

          switch (phase)
          {
            case ParallelCallPhase.BEFORE:
              if (label == L)
              {
                continue;
              }

              phase = ParallelCallPhase.AFTER;
              break;
            case ParallelCallPhase.MIDDLE:
              Debug.Assert(false);
              break;
            case ParallelCallPhase.AFTER:
              if (label == R)
              {
                continue;
              }

              civlTypeChecker.Error(parCallCmd,
                $"Mover types in parallel call do not match (left)*(non)?(right)* at layer {currLayerNum}");
              break;
          }
        }
      }

      // Check pattern (left)*(yielding-proc)*(right)*
      private void CheckYieldingProcCondition(ParCallCmd parCallCmd)
      {
        ParallelCallPhase phase = ParallelCallPhase.BEFORE;
        foreach (var callCmd in parCallCmd.CallCmds)
        {
          var label = CallCmdLabel(callCmd);
          Debug.Assert(label != N);
          if (label == P || label == Y && civlTypeChecker.procToYieldInvariant.ContainsKey(callCmd.Proc)
          )
          {
            continue;
          }

          switch (phase)
          {
            case ParallelCallPhase.BEFORE:
              if (label == Y)
              {
                phase = ParallelCallPhase.MIDDLE;
              }
              else if (label == R)
              {
                phase = ParallelCallPhase.AFTER;
              }

              break;
            case ParallelCallPhase.MIDDLE:
              if (label == Y)
              {
                continue;
              }

              if (label == L)
              {
                civlTypeChecker.Error(parCallCmd,
                  $"Mover types in parallel call do not match (left)*(yielding-proc)*(right)* at layer {currLayerNum}");
              }
              else
              {
                phase = ParallelCallPhase.AFTER;
              }

              break;
            case ParallelCallPhase.AFTER:
              if (label == R || label == B)
              {
                continue;
              }

              civlTypeChecker.Error(parCallCmd,
                $"Mover types in parallel call do not match (left)*(yielding-proc)*(right)* at layer {currLayerNum}");
              break;
          }
        }
      }

      private static string PrintGraph(Implementation impl, List<Tuple<Absy, string, Absy>> edges, Absy initialState,
        HashSet<Absy> finalStates)
      {
        Dictionary<Absy, int> map = new Dictionary<Absy, int>();
        int cnt = 0;
        foreach (var e in edges)
        {
          if (!map.ContainsKey(e.Item1))
          {
            map[e.Item1] = cnt++;
          }

          if (!map.ContainsKey(e.Item3))
          {
            map[e.Item3] = cnt++;
          }
        }

        var s = new StringBuilder();
        s.AppendLine("\nImplementation " + impl.Proc.Name + " digraph G {");
        foreach (var e in edges)
        {
          s.AppendLine("  \"" + map[e.Item1] + "\" -- " + e.Item2 + " --> \"" + map[e.Item3] + "\";");
        }

        s.AppendLine("}");
        s.AppendLine("Initial state: " + map[initialState]);
        s.Append("Final states: ");
        bool first = true;
        foreach (var finalState in finalStates)
        {
          s.Append((first ? "" : ", ") + map[finalState]);
          first = false;
        }

        s.AppendLine();
        return s.ToString();
      }
    }
  }
}
