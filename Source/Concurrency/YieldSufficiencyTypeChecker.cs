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
    // Edge labels of the automaton that abstracts the code of a procedure
    private const string Y = "Y"; // yield
    private const string B = "B"; // both mover action
    private const string L = "L"; // left mover action
    private const string R = "R"; // right mover action
    private const string A = "A"; // atomic (non mover) action
    private const string P = "P"; // private (local variable) access
    private const string I = "I"; // introduction action

    // States of Atomicity Automaton (check that transactions are separated by yields)
    private const int RM = 0;
    private const int LM = 1;

    // Transitions of Atomicity Automaton
    static List<Tuple<int, string, int>> AtomicitySpec = new List<Tuple<int, string, int>>
    {
      // initial: {RM, LM}, final: {RM, LM}
      new Tuple<int, string, int>(RM, P, RM),
      new Tuple<int, string, int>(RM, I, RM),
      new Tuple<int, string, int>(RM, B, RM),
      new Tuple<int, string, int>(RM, R, RM),
      new Tuple<int, string, int>(RM, Y, RM),
      new Tuple<int, string, int>(RM, L, LM),
      new Tuple<int, string, int>(RM, A, LM),
      new Tuple<int, string, int>(LM, P, LM),
      new Tuple<int, string, int>(LM, I, LM),
      new Tuple<int, string, int>(LM, B, LM),
      new Tuple<int, string, int>(LM, L, LM),
      new Tuple<int, string, int>(LM, Y, RM),
    };

    private static string MoverTypeToLabel(MoverType moverType)
    {
      switch (moverType)
      {
        case MoverType.Atomic:
          return A;
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
        if (callerProc == null) continue;

        foreach (var callCmd in impl.Blocks.SelectMany(b => b.Cmds).OfType<CallCmd>())
        {
          if (civlTypeChecker.procToYieldingProc.ContainsKey(callCmd.Proc))
          {
            MoverProc calleeProc = civlTypeChecker.procToYieldingProc[callCmd.Proc] as MoverProc;
            if (calleeProc == null) continue;

            Debug.Assert(callerProc.upperLayer == calleeProc.upperLayer);
            moverProcedureCallGraph.AddEdge(callerProc, calleeProc);
          }
        }
      }

      return moverProcedureCallGraph;
    }

    private class PerLayerYieldSufficiencyTypeChecker
    {
      CivlTypeChecker civlTypeChecker;
      YieldingProc yieldingProc;
      Implementation impl;
      int currLayerNum;
      Graph<Block> implGraph;
      private Graph<MoverProc> moverProcedureCallGraph;
      List<Tuple<Absy, string, Absy>> implEdges;
      Absy initialState;
      HashSet<Absy> finalStates;

      public PerLayerYieldSufficiencyTypeChecker(CivlTypeChecker civlTypeChecker, YieldingProc yieldingProc,
        Implementation impl, int currLayerNum, Graph<Block> implGraph, Graph<MoverProc> moverProcedureCallGraph)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.yieldingProc = yieldingProc;
        this.impl = impl;
        this.currLayerNum = currLayerNum;
        this.implGraph = implGraph;
        this.moverProcedureCallGraph = moverProcedureCallGraph;
        this.initialState = impl.Blocks[0];
        this.finalStates = new HashSet<Absy>();
        this.implEdges = new List<Tuple<Absy, string, Absy>>();
      }

      public void TypeCheckLayer()
      {
        ComputeGraph();
        LoopCheck();
        AtomicityCheck();
      }

      private void LoopCheck()
      {
        var edgeLabel = new Dictionary<Tuple<Absy, Absy>, string>();
        var graph = new Graph<Absy>();
        graph.AddSource(impl.Blocks[0]);
        implEdges.ForEach(e =>
        {
          graph.AddEdge(e.Item1, e.Item3);
          edgeLabel[new Tuple<Absy, Absy>(e.Item1, e.Item3)] = e.Item2;
        });
        graph.ComputeLoops();
        var edgeToLoopHeader = new Dictionary<Tuple<Absy, Absy>, Block>();
        foreach (Block header in graph.SortHeadersByDominance())
        {
          foreach (var source in graph.BackEdgeNodes(header))
          {
            edgeToLoopHeader[new Tuple<Absy, Absy>(source, header)] = header;
            foreach (var node in graph.NaturalLoops(header, source))
            {
              if (node == header) continue;
              foreach (var pred in graph.Predecessors(node))
              {
                var edge = new Tuple<Absy, Absy>(pred, node);
                if (edgeToLoopHeader.ContainsKey(edge)) continue;
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
          if (yieldingLoopHeaders.Contains(header)) continue;
          if (edgeLabel[edge] == Y)
          {
            civlTypeChecker.Error(header,
              $"Loop header must be yielding at layer {currLayerNum}");
          }
        }
      }

      private void AtomicityCheck()
      {
        var initialConstraints = new Dictionary<Absy, HashSet<int>>();

        foreach (Block header in implGraph.Headers)
        {
          if (civlTypeChecker.IsYieldingLoopHeader(header, currLayerNum) ||
              civlTypeChecker.IsTerminatingLoopHeader(header, currLayerNum)) continue;
          initialConstraints[header] = new HashSet<int> {RM};
        }

        if (IsMoverProcedure)
        {
          foreach (var call in impl.Blocks.SelectMany(b => b.cmds).OfType<CallCmd>())
          {
            if (!IsTerminatingCall(call))
            {
              initialConstraints[call] = new HashSet<int> {RM};
            }
          }
        }

        var simulationRelation =
          new SimulationRelation<Absy, int, string>(implEdges, AtomicitySpec, initialConstraints)
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

      private bool IsTerminatingCall(CallCmd call)
      {
        return !IsRecursiveMoverProcedureCall(call) || civlTypeChecker.IsTerminatingProcedure(call.Proc);
      }

      private bool CheckAtomicity(Dictionary<Absy, HashSet<int>> simulationRelation)
      {
        if (yieldingProc.moverType == MoverType.Atomic && simulationRelation[initialState].Count == 0)
          return false;
        if (yieldingProc.IsRightMover && (!simulationRelation[initialState].Contains(RM) ||
                                          finalStates.Any(f => !simulationRelation[f].Contains(RM))))
          return false;
        if (yieldingProc.IsLeftMover && !simulationRelation[initialState].Contains(LM)) return false;
        return true;
      }

      private bool IsRecursiveMoverProcedureCall(CallCmd call)
      {
        MoverProc source = null;
        if (civlTypeChecker.procToYieldingProc.ContainsKey(call.Proc))
          source = civlTypeChecker.procToYieldingProc[call.Proc] as MoverProc;
        if (source == null)
          return false;

        MoverProc target = (MoverProc) yieldingProc;

        HashSet<MoverProc> frontier = new HashSet<MoverProc> {source};
        HashSet<MoverProc> visited = new HashSet<MoverProc>();

        while (frontier.Count > 0)
        {
          var curr = frontier.First();
          frontier.Remove(curr);
          visited.Add(curr);

          if (curr == target)
            return true;
          frontier.UnionWith(moverProcedureCallGraph.Successors(curr).Except(visited));
        }

        return false;
      }

      private void ComputeGraph()
      {
        // Internal representation
        // At the end of the method, we translate to List<Tuple<Absy, int, Absy>>
        Dictionary<Tuple<Absy, Absy>, string> edgeLabels = new Dictionary<Tuple<Absy, Absy>, string>();

        foreach (Block block in impl.Blocks)
        {
          // Block entry edge
          Absy blockEntry = block.Cmds.Count == 0 ? (Absy) block.TransferCmd : (Absy) block.Cmds[0];
          edgeLabels[new Tuple<Absy, Absy>(block, blockEntry)] =
            civlTypeChecker.IsYieldingLoopHeader(block, currLayerNum) ? Y : P;

          // Block exit edges
          if (block.TransferCmd is GotoCmd gotoCmd)
          {
            foreach (Block successor in gotoCmd.labelTargets)
            {
              edgeLabels[new Tuple<Absy, Absy>(block.TransferCmd, successor)] = P;
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
            Tuple<Absy, Absy> edge = new Tuple<Absy, Absy>(cmd, next);
            if (cmd is CallCmd callCmd)
            {
              edgeLabels[edge] = CallCmdLabel(callCmd);
            }
            else if (cmd is ParCallCmd parCallCmd)
            {
              AddParCallCmdLabels(edgeLabels, parCallCmd, next);
            }
            else if (cmd is YieldCmd)
            {
              edgeLabels[edge] = Y;
            }
            else
            {
              edgeLabels[edge] = P;
            }
          }
        }

        foreach (Tuple<Absy, Absy> e in edgeLabels.Keys)
        {
          implEdges.Add(new Tuple<Absy, string, Absy>(e.Item1, edgeLabels[e], e.Item2));
        }
      }

      private string CallCmdLabel(CallCmd callCmd)
      {
        if (civlTypeChecker.procToIntroductionAction.ContainsKey(callCmd.Proc) ||
            civlTypeChecker.procToLemmaProc.ContainsKey(callCmd.Proc))
        {
          return I;
        }

        if (civlTypeChecker.procToYieldInvariant.ContainsKey(callCmd.Proc))
        {
          return civlTypeChecker.procToYieldInvariant[callCmd.Proc].LayerNum == currLayerNum ? Y : P;
        }

        YieldingProc callee = civlTypeChecker.procToYieldingProc[callCmd.Proc];
        if (callCmd.IsAsync)
        {
          return L;
        }

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
          Debug.Assert(label != I);
          if (label == P || label == Y || label == B) continue;
          switch (phase)
          {
            case ParallelCallPhase.BEFORE:
              if (label == L) continue;
              phase = ParallelCallPhase.AFTER;
              break;
            case ParallelCallPhase.MIDDLE:
              Debug.Assert(false);
              break;
            case ParallelCallPhase.AFTER:
              if (label == R) continue;
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
          Debug.Assert(label != I && label != A);
          if (label == P || label == Y && civlTypeChecker.procToYieldInvariant.ContainsKey(callCmd.Proc)
          ) continue;
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
              if (label == Y) continue;
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
              if (label == R || label == B) continue;
              civlTypeChecker.Error(parCallCmd,
                $"Mover types in parallel call do not match (left)*(yielding-proc)*(right)* at layer {currLayerNum}");
              break;
          }
        }
      }

      private void AddParCallCmdLabels(Dictionary<Tuple<Absy, Absy>, string> edgeLabels, ParCallCmd parCallCmd,
        Absy next)
      {
        CheckNonMoverCondition(parCallCmd);
        if (parCallCmd.CallCmds.Any(callCmd => CallCmdLabel(callCmd) == Y &&
                                               !civlTypeChecker.procToYieldInvariant.ContainsKey(
                                                 callCmd.Proc)))
        {
          if (parCallCmd.CallCmds.Any(callCmd => CallCmdLabel(callCmd) == A))
          {
            civlTypeChecker.Error(parCallCmd,
              $"Parallel call contains both non-mover and yielding procedure at layer {currLayerNum}");
          }
          else
          {
            CheckYieldingProcCondition(parCallCmd);
          }
        }

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

      private static string PrintGraph(Implementation impl, List<Tuple<Absy, string, Absy>> edges, Absy initialState,
        HashSet<Absy> finalStates)
      {
        Dictionary<Absy, int> map = new Dictionary<Absy, int>();
        int cnt = 0;
        foreach (var e in edges)
        {
          if (!map.ContainsKey(e.Item1)) map[e.Item1] = cnt++;
          if (!map.ContainsKey(e.Item3)) map[e.Item3] = cnt++;
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