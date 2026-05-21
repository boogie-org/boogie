using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics;
using System.ComponentModel;

namespace Microsoft.Boogie
{
  public static class YieldSufficiencyChecker
  {
    // Edge labels for the automata that abstract the code of a procedure
    private const string Y = "Y"; // yield
    private const string B = "B"; // both mover action
    private const string L = "L"; // left mover action
    private const string R = "R"; // right mover action
    private const string N = "N"; // non mover action
    private const string P = "P"; // private access (local variable, pure action, pure procedure, ...)
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
        case MoverType.Atomic:
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
      foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl))
      {
        var yieldingProc = (YieldProcedureDecl)impl.Proc;
        impl.PruneUnreachableBlocks(civlTypeChecker.Options);
        foreach (int layerNum in civlTypeChecker.AllRefinementLayers.Where(l => l <= yieldingProc.Layer))
        {
          new PerLayerYieldSufficiencyTypeChecker(civlTypeChecker, yieldingProc, impl, layerNum).TypeCheckLayer();
        }
      }
    }

    private class PerLayerYieldSufficiencyTypeChecker
    {
      private CivlTypeChecker civlTypeChecker;
      private YieldProcedureDecl yieldingProc;
      private Implementation impl;
      private int currLayerNum;

      private Dictionary<Tuple<Absy, Absy>, string> atomicityLabels;
      private Dictionary<Tuple<Absy, Absy>, string> asyncLabels;
      private Absy initialState;
      private HashSet<Absy> finalStates;
      
      public PerLayerYieldSufficiencyTypeChecker(CivlTypeChecker civlTypeChecker, YieldProcedureDecl yieldingProc,
        Implementation impl, int currLayerNum)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.yieldingProc = yieldingProc;
        this.impl = impl;
        this.currLayerNum = currLayerNum;
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
          .Where(header => yieldingProc.IsYieldingLoopHeader(header, currLayerNum)));
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

      private bool IsMoverProcedure => yieldingProc.MoverType.HasValue && yieldingProc.Layer == currLayerNum;

      private bool CheckAtomicity(Dictionary<Absy, HashSet<int>> simulationRelation)
      {
        if (yieldingProc.MoverType == MoverType.Atomic && simulationRelation[initialState].Count == 0)
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
          var entryLabel = yieldingProc.IsYieldingLoopHeader(block, currLayerNum) ? Y : P;
          atomicityLabels[entryEdge] = entryLabel;
          asyncLabels[entryEdge] = entryLabel;

          // Block exit edges
          if (block.TransferCmd is GotoCmd gotoCmd)
          {
            foreach (Block successor in gotoCmd.LabelTargets)
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
        if (callCmd.Proc.IsPure)
        {
          return P;
        }

        if (callCmd.Proc is YieldInvariantDecl yieldInvariant)
        {
          return yieldInvariant.Layer == currLayerNum ? Y : P;
        }

        var callee = (YieldProcedureDecl)callCmd.Proc;
        if (callCmd.IsAsync)
        {
          if (callee.MoverType.HasValue && callee.Layer == currLayerNum)
          {
            return MoverTypeToLabel(callee.MoverType.Value);
          }

          if (!callee.MoverType.HasValue && callee.Layer < currLayerNum && callCmd.HasAttribute(CivlAttributes.SYNC))
          {
            return MoverTypeToLabel(callee.RefinedActionAtLayer(currLayerNum).MoverType);
          }

          return L;
        }
        else
        {
          if (callee.MoverType.HasValue && callee.Layer == currLayerNum)
          {
            return MoverTypeToLabel(callee.MoverType.Value);
          }

          if (!callee.MoverType.HasValue && callee.Layer < currLayerNum)
          {
            return MoverTypeToLabel(callee.RefinedActionAtLayer(currLayerNum).MoverType);
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
        if (callCmd.Proc.IsPure)
        {
          return P;
        }

        if (callCmd.Proc is YieldInvariantDecl yieldInvariant)
        {
          return yieldInvariant.Layer == currLayerNum ? Y : P;
        }

        var callee = (YieldProcedureDecl)callCmd.Proc;
        if (callCmd.IsAsync)
        {
          if (callee.MoverType.HasValue && callee.Layer == currLayerNum)
          {
            return ModifiesGlobalLabel(callee.Modifies);
          }

          if (!callee.MoverType.HasValue && callee.Layer < currLayerNum)
          {
            if (callCmd.HasAttribute(CivlAttributes.SYNC))
            {
              return ModifiesGlobalLabel(callee.RefinedActionAtLayer(currLayerNum).ModifiedVars);
            }
            else
            {
              return P;
            }
          }

          var calleeYieldRequires = callee.YieldRequires.Select(x => ((YieldInvariantDecl)x.Proc).Layer == currLayerNum);
          var calleeYieldPreserves = callee.YieldPreserves.Select(x => ((YieldInvariantDecl)x.Proc).Layer == currLayerNum);
          if (calleeYieldRequires.Any() || calleeYieldPreserves.Any())
          {
            return A;
          }

          return P;
        }
        else
        {
          if (callee.MoverType.HasValue && callee.Layer == currLayerNum)
          {
            return ModifiesGlobalLabel(callee.Modifies);
          }

          if (!callee.MoverType.HasValue && callee.Layer < currLayerNum)
          {
            return ModifiesGlobalLabel(callee.RefinedActionAtLayer(currLayerNum).ModifiedVars);
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
        if (parCallCmd.CallCmds.Any(callCmd => CallCmdLabel(callCmd) == Y && callCmd.Proc is not YieldInvariantDecl))
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
          if (label == P || label == Y && callCmd.Proc is YieldInvariantDecl)
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
