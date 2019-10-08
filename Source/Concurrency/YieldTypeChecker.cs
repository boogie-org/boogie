using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics;
using System.ComponentModel;

namespace Microsoft.Boogie
{
    public class YieldTypeChecker
    {
        // Edge labels of the automaton that abstracts the code of a procedure
        private const char Y = 'Y';  // yield
        private const char B = 'B';  // both mover action
        private const char L = 'L';  // left mover action
        private const char R = 'R';  // right mover action
        private const char A = 'A';  // atomic (non mover) action
        private const char P = 'P';  // private (local variable) access
        private const char I = 'I';  // introduction action
        
        // States of Bracket Automaton (check that all accesses to global variables are bracketed by yields)
        private const int BEFORE = 0;
        private const int INSIDE = 1;
        private const int AFTER = 2;
        
        // Transitions of Bracket Automaton
        static List<Tuple<int, int, int>> BracketSpec = new List<Tuple<int, int, int>>
        { // initial: BEFORE, final: AFTER
            new Tuple<int, int, int>(BEFORE, P, BEFORE),
            new Tuple<int, int, int>(BEFORE, Y, INSIDE),
            new Tuple<int, int, int>(BEFORE, Y, AFTER),
            new Tuple<int, int, int>(INSIDE, Y, INSIDE),
            new Tuple<int, int, int>(INSIDE, B, INSIDE),
            new Tuple<int, int, int>(INSIDE, R, INSIDE),
            new Tuple<int, int, int>(INSIDE, L, INSIDE),
            new Tuple<int, int, int>(INSIDE, A, INSIDE),
            new Tuple<int, int, int>(INSIDE, P, INSIDE),
            new Tuple<int, int, int>(INSIDE, I, INSIDE),
            new Tuple<int, int, int>(INSIDE, Y, AFTER),
            new Tuple<int, int, int>(AFTER, P, AFTER),
        };
        
        // States of Atomicity Automaton (check that transactions are separated by yields)
        private const int RM = 0;
        private const int LM = 1;
        
        // Transitions of Atomicity Automaton
        static List<Tuple<int, int, int>> AtomicitySpec = new List<Tuple<int, int, int>>
        { // initial: {RM, LM}, final: {RM, LM}
            new Tuple<int, int, int>(RM, P, RM),
            new Tuple<int, int, int>(RM, I, RM),
            new Tuple<int, int, int>(RM, B, RM),
            new Tuple<int, int, int>(RM, R, RM),
            new Tuple<int, int, int>(RM, Y, RM),
            new Tuple<int, int, int>(RM, L, LM),
            new Tuple<int, int, int>(RM, A, LM),
            new Tuple<int, int, int>(LM, P, LM),
            new Tuple<int, int, int>(LM, I, LM),
            new Tuple<int, int, int>(LM, B, LM),
            new Tuple<int, int, int>(LM, L, LM),
            new Tuple<int, int, int>(LM, Y, RM),
        };

        private static int MoverTypeToLabel(MoverType moverType)
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

        CivlTypeChecker civlTypeChecker;
        public CheckingContext checkingContext;
        private Graph<MoverProc> moverProcedureCallGraph;

        public YieldTypeChecker(CivlTypeChecker civlTypeChecker)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.checkingContext = new CheckingContext(null);
            this.moverProcedureCallGraph = new Graph<MoverProc>();
        }

        public void TypeCheck()
        {
            // Mover procedures can only call other mover procedures on the same layer.
            // Thus, the constructed call graph naturally forms disconnected components w.r.t. layers and we
            // can keep a single graph instead of one for each layer;
            foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc)))
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

            foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc)))
            {
                var yieldingProc = civlTypeChecker.procToYieldingProc[impl.Proc];

                impl.PruneUnreachableBlocks();
                Graph<Block> implGraph = Program.GraphFromImpl(impl);
                implGraph.ComputeLoops();

                foreach (int layerNum in civlTypeChecker.allRefinementLayers.Where(l => l <= yieldingProc.upperLayer))
                {
                    PerLayerYieldTypeChecker perLayerTypeChecker = new PerLayerYieldTypeChecker(this, yieldingProc, impl, layerNum, implGraph);
                    perLayerTypeChecker.TypeCheckLayer();
                }
            }

            // To allow garbage collection
            moverProcedureCallGraph = null;

            // TODO: Remove "terminates" attribute
        }

        private class PerLayerYieldTypeChecker
        {
            YieldTypeChecker @base;
            YieldingProc yieldingProc;
            Implementation impl;
            int currLayerNum;
            Graph<Block> implGraph;

            List<Tuple<Absy, int, Absy>> implEdges;
            Absy initialState;
            HashSet<Absy> finalStates;

            public PerLayerYieldTypeChecker(YieldTypeChecker @base, YieldingProc yieldingProc, Implementation impl, int currLayerNum, Graph<Block> implGraph)
            {
                this.@base = @base;
                this.yieldingProc = yieldingProc;
                this.impl = impl;
                this.currLayerNum = currLayerNum;
                this.implGraph = implGraph;
                this.initialState = impl.Blocks[0];
                this.finalStates = new HashSet<Absy>();
                this.implEdges = new List<Tuple<Absy, int, Absy>>();
            }

            public void TypeCheckLayer()
            {
                ComputeGraph();
                // Console.WriteLine(PrintGraph(impl, implEdges, initialState, finalStates));

                if (!IsMoverProcedure)
                {
                    BracketCheck();
                }
                AtomicityCheck();
            }

            private void BracketCheck()
            {
                var initialConstraints = new Dictionary<Absy, HashSet<int>>();
                initialConstraints[initialState] = new HashSet<int> { BEFORE };
                foreach (var finalState in finalStates)
                {
                    initialConstraints[finalState] = new HashSet<int> { AFTER };
                }

                var simulationRelation = new SimulationRelation<Absy, int, int>(implEdges, BracketSpec, initialConstraints).ComputeSimulationRelation();
                if (simulationRelation[initialState].Count == 0)
                {
                    @base.checkingContext.Error(impl, string.Format("Implementation {0} fails bracket check at layer {1}. All code that accesses global variables must be bracketed by yields.", impl.Name, currLayerNum));
                }
            }

            private void AtomicityCheck()
            {
                var initialConstraints = new Dictionary<Absy, HashSet<int>>();

                foreach (Block header in implGraph.Headers)
                {
                    if (!IsTerminatingLoopHeader(header))
                    {
                        initialConstraints[header] = new HashSet<int> { RM };
                    }
                }
                if (IsMoverProcedure)
                {
                    foreach (var call in impl.Blocks.SelectMany(b => b.cmds).OfType<CallCmd>())
                    {
                        if (!IsTerminatingCall(call))
                        {
                            initialConstraints[call] = new HashSet<int> { RM };
                        }
                    }
                }

                var simulationRelation = new SimulationRelation<Absy, int, int>(implEdges, AtomicitySpec, initialConstraints).ComputeSimulationRelation();

                if (IsMoverProcedure)
                {
                    if (!CheckAtomicity(simulationRelation))
                    {
                        @base.checkingContext.Error(impl, "The atomicity declared for mover procedure is not valid");
                    }
                }
                else if (simulationRelation[initialState].Count == 0)
                {
                    @base.checkingContext.Error(impl, string.Format("Implementation {0} fails atomicity check at layer {1}. Transactions must be separated by yields.", impl.Name, currLayerNum));
                }
            }

            private bool IsMoverProcedure { get { return yieldingProc is MoverProc && yieldingProc.upperLayer == currLayerNum; } }

            private bool IsTerminatingLoopHeader(Block block)
            {
                return block.cmds.OfType<AssertCmd>().Any(c => c.HasAttribute(CivlAttributes.TERMINATES) && @base.civlTypeChecker.absyToLayerNums[c].Contains(currLayerNum));
            }

            private bool IsTerminatingCall(CallCmd call){
                return !IsRecursiveMoverProcedureCall(call) || call.Proc.HasAttribute(CivlAttributes.TERMINATES);
            }

            private bool CheckAtomicity(Dictionary<Absy, HashSet<int>> simulationRelation)
            {
                if (yieldingProc.moverType == MoverType.Atomic && simulationRelation[initialState].Count == 0) return false;
                if (yieldingProc.IsRightMover && (!simulationRelation[initialState].Contains(RM) || finalStates.Any(f => !simulationRelation[f].Contains(RM)))) return false;
                if (yieldingProc.IsLeftMover && !simulationRelation[initialState].Contains(LM)) return false;
                return true;
            }

            private bool IsRecursiveMoverProcedureCall(CallCmd call)
            {
                MoverProc source = null;
                if (@base.civlTypeChecker.procToYieldingProc.ContainsKey(call.Proc))
                    source = @base.civlTypeChecker.procToYieldingProc[call.Proc] as MoverProc;
                if (source == null)
                    return false;

                MoverProc target = (MoverProc)yieldingProc;

                HashSet<MoverProc> frontier = new HashSet<MoverProc> { source };
                HashSet<MoverProc> visited = new HashSet<MoverProc>();

                while (frontier.Count > 0)
                {
                    var curr = frontier.First();
                    frontier.Remove(curr);
                    visited.Add(curr);

                    if (curr == target)
                        return true;
                    frontier.UnionWith(@base.moverProcedureCallGraph.Successors(curr).Except(visited));
                }

                return false;
            }

            private void ComputeGraph()
            {
                // Internal representation
                // At the end of the method, we translate to List<Tuple<Absy, int, Absy>>
                Dictionary<Tuple<Absy, Absy>, int> edgeLabels = new Dictionary<Tuple<Absy, Absy>, int>();

                foreach (Block block in impl.Blocks)
                {
                    // Block entry edge
                    Absy blockEntry = block.Cmds.Count == 0 ? (Absy)block.TransferCmd : (Absy)block.Cmds[0];
                    edgeLabels[new Tuple<Absy, Absy>(block, blockEntry)] = P;

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
                        Absy next = (i + 1 == block.Cmds.Count) ? (Absy)block.TransferCmd : block.Cmds[i + 1];
                        Tuple<Absy, Absy> edge = new Tuple<Absy, Absy>(cmd, next);
                        if (cmd is CallCmd callCmd)
                        {
                            edgeLabels[edge] = CallCmdLabel(callCmd);
                        }
                        else if (cmd is ParCallCmd parCallCmd)
                        {
                            edgeLabels[edge] = ParCallCmdLabel(parCallCmd);
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
                    implEdges.Add(new Tuple<Absy, int, Absy>(e.Item1, edgeLabels[e], e.Item2));
                }
            }

            private int CallCmdLabel(CallCmd callCmd)
            {
                if (@base.civlTypeChecker.procToIntroductionProc.ContainsKey(callCmd.Proc))
                    return I;

                YieldingProc callee = @base.civlTypeChecker.procToYieldingProc[callCmd.Proc];
                if (callCmd.IsAsync)
                {
                    if ((currLayerNum < yieldingProc.upperLayer && currLayerNum > callee.upperLayer) ||
                        (currLayerNum == yieldingProc.upperLayer && callee.upperLayer < yieldingProc.upperLayer))
                    {
                        return MoverTypeToLabel(callee.moverType);
                    }
                    return L;
                }
                else
                {
                    if (callee.upperLayer < currLayerNum || (callee.upperLayer == currLayerNum && callee is MoverProc))
                    {
                        return MoverTypeToLabel(callee.moverType);
                    }
                    return Y;
                }
            }

            private int ParCallCmdLabel(ParCallCmd parCallCmd)
            {
                foreach (CallCmd callCmd in parCallCmd.CallCmds)
                {
                    if (@base.civlTypeChecker.procToYieldingProc[callCmd.Proc].upperLayer >= currLayerNum)
                        return Y;
                }

                bool isRightMover = true;
                bool isLeftMover = true;
                int numAtomicActions = 0;
                foreach (CallCmd callCmd in parCallCmd.CallCmds)
                {
                    YieldingProc callee = @base.civlTypeChecker.procToYieldingProc[callCmd.Proc];
                    isRightMover = isRightMover && callee.IsRightMover;
                    isLeftMover = isLeftMover && callee.IsLeftMover;
                    if (callee is ActionProc)
                    {
                        numAtomicActions++;
                    }
                }

                if (isLeftMover && isRightMover)
                    return B;
                else if (isLeftMover)
                    return L;
                else if (isRightMover)
                    return R;

                Debug.Assert(numAtomicActions == 1);
                return A;
            }

            private static string PrintGraph(Implementation impl, List<Tuple<Absy, int, Absy>> edges, Absy initialState, HashSet<Absy> finalStates)
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
                    s.AppendLine("  \"" + map[e.Item1] + "\" -- " + (char)e.Item2 + " --> \"" + map[e.Item3] + "\";");
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
