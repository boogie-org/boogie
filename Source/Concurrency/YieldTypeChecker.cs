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

namespace Microsoft.Boogie
{
    public class YieldTypeChecker
    {
        // States of Yield Sufficiency Automaton (YSA)
        static int RM = 0;
        static int LM = 1;

        // Edge labels of YSA
        static char Y = 'Y';
        static char B = 'B';
        static char L = 'L';
        static char R = 'R';
        static char A = 'A';
        static char P = 'P';

        static List<Tuple<int, int, int>> ASpec = new List<Tuple<int, int, int>>
        { // initial: RM, final: LM
            new Tuple<int, int, int>(RM, Y, LM),
            new Tuple<int, int, int>(LM, Y, LM),
            new Tuple<int, int, int>(LM, B, LM),
            new Tuple<int, int, int>(LM, R, LM),
            new Tuple<int, int, int>(LM, L, LM),
            new Tuple<int, int, int>(LM, A, LM),
            new Tuple<int, int, int>(RM, P, RM),
            new Tuple<int, int, int>(LM, P, LM)
        };
        static List<Tuple<int, int, int>> BSpec = new List<Tuple<int, int, int>>
        { // initial: LM, final: RM
            new Tuple<int, int, int>(LM, Y, RM),
            new Tuple<int, int, int>(LM, Y, LM),
            new Tuple<int, int, int>(LM, B, LM),
            new Tuple<int, int, int>(LM, R, LM),
            new Tuple<int, int, int>(LM, L, LM),
            new Tuple<int, int, int>(LM, A, LM),
            new Tuple<int, int, int>(RM, P, RM),
            new Tuple<int, int, int>(LM, P, LM)
        };
        static List<Tuple<int, int, int>> CSpec = new List<Tuple<int, int, int>>
        { // initial: {RM, LM}, final: {RM, LM}
            new Tuple<int, int, int>(RM, B, RM),
            new Tuple<int, int, int>(RM, R, RM),
            new Tuple<int, int, int>(RM, Y, RM),
            new Tuple<int, int, int>(RM, B, LM),
            new Tuple<int, int, int>(RM, R, LM),
            new Tuple<int, int, int>(RM, L, LM),
            new Tuple<int, int, int>(RM, A, LM),
            new Tuple<int, int, int>(LM, B, LM),
            new Tuple<int, int, int>(LM, L, LM),
            new Tuple<int, int, int>(LM, Y, RM),
            new Tuple<int, int, int>(RM, P, RM),
            new Tuple<int, int, int>(LM, P, LM)
        };

        CivlTypeChecker civlTypeChecker;
        public CheckingContext checkingContext;
        private Graph<MoverActionInfo> moverProcedureCallGraph;

        public YieldTypeChecker(CivlTypeChecker civlTypeChecker)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.checkingContext = new CheckingContext(null);
            this.moverProcedureCallGraph = new Graph<MoverActionInfo>();
        }

        public void TypeCheck()
        {
            // Mover procedures can only call other mover procedures on the same layer.
            // Thus, the constructed call graph naturally forms disconnected components w.r.t. layers and we
            // can keep a single graph instead of one for each layer;
            foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => civlTypeChecker.procToActionInfo.ContainsKey(impl.Proc)))
            {
                MoverActionInfo callerActionInfo = civlTypeChecker.procToActionInfo[impl.Proc] as MoverActionInfo;
                if (callerActionInfo == null) continue;

                foreach (var callCmd in impl.Blocks.SelectMany(b => b.Cmds).OfType<CallCmd>())
                {
                    if (civlTypeChecker.procToActionInfo.ContainsKey(callCmd.Proc))
                    {
                        MoverActionInfo calleeActionInfo = civlTypeChecker.procToActionInfo[callCmd.Proc] as MoverActionInfo;
                        if (calleeActionInfo == null) continue;

                        Debug.Assert(callerActionInfo.createdAtLayerNum == calleeActionInfo.createdAtLayerNum);
                        moverProcedureCallGraph.AddEdge(callerActionInfo, calleeActionInfo);
                    }
                }
            }

            foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => civlTypeChecker.procToActionInfo.ContainsKey(impl.Proc)))
            {
                var actionInfo = civlTypeChecker.procToActionInfo[impl.Proc];

                impl.PruneUnreachableBlocks();
                Graph<Block> implGraph = Program.GraphFromImpl(impl);
                implGraph.ComputeLoops();

                foreach (int layerNum in civlTypeChecker.allLayerNums.Where(l => l <= actionInfo.createdAtLayerNum))
                {
                    PerLayerYieldTypeChecker perLayerTypeChecker = new PerLayerYieldTypeChecker(this, actionInfo, impl, layerNum, implGraph);
                    perLayerTypeChecker.TypeCheckLayer();
                }
            }

            // To allow garbage collection
            moverProcedureCallGraph = null;

            // TODO: Remove "terminates" attribute
        }

        private class PerLayerYieldTypeChecker
        {
            int stateCounter;
            YieldTypeChecker @base;
            ActionInfo actionInfo;
            Implementation impl;
            int currLayerNum;
            Dictionary<Absy, int> absyToNode;
            Dictionary<int, Absy> nodeToAbsy;
            int initialState;
            HashSet<int> finalStates;
            Dictionary<Tuple<int, int>, int> edgeLabels;
            Graph<Block> implGraph;

            public PerLayerYieldTypeChecker(YieldTypeChecker @base, ActionInfo actionInfo, Implementation impl, int currLayerNum, Graph<Block> implGraph)
            {
                this.@base = @base;
                this.actionInfo = actionInfo;
                this.impl = impl;
                this.currLayerNum = currLayerNum;
                this.implGraph = implGraph;
                this.stateCounter = 0;
                this.absyToNode = new Dictionary<Absy, int>();
                this.initialState = 0;
                this.finalStates = new HashSet<int>();
                this.edgeLabels = new Dictionary<Tuple<int, int>, int>();
            }

            public void TypeCheckLayer()
            {
                ComputeStates();
                ComputeEdges();
                IsYieldTypeSafe();
            }

            private void IsYieldTypeSafe()
            {
                List<Tuple<int, int, int>> implEdges = new List<Tuple<int, int, int>>();
                foreach (Tuple<int, int> e in edgeLabels.Keys)
                {
                    implEdges.Add(new Tuple<int, int, int>(e.Item1, edgeLabels[e], e.Item2));
                }
                //Console.WriteLine(PrintGraph(impl, implEdges, initialState, finalStates));

                if (!IsMoverProcedure)
                {
                    ASpecCheck(implEdges);
                    BSpecCheck(implEdges);
                }
                CSpecCheck(implEdges);
            }

            private void ASpecCheck(List<Tuple<int, int, int>> implEdges)
            {
                var initialConstraints = new Dictionary<int, HashSet<int>>();
                initialConstraints[initialState] = new HashSet<int> { RM };
                foreach (var finalState in finalStates)
                {
                    initialConstraints[finalState] = new HashSet<int> { LM };
                }

                var simulationRelation = new SimulationRelation<int, int, int>(implEdges, ASpec, initialConstraints).ComputeSimulationRelation();
                if (simulationRelation[initialState].Count == 0)
                {
                    @base.checkingContext.Error(impl, string.Format("Implementation {0} fails simulation check A at layer {1}. An action must be preceded by a yield.\n", impl.Name, currLayerNum));
                }
            }

            private void BSpecCheck(List<Tuple<int, int, int>> implEdges)
            {
                var initialConstraints = new Dictionary<int, HashSet<int>>();
                initialConstraints[initialState] = new HashSet<int> { LM };
                foreach (var finalState in finalStates)
                {
                    initialConstraints[finalState] = new HashSet<int> { RM };
                }

                var simulationRelation = new SimulationRelation<int, int, int>(implEdges, BSpec, initialConstraints).ComputeSimulationRelation();
                if (simulationRelation[initialState].Count == 0)
                {
                    @base.checkingContext.Error(impl, string.Format("Implementation {0} fails simulation check B at layer {1}. An action must be succeeded by a yield.\n", impl.Name, currLayerNum));
                }
            }

            private void CSpecCheck(List<Tuple<int, int, int>> implEdges)
            {
                var initialConstraints = new Dictionary<int, HashSet<int>>();

                if (IsMoverProcedure)
                {
                    foreach (Block header in implGraph.Headers.Where(h => !IsTerminatingLoopHeader(h)))
                    {
                        initialConstraints[absyToNode[header]] = new HashSet<int> { RM };
                    }
                    foreach (var call in impl.Blocks.SelectMany(b => b.cmds).OfType<CallCmd>().Where(c => IsRecursiveMoverProcedureCall(c) && !IsTerminating(c.Proc)))
                    {
                        initialConstraints[absyToNode[call]] = new HashSet<int> { RM };
                    }
                }
                else
                {
                    foreach (Block header in implGraph.Headers)
                    {
                        initialConstraints[absyToNode[header]] = new HashSet<int> { RM };
                    }
                }

                var simulationRelation = new SimulationRelation<int, int, int>(implEdges, CSpec, initialConstraints).ComputeSimulationRelation();

                if (IsMoverProcedure)
                {
                    if (!CheckAtomicity(simulationRelation))
                    {
                        @base.checkingContext.Error(impl, "The atomicity declared for mover procedure is not valid");
                    }
                }
                else if (simulationRelation[initialState].Count == 0)
                {
                    @base.checkingContext.Error(impl, string.Format("Implementation {0} fails simulation check C at layer {1}. Transactions must be separated by a yield.\n", impl.Name, currLayerNum));
                }
            }

            private bool IsMoverProcedure { get { return actionInfo is MoverActionInfo && actionInfo.createdAtLayerNum == currLayerNum; } }

            private static bool IsTerminating(ICarriesAttributes x)
            {
                return x.HasAttribute(CivlAttributes.TERMINATES);
            }

            private bool IsTerminatingLoopHeader(Block block)
            {
                return block.cmds.OfType<AssertCmd>().Any(c => IsTerminating(c));
            }

            private bool CheckAtomicity(Dictionary<int, HashSet<int>> simulationRelation)
            {
                if (actionInfo.moverType == MoverType.Atomic && simulationRelation[initialState].Count == 0) return false;
                if (actionInfo.IsRightMover && (!simulationRelation[initialState].Contains(RM) || finalStates.Any(f => !simulationRelation[f].Contains(RM)))) return false;
                if (actionInfo.IsLeftMover && !simulationRelation[initialState].Contains(LM)) return false;
                return true;
            }
            
            private bool IsRecursiveMoverProcedureCall(CallCmd call)
            {
                MoverActionInfo target = (MoverActionInfo)actionInfo;
                MoverActionInfo source = null;
                if (@base.civlTypeChecker.procToActionInfo.ContainsKey(call.Proc))
                    source = @base.civlTypeChecker.procToActionInfo[call.Proc] as MoverActionInfo;
                if (source == null)
                    return false;

                HashSet<MoverActionInfo> frontier = new HashSet<MoverActionInfo> { source };
                HashSet<MoverActionInfo> visited = new HashSet<MoverActionInfo>();

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

            private void ComputeStates()
            {
                foreach (Block block in impl.Blocks)
                {
                    absyToNode[block] = stateCounter++;
                    foreach (Cmd cmd in block.Cmds)
                    {
                        absyToNode[cmd] = stateCounter++;
                    }
                    absyToNode[block.TransferCmd] = stateCounter++;
                    if (block.TransferCmd is ReturnCmd)
                    {
                        finalStates.Add(absyToNode[block.TransferCmd]);
                    }
                }
                foreach (Block block in impl.Blocks)
                {
                    Absy blockEntry = block.Cmds.Count == 0 ? (Absy)block.TransferCmd : (Absy)block.Cmds[0];
                    edgeLabels[new Tuple<int, int>(absyToNode[block], absyToNode[blockEntry])] = P;

                    GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                    if (gotoCmd == null) continue;
                    foreach (Block successor in gotoCmd.labelTargets)
                    {
                        edgeLabels[new Tuple<int, int>(absyToNode[gotoCmd], absyToNode[successor])] = P;
                    }
                }

                // reverse mapping
                this.nodeToAbsy = absyToNode.ToDictionary(x => x.Value, x => x.Key);
            }

            private void ComputeEdges()
            {
                foreach (Block block in impl.Blocks)
                {
                    for (int i = 0; i < block.Cmds.Count; i++)
                    {
                        Cmd cmd = block.Cmds[i];
                        int curr = absyToNode[cmd];
                        int next = (i + 1 == block.Cmds.Count) ? absyToNode[block.TransferCmd] : absyToNode[block.Cmds[i + 1]];
                        Tuple<int, int> edge = new Tuple<int, int>(curr, next);
                        if (cmd is CallCmd)
                        {
                            CallCmd callCmd = cmd as CallCmd;
                            if (!@base.civlTypeChecker.procToActionInfo.ContainsKey(callCmd.Proc))
                            {
                                edgeLabels[edge] = P;
                            }
                            else
                            {
                                ActionInfo calledAction = @base.civlTypeChecker.procToActionInfo[callCmd.Proc];
                                // TODO: double check that label assignment is correct
                                if (callCmd.IsAsync)
                                {
                                    if (currLayerNum <= calledAction.createdAtLayerNum)
                                        edgeLabels[edge] = L;
                                    else
                                        edgeLabels[edge] = B;
                                }
                                else
                                {
                                    MoverType? moverType = null;
                                    if (calledAction.createdAtLayerNum < currLayerNum || (calledAction.createdAtLayerNum == currLayerNum && calledAction is MoverActionInfo))
                                    {
                                        moverType = calledAction.moverType;
                                    }

                                    switch (moverType)
                                    {
                                        case MoverType.Atomic:
                                            edgeLabels[edge] = A; break;
                                        case MoverType.Both:
                                            edgeLabels[edge] = B; break;
                                        case MoverType.Left:
                                            edgeLabels[edge] = L; break;
                                        case MoverType.Right:
                                            edgeLabels[edge] = R; break;
                                        case null:
                                            edgeLabels[edge] = Y; break;
                                    }
                                }
                            }
                        }
                        else if (cmd is ParCallCmd)
                        {
                            // TODO: handle mover procedures!
                            ParCallCmd parCallCmd = cmd as ParCallCmd;
                            bool isYield = false;
                            bool isRightMover = true;
                            bool isLeftMover = true;
                            foreach (CallCmd callCmd in parCallCmd.CallCmds)
                            {
                                if (@base.civlTypeChecker.procToActionInfo[callCmd.Proc].createdAtLayerNum >= currLayerNum)
                                {
                                    isYield = true;
                                }
                            }
                            if (isYield)
                            {
                                edgeLabels[edge] = Y;
                            }
                            else
                            {
                                int numAtomicActions = 0;
                                foreach (CallCmd callCmd in parCallCmd.CallCmds)
                                {
                                    ActionInfo actionInfo = @base.civlTypeChecker.procToActionInfo[callCmd.Proc];
                                    isRightMover = isRightMover && actionInfo.IsRightMover;
                                    isLeftMover = isLeftMover && actionInfo.IsLeftMover;
                                    if (actionInfo is AtomicActionInfo)
                                    {
                                        numAtomicActions++;
                                    }
                                }
                                if (isLeftMover && isRightMover)
                                {
                                    edgeLabels[edge] = B;
                                }
                                else if (isLeftMover)
                                {
                                    edgeLabels[edge] = L;
                                }
                                else if (isRightMover)
                                {
                                    edgeLabels[edge] = R;
                                }
                                else
                                {
                                    Debug.Assert(numAtomicActions == 1);
                                    edgeLabels[edge] = A;
                                }
                            }
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
            }

            private static string PrintGraph(Implementation impl, List<Tuple<int, int, int>> edges, int initialState, HashSet<int> finalStates)
            {
                var s = new StringBuilder();
                s.AppendLine("\nImplementation " + impl.Proc.Name + " digraph G {");
                foreach (var e in edges)
                {
                    s.AppendLine("  \"" + e.Item1.ToString() + "\" -- " + (char)e.Item2 + " --> " + "  \"" + e.Item3.ToString() + "\";");
                }
                s.AppendLine("}");
                s.AppendLine("Initial state: " + initialState);
                s.Append("Final states: ");
                bool first = true;
                foreach (int finalState in finalStates)
                {
                    s.Append((first ? "" : ", ") + finalState);
                    first = false;
                }
                s.AppendLine();
                return s.ToString();
            }
        }
    }
}
