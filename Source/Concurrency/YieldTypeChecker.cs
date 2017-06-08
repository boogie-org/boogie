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

        public YieldTypeChecker(CivlTypeChecker civlTypeChecker)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.checkingContext = new CheckingContext(null);
        }

        public void TypeCheck()
        {
            foreach (var impl in civlTypeChecker.program.Implementations.Where(i => civlTypeChecker.procToActionInfo.ContainsKey(i.Proc)))
            {
                impl.PruneUnreachableBlocks();
                Graph<Block> implGraph = Program.GraphFromImpl(impl);
                implGraph.ComputeLoops();
                int specLayerNum = civlTypeChecker.procToActionInfo[impl.Proc].createdAtLayerNum;
                foreach (int layerNum in civlTypeChecker.allLayerNums.Where(l => l <= specLayerNum))
                {
                    PerLayerYieldTypeChecker perLayerTypeChecker = new PerLayerYieldTypeChecker(civlTypeChecker, impl, layerNum, implGraph.Headers, checkingContext);
                    perLayerTypeChecker.TypeCheckLayer();
                }
            }

            // TODO: Remove "terminates" attribute
        }

        private class PerLayerYieldTypeChecker
        {
            int stateCounter;
            CivlTypeChecker civlTypeChecker;
            Implementation impl;
            int currLayerNum;
            Dictionary<Absy, int> absyToNode;
            Dictionary<int, Absy> nodeToAbsy;
            int initialState;
            HashSet<int> finalStates;
            Dictionary<Tuple<int, int>, int> edgeLabels;
            IEnumerable<Block> loopHeaders;

            CheckingContext checkingContext;

            public PerLayerYieldTypeChecker(CivlTypeChecker civlTypeChecker, Implementation impl, int currLayerNum, IEnumerable<Block> loopHeaders, CheckingContext checkingContext)
            {
                this.civlTypeChecker = civlTypeChecker;
                this.impl = impl;
                this.currLayerNum = currLayerNum;
                this.loopHeaders = loopHeaders;
                this.stateCounter = 0;
                this.absyToNode = new Dictionary<Absy, int>();
                this.initialState = 0;
                this.finalStates = new HashSet<int>();
                this.edgeLabels = new Dictionary<Tuple<int, int>, int>();

                this.checkingContext = checkingContext;
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
                ASpecCheck(implEdges);
                BSpecCheck(implEdges);
                CSpecCheck(implEdges);
            }

            private void ASpecCheck(List<Tuple<int, int, int>> implEdges)
            {
                Dictionary<int, HashSet<int>> initialConstraints = new Dictionary<int, HashSet<int>>();
                initialConstraints[initialState] = new HashSet<int>(new int[] { RM });
                foreach (var finalState in finalStates)
                {
                    initialConstraints[finalState] = new HashSet<int>(new int[] { LM });
                }
                SimulationRelation<int, int, int> x = new SimulationRelation<int, int, int>(implEdges, ASpec, initialConstraints);
                Dictionary<int, HashSet<int>> simulationRelation = x.ComputeSimulationRelation();
                if (simulationRelation[initialState].Count == 0)
                {
                    checkingContext.Error(impl, string.Format("Implementation {0} fails simulation check A at layer {1}. An action must be preceded by a yield.\n", impl.Name, currLayerNum));
                }
            }

            private void BSpecCheck(List<Tuple<int, int, int>> implEdges)
            {
                Dictionary<int, HashSet<int>> initialConstraints = new Dictionary<int, HashSet<int>>();
                initialConstraints[initialState] = new HashSet<int>(new int[] { LM });
                foreach (var finalState in finalStates)
                {
                    initialConstraints[finalState] = new HashSet<int>(new int[] { RM });
                }
                SimulationRelation<int, int, int> x = new SimulationRelation<int, int, int>(implEdges, BSpec, initialConstraints);
                Dictionary<int, HashSet<int>> simulationRelation = x.ComputeSimulationRelation();
                if (simulationRelation[initialState].Count == 0)
                {
                    checkingContext.Error(impl, string.Format("Implementation {0} fails simulation check B at layer {1}. An action must be succeeded by a yield.\n", impl.Name, currLayerNum));
                }
            }

            private void CSpecCheck(List<Tuple<int, int, int>> implEdges)
            {
                Dictionary<int, HashSet<int>> initialConstraints = new Dictionary<int, HashSet<int>>();
                foreach (Block block in loopHeaders)
                {
                    if (!IsTerminatingLoopHeader(block))
                    {
                        initialConstraints[absyToNode[block]] = new HashSet<int>(new int[] { RM });
                    }
                }
                SimulationRelation<int, int, int> x = new SimulationRelation<int, int, int>(implEdges, CSpec, initialConstraints);
                Dictionary<int, HashSet<int>> simulationRelation = x.ComputeSimulationRelation();
                if (simulationRelation[initialState].Count == 0)
                {
                    checkingContext.Error(impl, string.Format("Implementation {0} fails simulation check C at layer {1}. Transactions must be separated by a yield.\n", impl.Name, currLayerNum));
                }
            }

            private bool IsTerminatingLoopHeader(Block block)
            {
                foreach (Cmd cmd in block.Cmds)
                {
                    AssertCmd assertCmd = cmd as AssertCmd;
                    if (assertCmd != null && assertCmd.HasAttribute(CivlAttributes.TERMINATES) && civlTypeChecker.absyToLayerNums[assertCmd].Contains(currLayerNum))
                    {
                        return true;
                    }
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

                this.nodeToAbsy = new Dictionary<int, Absy>();
                foreach (KeyValuePair<Absy, int> state in absyToNode)
                {
                    this.nodeToAbsy[state.Value] = state.Key;
                }
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
                            if (callCmd.IsAsync)
                            {
                                ActionInfo actionInfo = civlTypeChecker.procToActionInfo[callCmd.Proc];
                                if (currLayerNum <= actionInfo.createdAtLayerNum)
                                    edgeLabels[edge] = L;
                                else
                                    edgeLabels[edge] = B;
                            }
                            else if (!civlTypeChecker.procToActionInfo.ContainsKey(callCmd.Proc))
                            {
                                edgeLabels[edge] = P;
                            }
                            else
                            {
                                MoverType moverType;
                                ActionInfo actionInfo = civlTypeChecker.procToActionInfo[callCmd.Proc];
                                if (actionInfo.createdAtLayerNum >= currLayerNum)
                                {
                                    moverType = MoverType.Top;
                                }
                                else
                                {
                                    moverType = actionInfo.moverType;
                                }
                                switch (moverType)
                                {
                                    case MoverType.Atomic:
                                        edgeLabels[edge] = A;
                                        break;
                                    case MoverType.Both:
                                        edgeLabels[edge] = B;
                                        break;
                                    case MoverType.Left:
                                        edgeLabels[edge] = L;
                                        break;
                                    case MoverType.Right:
                                        edgeLabels[edge] = R;
                                        break;
                                    case MoverType.Top:
                                        edgeLabels[edge] = Y;
                                        break;
                                }
                            }
                        }
                        else if (cmd is ParCallCmd)
                        {
                            ParCallCmd parCallCmd = cmd as ParCallCmd;
                            bool isYield = false;
                            bool isRightMover = true;
                            bool isLeftMover = true;
                            foreach (CallCmd callCmd in parCallCmd.CallCmds)
                            {
                                if (civlTypeChecker.procToActionInfo[callCmd.Proc].createdAtLayerNum >= currLayerNum)
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
                                    ActionInfo actionInfo = civlTypeChecker.procToActionInfo[callCmd.Proc];
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
