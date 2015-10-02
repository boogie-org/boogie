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
    class YieldTypeChecker
    {
        static List<Tuple<int, int, int>> ASpec;
        static List<Tuple<int, int, int>> BSpec;
        static List<Tuple<int, int, int>> CSpec;
        static YieldTypeChecker()
        {
            // initial: 0, final: 1
            ASpec = new List<Tuple<int,int,int>>();
            ASpec.Add(new Tuple<int, int, int>(0, 'Y', 1));
            ASpec.Add(new Tuple<int, int, int>(1, 'Y', 1));
            ASpec.Add(new Tuple<int, int, int>(1, 'B', 1));
            ASpec.Add(new Tuple<int, int, int>(1, 'R', 1));
            ASpec.Add(new Tuple<int, int, int>(1, 'L', 1));
            ASpec.Add(new Tuple<int, int, int>(1, 'A', 1));
            ASpec.Add(new Tuple<int, int, int>(0, 'P', 0));
            ASpec.Add(new Tuple<int, int, int>(1, 'P', 1));

            // initial: 1, final: 0
            BSpec = new List<Tuple<int, int, int>>();
            BSpec.Add(new Tuple<int, int, int>(1, 'Y', 0));
            BSpec.Add(new Tuple<int, int, int>(1, 'Y', 1));
            BSpec.Add(new Tuple<int, int, int>(1, 'B', 1));
            BSpec.Add(new Tuple<int, int, int>(1, 'R', 1));
            BSpec.Add(new Tuple<int, int, int>(1, 'L', 1));
            BSpec.Add(new Tuple<int, int, int>(1, 'A', 1));
            BSpec.Add(new Tuple<int, int, int>(0, 'P', 0));
            BSpec.Add(new Tuple<int, int, int>(1, 'P', 1));

            // initial: {0, 1}, final: {0, 1}
            CSpec = new List<Tuple<int,int,int>>();
            CSpec.Add(new Tuple<int, int, int>(0, 'B', 0));
            CSpec.Add(new Tuple<int, int, int>(0, 'R', 0));
            CSpec.Add(new Tuple<int, int, int>(0, 'Y', 0));
            CSpec.Add(new Tuple<int, int, int>(0, 'B', 1));
            CSpec.Add(new Tuple<int, int, int>(0, 'R', 1));
            CSpec.Add(new Tuple<int, int, int>(0, 'L', 1));
            CSpec.Add(new Tuple<int, int, int>(0, 'A', 1));
            CSpec.Add(new Tuple<int, int, int>(1, 'B', 1));
            CSpec.Add(new Tuple<int, int, int>(1, 'L', 1));
            CSpec.Add(new Tuple<int, int, int>(1, 'Y', 0));
            CSpec.Add(new Tuple<int, int, int>(0, 'P', 0));
            CSpec.Add(new Tuple<int, int, int>(1, 'P', 1));
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
            initialConstraints[initialState] = new HashSet<int>(new int[] { 0 });
            foreach (var finalState in finalStates)
            {
                initialConstraints[finalState] = new HashSet<int>(new int[] { 1 });
            }
            SimulationRelation<int, int, int> x = new SimulationRelation<int, int, int>(implEdges, ASpec, initialConstraints);
            Dictionary<int, HashSet<int>> simulationRelation = x.ComputeSimulationRelation();
            if (simulationRelation[initialState].Count == 0)
            {
                civlTypeChecker.Error(impl, string.Format("Implementation {0} fails simulation check A at layer {1}. An action must be preceded by a yield.\n", impl.Name, currLayerNum));
            }
        }

        private void BSpecCheck(List<Tuple<int, int, int>> implEdges)
        {
            Dictionary<int, HashSet<int>> initialConstraints = new Dictionary<int, HashSet<int>>();
            initialConstraints[initialState] = new HashSet<int>(new int[] { 1 });
            foreach (var finalState in finalStates)
            {
                initialConstraints[finalState] = new HashSet<int>(new int[] { 0 });
            }
            SimulationRelation<int, int, int> x = new SimulationRelation<int, int, int>(implEdges, BSpec, initialConstraints);
            Dictionary<int, HashSet<int>> simulationRelation = x.ComputeSimulationRelation();
            if (simulationRelation[initialState].Count == 0)
            {
                civlTypeChecker.Error(impl, string.Format("Implementation {0} fails simulation check B at layer {1}. An action must be succeeded by a yield.\n", impl.Name, currLayerNum));
            }
        }

        private void CSpecCheck(List<Tuple<int, int, int>> implEdges)
        {
            Dictionary<int, HashSet<int>> initialConstraints = new Dictionary<int, HashSet<int>>();
            foreach (Block block in loopHeaders)
            {
                if (!IsTerminatingLoopHeader(block))
                {
                    initialConstraints[absyToNode[block]] = new HashSet<int>(new int[] { 0 });
                }
            }
            SimulationRelation<int, int, int> x = new SimulationRelation<int, int, int>(implEdges, CSpec, initialConstraints);
            Dictionary<int, HashSet<int>> simulationRelation = x.ComputeSimulationRelation();
            if (simulationRelation[initialState].Count == 0)
            {
                civlTypeChecker.Error(impl, string.Format("Implementation {0} fails simulation check C at layer {1}. Transactions must be separated by a yield.\n", impl.Name, currLayerNum));
            }
        }

        private bool IsTerminatingLoopHeader(Block block)
        {
            foreach (Cmd cmd in block.Cmds)
            {
                AssertCmd assertCmd = cmd as AssertCmd;
                if (assertCmd != null && QKeyValue.FindBoolAttribute(assertCmd.Attributes, "terminates") && civlTypeChecker.absyToLayerNums[assertCmd].Contains(currLayerNum))
                {
                    return true;
                }
            }
            return false;
        }
        
        public static void PerformYieldSafeCheck(CivlTypeChecker civlTypeChecker)
        {
            foreach (var impl in civlTypeChecker.program.Implementations)
            {
                if (!civlTypeChecker.procToActionInfo.ContainsKey(impl.Proc)) continue;
                impl.PruneUnreachableBlocks();
                Graph<Block> implGraph = Program.GraphFromImpl(impl);
                implGraph.ComputeLoops();
                int specLayerNum = civlTypeChecker.procToActionInfo[impl.Proc].createdAtLayerNum;
                foreach (int layerNum in civlTypeChecker.AllLayerNums)
                {
                    if (layerNum > specLayerNum) continue;
                    YieldTypeChecker executor = new YieldTypeChecker(civlTypeChecker, impl, layerNum, implGraph.Headers);
                }
            }
        }

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

        private YieldTypeChecker(CivlTypeChecker civlTypeChecker, Implementation impl, int currLayerNum, IEnumerable<Block> loopHeaders)
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
            
            foreach (Block block in impl.Blocks)
            {
                absyToNode[block] = stateCounter;
                stateCounter++;
                foreach (Cmd cmd in block.Cmds)
                {
                    absyToNode[cmd] = stateCounter;
                    stateCounter++;
                }
                absyToNode[block.TransferCmd] = stateCounter;
                stateCounter++;
                if (block.TransferCmd is ReturnCmd)
                {
                    finalStates.Add(absyToNode[block.TransferCmd]);
                }
            }
            foreach (Block block in impl.Blocks)
            {
                Absy blockEntry = block.Cmds.Count == 0 ? (Absy)block.TransferCmd : (Absy)block.Cmds[0];
                edgeLabels[new Tuple<int, int>(absyToNode[block], absyToNode[blockEntry])] = 'P';
                
                GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                if (gotoCmd == null) continue;
                foreach (Block successor in gotoCmd.labelTargets)
                {
                    edgeLabels[new Tuple<int, int>(absyToNode[gotoCmd], absyToNode[successor])] = 'P';
                }
            }

            this.nodeToAbsy = new Dictionary<int, Absy>();
            foreach (KeyValuePair<Absy, int> state in absyToNode)
            {
                this.nodeToAbsy[state.Value] = state.Key;
            }

            ComputeGraph();
            IsYieldTypeSafe();
        }

        private void ComputeGraph()
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
                                edgeLabels[edge] = 'L';
                            else
                                edgeLabels[edge] = 'B';
                        }
                        else if (!civlTypeChecker.procToActionInfo.ContainsKey(callCmd.Proc))
                        {
                            edgeLabels[edge] = 'P';
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
                                AtomicActionInfo atomicActionInfo = actionInfo as AtomicActionInfo;
                                if (atomicActionInfo == null)
                                    moverType = MoverType.Both;
                                else
                                    moverType = atomicActionInfo.moverType;
                            }
                            switch (moverType)
                            {
                                case MoverType.Atomic:
                                    edgeLabels[edge] = 'A';
                                    break;
                                case MoverType.Both:
                                    edgeLabels[edge] = 'B';
                                    break;
                                case MoverType.Left:
                                    edgeLabels[edge] = 'L';
                                    break;
                                case MoverType.Right:
                                    edgeLabels[edge] = 'R';
                                    break;
                                case MoverType.Top:
                                    edgeLabels[edge] = 'Y';
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
                            edgeLabels[edge] = 'Y';
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
                                edgeLabels[edge] = 'B';
                            }
                            else if (isLeftMover)
                            {
                                edgeLabels[edge] = 'L';
                            }
                            else if (isRightMover)
                            {
                                edgeLabels[edge] = 'R';
                            }
                            else
                            {
                                Debug.Assert(numAtomicActions == 1);
                                edgeLabels[edge] = 'A';
                            }
                        }
                    }
                    else if (cmd is YieldCmd)
                    {
                        edgeLabels[edge] = 'Y';
                    }
                    else
                    {
                        edgeLabels[edge] = 'P';
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
                string label = "P";
                switch (e.Item2)
                {
                    case 'P': label = "P"; break;
                    case 'Y': label = "Y"; break;
                    case 'B': label = "B"; break;
                    case 'R': label = "R"; break;
                    case 'L': label = "L"; break;
                    case 'A': label = "A"; break;
                    default: Debug.Assert(false); break;
                }
                s.AppendLine("  \"" + e.Item1.ToString() + "\" -- " + label + " --> " + "  \"" + e.Item3.ToString() + "\";");
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
