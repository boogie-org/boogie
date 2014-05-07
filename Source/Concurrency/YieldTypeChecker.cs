#if QED

using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Automata;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    class YieldTypeChecker
    {
        static CharSetSolver yieldTypeCheckerAutomatonSolver;
        static Automaton<BvSet> yieldTypeCheckerAutomaton;
        static List<Tuple<int, int, int>> yieldTypeCheckerAutomatonEdges;
        static YieldTypeChecker()
        {
            yieldTypeCheckerAutomatonSolver = new CharSetSolver(BitWidth.BV7);
            yieldTypeCheckerAutomaton = yieldTypeCheckerAutomatonSolver.ReadFromRanges(3, new int[] { 0 },
                new int[][] {
                    new int[] {3, 'P', 'P', 3 },
                    new int[] {3, 'Y', 'Y', 0 },
                    new int[] {3, 'Y', 'Y', 1 },
                    new int[] {3, 'Y', 'Y', 2 },
                    new int[] {0, 'P', 'P', 0 },
                    new int[] {0, 'Y', 'Y', 0 },
                    new int[] {0, 'Y', 'Y', 1 },
                    new int[] {0, 'Y', 'Y', 2 },
                    new int[] {1, 'P', 'P', 1 },
                    new int[] {1, 'R', 'R', 1 },
                    new int[] {1, 'B', 'B', 1 },
                    new int[] {1, 'Y', 'Y', 1 },
                    new int[] {1, 'Y', 'Y', 0 },
                    new int[] {1, 'A', 'A', 2 },
                    new int[] {1, 'P', 'P', 2 },
                    new int[] {1, 'R', 'R', 2 },
                    new int[] {1, 'B', 'B', 2 },
                    new int[] {1, 'Y', 'Y', 2 },
                    new int[] {2, 'L', 'L', 2 },
                    new int[] {2, 'B', 'B', 2 },
                    new int[] {2, 'P', 'P', 2 },
                    new int[] {2, 'Y', 'Y', 2 },
                    new int[] {2, 'Y', 'Y', 1 },
                    new int[] {2, 'Y', 'Y', 0 },
                });
            // uncomment the following line to visualize the spec automaton
            // yieldTypeCheckerAutomatonSolver.ShowGraph(yieldTypeCheckerAutomaton, "yieldTypeCheckerAutomaton.dgml");

            yieldTypeCheckerAutomatonEdges = new List<Tuple<int, int, int>>();
            AddEdge(0, 'P', 0);
            AddEdge(0, 'Y', 0);
            AddEdge(0, 'Y', 1);
            AddEdge(0, 'Y', 2);
            AddEdge(1, 'P', 1);
            AddEdge(1, 'R', 1);
            AddEdge(1, 'B', 1);
            AddEdge(1, 'Y', 1);
            AddEdge(1, 'Y', 0);
            AddEdge(1, 'A', 2);
            AddEdge(1, 'P', 2);
            AddEdge(1, 'R', 2);
            AddEdge(1, 'B', 2);
            AddEdge(1, 'Y', 2);
            AddEdge(2, 'L', 2);
            AddEdge(2, 'B', 2);
            AddEdge(2, 'P', 2);
            AddEdge(2, 'Y', 2);
            AddEdge(2, 'Y', 1);
            AddEdge(2, 'Y', 0);
        }
        private static void AddEdge(int source, int label, int dest)
        {
            yieldTypeCheckerAutomatonEdges.Add(new Tuple<int, int, int>(source, label, dest));
        }

        private void IsYieldTypeSafe()
        {
            List<int[]> transitions = new List<int[]>();
            foreach (Tuple<int, int> e in edgeLabels.Keys)
            {
                int label = edgeLabels[e];
                int[] transition = new int[4];
                transition[0] = e.Item1;
                transition[1] = label;
                transition[2] = label;
                transition[3] = e.Item2;
                transitions.Add(transition);
            }

            int dummyInitial = stateCounter;
            foreach (Tuple<int, int> e in edgeLabels.Keys)
            {
                if (initialStates.Contains(e.Item1))
                {
                    int[] transition = new int[4];
                    transition[0] = dummyInitial;
                    transition[1] = edgeLabels[e];
                    transition[2] = edgeLabels[e];
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
            }

            List<Tuple<int, int, int>> implEdges = new List<Tuple<int, int, int>>();
            foreach (int[] transition in transitions)
            {
                implEdges.Add(new Tuple<int, int, int>(transition[0], transition[1], transition[3]));
            }
            Dictionary<int, HashSet<int>> initialConstraints = new Dictionary<int, HashSet<int>>();
            initialConstraints[dummyInitial] = new HashSet<int>(new int[] {0});
            foreach (var finalState in finalStates)
            {
                initialConstraints[finalState] = new HashSet<int>(new int[] { 0 });
            }
            foreach (Block block in loopHeaders)
            {
                if (!IsTerminatingLoopHeader(block))
                {
                    initialConstraints[absyToNode[block]] = new HashSet<int>(new int[] { 0, 1 });
                }
            }

            Automaton<BvSet> implAutomaton = yieldTypeCheckerAutomatonSolver.ReadFromRanges(dummyInitial, finalStates.ToArray(), transitions);
            // yieldTypeCheckerAutomatonSolver.SaveAsDgml(implAutomaton, string.Format("{0}.dgml", impl.Name));
            List<BvSet> witnessSet;
            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                           implAutomaton,
                                                           yieldTypeCheckerAutomaton,
                                                           0,
                                                           yieldTypeCheckerAutomatonSolver,
                                                           out witnessSet);
            var diffAutomaton = implAutomaton.Minus(yieldTypeCheckerAutomaton, yieldTypeCheckerAutomatonSolver);
            if (isNonEmpty)
            {
                moverTypeChecker.Error(impl, PrintErrorTrace(diffAutomaton));
            }

            SimulationRelation<int, int, int> x = new SimulationRelation<int, int, int>(implEdges, yieldTypeCheckerAutomatonEdges, initialConstraints);
            Dictionary<int, HashSet<int>> simulationRelation = x.ComputeSimulationRelation();
            foreach (Block block in loopHeaders)
            {
                if (simulationRelation[absyToNode[block]].Count == 0)
                {
                    IToken tok = block.tok;
                    moverTypeChecker.Error(impl, string.Format("Loop at {0}({1}, {2}) not simulated appropriately at phase {3}\n", tok.filename, tok.line, tok.col, currPhaseNum));
                    yieldTypeCheckerAutomatonSolver.SaveAsDgml(implAutomaton, string.Format("{0}_{1}.dgml", impl.Name, currPhaseNum));
                }
            }
        }

        private static bool IsTerminatingLoopHeader(Block block)
        {
            foreach (Cmd cmd in block.Cmds)
            {
                AssertCmd assertCmd = cmd as AssertCmd;
                if (assertCmd != null && QKeyValue.FindBoolAttribute(assertCmd.Attributes, "terminates"))
                {
                    return true;
                }
            }
            return false;
        }
        
        private string PrintErrorTrace(Automaton<BvSet> errorAutomaton)
        {
            String s = "\nBody of " + impl.Proc.Name + " is not yield_type_safe at phase " + currPhaseNum.ToString() + "\n";
            foreach (var move in errorAutomaton.GetMoves())
            {
                if (nodeToAbsy.ContainsKey(move.SourceState))
                {
                    IToken tok = nodeToAbsy[move.SourceState].tok;
                    s += string.Format("{0}({1}, {2})\n", tok.filename, tok.line, tok.col);
                }
            }
            return s;
        }

        public static void PerformYieldSafeCheck(MoverTypeChecker moverTypeChecker)
        {
            foreach (var decl in moverTypeChecker.program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null || !moverTypeChecker.procToActionInfo.ContainsKey(impl.Proc) || moverTypeChecker.procToActionInfo[impl.Proc].phaseNum == 0) continue;
                impl.PruneUnreachableBlocks();
                Graph<Block> implGraph = Program.GraphFromImpl(impl);
                implGraph.ComputeLoops();
                int specPhaseNum = moverTypeChecker.procToActionInfo[impl.Proc].phaseNum;
                foreach (int phaseNum in moverTypeChecker.AllPhaseNums)
                {
                    if (phaseNum > specPhaseNum) continue;
                    YieldTypeChecker executor = new YieldTypeChecker(moverTypeChecker, impl, phaseNum, implGraph.Headers);
                }
            }
        }

        int stateCounter;
        MoverTypeChecker moverTypeChecker;
        Implementation impl;
        int currPhaseNum;
        Dictionary<Absy, int> absyToNode;
        Dictionary<int, Absy> nodeToAbsy;
        HashSet<int> initialStates;
        HashSet<int> finalStates;
        Dictionary<Tuple<int, int>, int> edgeLabels;
        IEnumerable<Block> loopHeaders;

        private YieldTypeChecker(MoverTypeChecker moverTypeChecker, Implementation impl, int currPhaseNum, IEnumerable<Block> loopHeaders)
        {
            this.moverTypeChecker = moverTypeChecker;
            this.impl = impl;
            this.currPhaseNum = currPhaseNum;
            this.loopHeaders = loopHeaders;
            this.stateCounter = 0;
            this.absyToNode = new Dictionary<Absy, int>();
            this.initialStates = new HashSet<int>();
            initialStates.Add(0);
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
                            ActionInfo actionInfo = moverTypeChecker.procToActionInfo[callCmd.Proc];
                            if (currPhaseNum <= actionInfo.phaseNum)
                                edgeLabels[edge] = 'L';
                            else
                                edgeLabels[edge] = 'B';
                        }
                        else if (!moverTypeChecker.procToActionInfo.ContainsKey(callCmd.Proc))
                        {
                            edgeLabels[edge] = 'P';
                        }
                        else
                        {
                            MoverType moverType;
                            ActionInfo actionInfo = moverTypeChecker.procToActionInfo[callCmd.Proc];
                            if (actionInfo.phaseNum >= currPhaseNum)
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
                            if (moverTypeChecker.procToActionInfo[callCmd.Proc].phaseNum >= currPhaseNum)
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
                            foreach (CallCmd callCmd in parCallCmd.CallCmds)
                            {
                                ActionInfo actionInfo = moverTypeChecker.procToActionInfo[callCmd.Proc];
                                isRightMover = isRightMover && actionInfo.IsRightMover;
                                isLeftMover = isLeftMover && actionInfo.IsLeftMover;
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
                                Debug.Assert(parCallCmd.CallCmds.Count == 1);
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

        private static string PrintGraph(Implementation yTypeChecked, Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels)
        {
            var s = new StringBuilder();
            s.AppendLine("\nImplementation " + yTypeChecked.Proc.Name + " digraph G {");
            foreach (var e in graph.Edges)
                s.AppendLine("  \"" + e.Item1.ToString() + "\" -- " + edgeLabels[e] + " --> " + "  \"" + e.Item2.ToString() + "\";");
            s.AppendLine("}");
            return s.ToString();
        }
    }
}

#endif