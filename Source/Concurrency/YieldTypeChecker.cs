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
        static YieldTypeChecker()
        {
            yieldTypeCheckerAutomatonSolver = new CharSetSolver(BitWidth.BV7);
            yieldTypeCheckerAutomaton = yieldTypeCheckerAutomatonSolver.ReadFromRanges(0, new int[] { 0 },
                new int[][] {
                    new int[] {0, 'P', 'P', 0 },
                    new int[] {0, 'Y', 'Y', 0 },
                    new int[] {0, 'Y', 'Y', 1 },
                    new int[] {1, 'P', 'P', 1 },
                    new int[] {1, 'R', 'R', 1 },
                    new int[] {1, 'B', 'B', 1 },
                    new int[] {1, 'Y', 'Y', 1 },
                    new int[] {1, 'Y', 'Y', 0 },
                    new int[] {1, 'A', 'A', 2 },
                    new int[] {1, -1, -1, 2 },
                    new int[] {2, 'L', 'L', 2 },
                    new int[] {2, 'B', 'B', 2 },
                    new int[] {2, 'Y', 'Y', 1 },
                    new int[] {2, 'Y', 'Y', 0 },
                });
            // uncomment the following line to visualize the spec automaton
            // yieldTypeCheckerAutomatonSolver.ShowGraph(yieldTypeCheckerAutomaton, "yieldTypeCheckerAutomaton.dgml");
        }

        public void IsYieldTypeSafe(Automaton<BvSet> implAutomaton)
        {
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
        }

        public string PrintErrorTrace(Automaton<BvSet> errorAutomaton)
        {
            String s = "\nBody of " + impl.Proc.Name + " is not yield_type_safe at phase " + currPhaseNum.ToString() + "\n";
            foreach (var move in errorAutomaton.GetMoves())
            {
                IToken tok = nodeToAbsy[move.SourceState].tok;
                s += string.Format("{0}({1}, {2})\n", tok.filename, tok.line, tok.col);
            }
            return s;
        }

        public static void PerformYieldSafeCheck(MoverTypeChecker moverTypeChecker)
        {
            foreach (int yTypeCheckCurrentPhaseNum in moverTypeChecker.allPhaseNums)
            {
                foreach (var decl in moverTypeChecker.program.TopLevelDeclarations)
                {
                    Implementation impl = decl as Implementation;
                    if (impl == null) continue;
                    int phaseNumSpecImpl = moverTypeChecker.FindPhaseNumber(impl.Proc);
                    if (yTypeCheckCurrentPhaseNum > phaseNumSpecImpl) continue;

                    YieldTypeChecker executor = new YieldTypeChecker(moverTypeChecker, impl, yTypeCheckCurrentPhaseNum);
                }
            }
        }

        public MoverType FindMoverType(Procedure proc)
        {
            if (!moverTypeChecker.procToActionInfo.ContainsKey(proc))
                return MoverType.Top;
            ActionInfo actionInfo = moverTypeChecker.procToActionInfo[proc];
            if (actionInfo.phaseNum >= currPhaseNum)
                return MoverType.Top;
            return actionInfo.moverType;
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

        public YieldTypeChecker(MoverTypeChecker moverTypeChecker, Implementation impl, int currPhaseNum)
        {
            this.moverTypeChecker = moverTypeChecker;
            this.impl = impl;
            this.currPhaseNum = currPhaseNum;
            this.stateCounter = 0;
            this.absyToNode = new Dictionary<Absy, int>();
            this.initialStates = new HashSet<int>();
            initialStates.Add(0);
            this.finalStates = new HashSet<int>();
            this.edgeLabels = new Dictionary<Tuple<int, int>, int>(); 
            
            foreach (Block block in impl.Blocks)
            {
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
                GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                if (gotoCmd == null) continue;
                foreach (Block successor in gotoCmd.labelTargets)
                {
                    Absy successorEntry = successor.Cmds.Count == 0 ? (Absy)successor.TransferCmd : (Absy)successor.Cmds[0];
                    edgeLabels[new Tuple<int, int>(absyToNode[block.TransferCmd], absyToNode[successorEntry])] = 'Q';
                }
            }

            this.nodeToAbsy = new Dictionary<int, Absy>();
            foreach (KeyValuePair<Absy, int> state in absyToNode)
            {
                this.nodeToAbsy[state.Value] = state.Key;
            }

            Graph<int> graph = ComputeGraph();

            // Compute all edges that can reach yield or exit
            HashSet<int> targetStates = new HashSet<int>(finalStates);
            foreach (Tuple<int, int> edge in edgeLabels.Keys)
            {
                if (edgeLabels[edge] == 'Y')
                {
                    targetStates.Add(edge.Item1);
                }
            }
            HashSet<Tuple<int, int>> backwardReachableEdges = CollectBackwardReachableEdges(graph, targetStates);
            HashSet<Tuple<int, int>> edges = new HashSet<Tuple<int, int>>(edgeLabels.Keys);
            foreach (Tuple<int, int> edge in edges)
            {
                int label = edgeLabels[edge];
                if (label == 'A' || label == 'L')
                {
                    if (!backwardReachableEdges.Contains(edge))
                    {
                        moverTypeChecker.Error(impl, "Error message TBD");
                    }
                }
                else if (label == 'B')
                {
                    if (!backwardReachableEdges.Contains(edge))
                    {
                        edgeLabels[edge] = 'R';
                    }
                }
                else if (label == 'Q')
                {
                    if (!backwardReachableEdges.Contains(edge))
                    {
                        edgeLabels[edge] = 'P';
                    }
                    else
                    {
                        edgeLabels[edge] = -1;
                    }
                }
            }
            Automaton<BvSet> implYieldTypeSafeCheckAut = BuildAutomatonYieldSafe();
            IsYieldTypeSafe(implYieldTypeSafeCheckAut);
        }

        private Graph<int> ComputeGraph()
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
                            edgeLabels[edge] = 'Q';
                        }
                        else
                        {
                            switch (FindMoverType(callCmd.Proc))
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
                                    finalStates.Add(curr);
                                    initialStates.Add(next);
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
                            int phaseSpecCallee = moverTypeChecker.FindPhaseNumber(callCmd.Proc);
                            if (phaseSpecCallee >= currPhaseNum)
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
                                Debug.Assert(false);
                            }
                        }
                    }
                    else if (cmd is YieldCmd)
                    {
                        edgeLabels[edge] = 'Y';
                    }
                    else if (cmd is AssumeCmd)
                    {
                        if (AccessesGlobals(cmd))
                        {
                            finalStates.Add(curr);
                            initialStates.Add(next);
                        }
                        else
                        {
                            edgeLabels[edge] = 'P';
                        }
                    }
                    else if (cmd is AssertCmd)
                    {
                        edgeLabels[edge] = 'Q';
                    }
                    else if (cmd is AssignCmd || cmd is HavocCmd)
                    {
                        if (AccessesGlobals(cmd))
                        {
                            finalStates.Add(curr);
                            initialStates.Add(next);
                        }
                        else
                        {
                            edgeLabels[edge] = 'Q';
                        }
                    }
                    else
                    {
                        edgeLabels[edge] = 'Q';
                    }
                }
            }
            Graph<int> graph = new Graph<int>(new HashSet<Tuple<int, int>>(edgeLabels.Keys));
            for (int i = 0; i < stateCounter; i++)
            {
                graph.AddSource(i);
            }
            return graph;
        }

        private static bool AccessesGlobals(Cmd cmd)
        {
            VariableCollector collector = new VariableCollector();
            collector.Visit(cmd);
            return collector.usedVars.Any(x => x is GlobalVariable);
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

        private static HashSet<Tuple<int, int>> CollectBackwardReachableEdges(Graph<int> graph, HashSet<int> targets)
        {
            HashSet<Tuple<int, int>> edgesReachable = new HashSet<Tuple<int, int>>(); 
            HashSet<int> gray = new HashSet<int>();
            Queue<int> frontier = new Queue<int>();
            foreach (int v in targets)
            {
                gray.Add(v);
                frontier.Enqueue(v);
            }
            while (frontier.Count > 0)
            {
                int v = frontier.Dequeue();
                foreach (int u in graph.Predecessors(v))
                {
                    edgesReachable.Add(new Tuple<int, int>(u, v));
                    if (!gray.Contains(u))
                    {
                        gray.Add(u);
                        frontier.Enqueue(u);
                    }
                }
            }
            return edgesReachable;
        }

        private Automaton<BvSet> BuildAutomatonYieldSafe()
        {
            List<int[]> transitions = new List<int[]>();
            foreach (Tuple<int, int> e in edgeLabels.Keys)
            {
                int label = edgeLabels[e];
                Debug.Assert(label != 'Q');
                int[] transition = new int[4];
                transition[0] = e.Item1;
                transition[1] = label;
                transition[2] = label;
                transition[3] = e.Item2;
                transitions.Add(transition);
            }

            int dummyInitial = stateCounter;
            foreach (int s in initialStates)
            {
                int[] transition = new int[4];
                transition[0] = dummyInitial;
                transition[1] = -1;
                transition[2] = -1;
                transition[3] = s;
                transitions.Add(transition);
            }

            Automaton<BvSet> yieldTypeCheckAutomaton = yieldTypeCheckerAutomatonSolver.ReadFromRanges(dummyInitial, finalStates.ToArray(), transitions);
            return yieldTypeCheckAutomaton;
        }
    }
}

#endif