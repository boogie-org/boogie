#if QED

#define DEBUG

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

namespace Microsoft.Boogie
{
    using Set = GSet<object>;

    class YieldTypeChecker
    {
        static CharSetSolver yieldCheckerAutomatonSolver;
        static string yieldReachabilityOptCheckerRegex = @"^1*([D]+([571])*A?([97])*)*$";
        static Automaton<BvSet> yieldReachabilityOptCheckerAutomaton;
        static Automaton<BvSet> minimizedReachabilityOptCheckerAutomaton;
        static Automaton<BvSet> yieldTypeSafeCheckerAutomaton;
        static Automaton<BvSet> minimizedYieldTypeSafeCheckerAutomaton;

        static YieldTypeChecker()
        {
            yieldCheckerAutomatonSolver = new CharSetSolver(BitWidth.BV7);
            yieldReachabilityOptCheckerAutomaton =
           Automaton<BvSet>.MkProduct(yieldCheckerAutomatonSolver.Convert(yieldReachabilityOptCheckerRegex),
                                          yieldCheckerAutomatonSolver.Convert(@"^[1-9A-D]*$"), // result of product with this Automaton provides us an automaton that has (*) existence alphanum chars in our property automaton 
                                          yieldCheckerAutomatonSolver);
            minimizedReachabilityOptCheckerAutomaton = yieldReachabilityOptCheckerAutomaton.Determinize(yieldCheckerAutomatonSolver).Minimize(yieldCheckerAutomatonSolver);
            yieldTypeSafeCheckerAutomaton = yieldCheckerAutomatonSolver.ReadFromRanges(
                                            0,
                                           new int[] { 0, 2 },
                                           new int[][] { 
                                               // self loop on state 0 transitions
                                                new int[] {0,51,51,0}, // Q
                                                new int[] {0,68,68,0},// Y
                                                new int[] {0,49,49,0},
                                               //0 to 1 transitions
                                                new int[] {0,65,65,1},//A
                                                new int[] {0,55,55,1}, //B
                                                new int[] {0,57,57,1},//L
                                                new int[] {0,53,53,1}, //R
                                               //self loop on state 1 transitions
                                                new int[] {1,65,65,1},//A 
                                                new int[] {1,55,55,1},//B
                                                new int[] {1,57,57,1},//L
                                                new int[] {1,53,53,1},//R
                                                new int[] {1,49,49,1},//P
                                                new int[] {1,51,51,1},//Q
                                                //1 to 2 transition
                                                new int[] {1,68,68,2}, //Y
                                                //self loop on state 2 transitions
                                                new int[] {2,65,65,2},//A
                                                new int[] {2,55,55,2},//B
                                                new int[] {2,57,57,2},//L
                                                new int[] {2,53,53,2},//R
                                                new int[] {2,49,49,2},//P
                                                new int[] {2,68,68,2},//Y 
                                                new int[] {2,51,51,2},//Q
                                           });


            minimizedYieldTypeSafeCheckerAutomaton = yieldTypeSafeCheckerAutomaton.Determinize(yieldCheckerAutomatonSolver).Minimize(yieldCheckerAutomatonSolver);

#if !DEBUG
            yieldCheckerAutomatonSolver.ShowGraph(minimizedReachabilityOptCheckerAutomaton, "minimizedReachabilityPropertyAutomaton.dgml");
            yieldCheckerAutomatonSolver.ShowGraph(minimizedYieldTypeSafeCheckerAutomaton, "minimizedTypeSafePropertyAutomaton.dgml");
#endif
        }

        private static Tuple<Automaton<BvSet>, bool> IsYieldReachabilitySafe(Automaton<BvSet> implReachabilityCheckAutomaton)
        {
            List<BvSet> witnessSet;
            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                          implReachabilityCheckAutomaton,
                                                          yieldReachabilityOptCheckerAutomaton,
                                                          0,
                                                          yieldCheckerAutomatonSolver,
                                                          out witnessSet);

            var diffAutomaton = implReachabilityCheckAutomaton.Minus(yieldReachabilityOptCheckerAutomaton, yieldCheckerAutomatonSolver);
            return new Tuple<Automaton<BvSet>, bool>(diffAutomaton, !isNonEmpty);
        }

        private static Tuple<Automaton<BvSet>, bool> IsYieldTypeSafe(Automaton<BvSet> implTypeSafeCheckAutomaton)
        {
            List<BvSet> witnessSet;
            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                           implTypeSafeCheckAutomaton,
                                                           yieldTypeSafeCheckerAutomaton,
                                                           0,
                                                           yieldCheckerAutomatonSolver,
                                                           out witnessSet);
            var diffAutomaton = implTypeSafeCheckAutomaton.Minus(yieldTypeSafeCheckerAutomaton, yieldCheckerAutomatonSolver);
            return new Tuple<Automaton<BvSet>, bool>(diffAutomaton, !isNonEmpty);
        }

        private static void/*string*/ PrintErrorTrace(Dictionary<int, Absy> cmds, Automaton<BvSet> errorAutomaton, Implementation yTypeChecked)
        {
            //   var s = new StringBuilder();
            String s = "";

            s += "\nError Trace " + yTypeChecked.Proc.Name + "{" + "\n";
            foreach (var move in errorAutomaton.GetMoves())
            {
                s += " [Line :" + cmds[move.SourceState].Line.ToString() + "] , [Cmd :" + cmds[move.SourceState].ToString() + " ]" + " \n";
            }
            s += "}";

            Console.WriteLine(s);
            // return s;
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

                    Tuple<Tuple<Dictionary<int, Absy>, Automaton<BvSet>>, Tuple<Dictionary<int, Absy>, Automaton<BvSet>>> yieldCheckAutomatons =
                             YieldTypeCheckExecutor.YieldTypeCheckAutomaton(impl, phaseNumSpecImpl, yTypeCheckCurrentPhaseNum, moverTypeChecker);

                    Tuple<Automaton<BvSet>, bool> isYieldReachable = IsYieldReachabilitySafe(yieldCheckAutomatons.Item2.Item2);
                    Tuple<Automaton<BvSet>, bool> isYieldTypeSafe = IsYieldTypeSafe(yieldCheckAutomatons.Item1.Item2);

                    Dictionary<int, Absy> isYieldTypeSafeCmds = yieldCheckAutomatons.Item1.Item1;
                    Dictionary<int, Absy> isYieldReachableSafeCmds = yieldCheckAutomatons.Item2.Item1;

                    if (!isYieldTypeSafe.Item2)
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_type_safe at phase " + yTypeCheckCurrentPhaseNum.ToString() + "\n");
                        PrintErrorTrace(isYieldTypeSafeCmds, isYieldTypeSafe.Item1, impl);
                    }
                    if (!isYieldReachable.Item2)
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_reachable_safe at phase " + yTypeCheckCurrentPhaseNum.ToString() + "\n");
                        PrintErrorTrace(isYieldReachableSafeCmds, isYieldReachable.Item1, impl);
                    }
                }
            }
        }
    }

    static class YieldTypeCheckExecutor
    {
        static int stateCounter;

        public static Tuple<Tuple<Dictionary<int, Absy>, Automaton<BvSet>>, Tuple<Dictionary<int, Absy>, Automaton<BvSet>>>
            YieldTypeCheckAutomaton(Implementation yTypeChecked, int specPhaseNumImpl, int yTypeCheckCurrentPhaseNum, MoverTypeChecker moverTypeChecker)
        {
            CharSetSolver solver = new CharSetSolver(BitWidth.BV7);
            Dictionary<Tuple<int, int>, string> edgeLabels = new Dictionary<Tuple<int, int>, string>(); // Tuple<int,int> --> "Y" : State(k) --Y--> State(k+1)
            HashSet<int> finalStates = new HashSet<int>();
            HashSet<int> initialStates = new HashSet<int>();
            stateCounter = 0;
            initialStates.Add(stateCounter); // First state is added to initial states
            Dictionary<Absy, int> abysToNode = CreateStateNumbers(yTypeChecked);
            Graph<int> graph = BuildAutomatonGraph(yTypeChecked, yTypeCheckCurrentPhaseNum, abysToNode, edgeLabels, finalStates, initialStates, moverTypeChecker); // build component of graph for a phase interval            

            //Buradayim
            Automaton<BvSet> implYieldTypeSafeCheckAut = BuildAutomatonYieldSafe(graph, initialStates, finalStates, edgeLabels, solver);
            Dictionary<int, Absy> nodeToAbysYieldTypeSafe = new Dictionary<int, Absy>();
            foreach (KeyValuePair<Absy, int> state in abysToNode)
            {
                nodeToAbysYieldTypeSafe[state.Value] = state.Key;
            }
            Tuple<Dictionary<int, Absy>, Automaton<BvSet>> implYieldTypeSafeCheckAutomaton = new Tuple<Dictionary<int, Absy>, Automaton<BvSet>>(nodeToAbysYieldTypeSafe, implYieldTypeSafeCheckAut);
            Automaton<BvSet> implYieldReachCheckAut = BuildOptAutomatonYieldReachSafe(yTypeChecked, graph, edgeLabels, initialStates, finalStates, moverTypeChecker, solver);
            Dictionary<int, Absy> nodeToAbysYieldReachSafe = new Dictionary<int, Absy>();
            foreach (KeyValuePair<Absy, int> state in abysToNode)
            {
                nodeToAbysYieldReachSafe[state.Value] = state.Key;
            }
            Tuple<Dictionary<int, Absy>, Automaton<BvSet>> implYieldReachCheckAutomaton = new Tuple<Dictionary<int, Absy>, Automaton<BvSet>>(nodeToAbysYieldReachSafe, implYieldReachCheckAut);
            Tuple<Tuple<Dictionary<int, Absy>, Automaton<BvSet>>, Tuple<Dictionary<int, Absy>, Automaton<BvSet>>> yieldCheckImplAutomaton =
                new Tuple<Tuple<Dictionary<int, Absy>, Automaton<BvSet>>, Tuple<Dictionary<int, Absy>, Automaton<BvSet>>>(implYieldTypeSafeCheckAutomaton, implYieldReachCheckAutomaton);
            return yieldCheckImplAutomaton;
        }

        public static Dictionary<Absy, int> CreateStateNumbers(Implementation yTypeChecked)
        {
            Dictionary<Absy, int> abysToNodeNo = new Dictionary<Absy, int>();
            foreach (Block block in yTypeChecked.Blocks)
            {
                foreach (Cmd cmd in block.Cmds)
                {
                    if (IsAsyncCallCmd(cmd)) continue;
                    if (cmd is ParCallCmd)
                    {
                        ParCallCmd calle = cmd as ParCallCmd;
                        for (int i = 0; i < calle.CallCmds.Count; i++)
                        {
                            abysToNodeNo[calle.CallCmds[i]] = stateCounter;
                            stateCounter++;
                        }
                    }
                    else
                    {
                        abysToNodeNo[cmd] = stateCounter;
                        stateCounter++;
                    }
                }
                abysToNodeNo[block.TransferCmd] = stateCounter;
                stateCounter++;
            }
            return abysToNodeNo;
        }

        private static Graph<int> BuildAutomatonGraph(Implementation yTypeChecked, int yTypeCheckCurrentPhaseNum, Dictionary<Absy, int> abysToNode, Dictionary<Tuple<int, int>, string> edgeLabels, HashSet<int> finalStates, HashSet<int> initialStates, MoverTypeChecker moverTypeChecker)
        {
            HashSet<Tuple<int, int>> edges = new HashSet<Tuple<int, int>>();
            foreach (Block block in yTypeChecked.Blocks)
            {
                if (block.Cmds.Count >= 2)
                {
                    for (int i = 0; i < block.Cmds.Count - 1; i++)
                    {
                        //IsProper
                        if (IsProperActionCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsProperActionCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))// this is handled in else but keep this branch now
                        { // proper state transition
                            int source = abysToNode[block.Cmds[i]];
                            int dest = abysToNode[block.Cmds[i + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsProperActionCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsExitStatement(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            int source = abysToNode[block.Cmds[i]];
                            // create artificial final state
                            int dest = Math.Abs(Guid.NewGuid().GetHashCode()); // Generate unique dummy node ref: http://msdn.microsoft.com/en-us/library/system.guid(v=vs.110).aspx
                            finalStates.Add(dest);
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsProperActionCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsParallelCallCmdYield(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            int source = abysToNode[block.Cmds[i]];
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            int dest = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        else if (IsProperActionCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsSeqComposableParCallCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            int source = abysToNode[block.Cmds[i]];
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            int dest = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        // IsCallCmdsExit
                        else if (IsExitStatement(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsProperActionCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        { // current cmd exit , next cmd will be put as initial state
                            initialStates.Add(abysToNode[block.Cmds[i + 1]]);
                        }
                        else if (IsExitStatement(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsExitStatement(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            continue;
                        }
                        else if (IsExitStatement(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsParallelCallCmdYield(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            // Add state number CallCmd of ParallelCmd
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            initialStates.Add(abysToNode[nextCmd.CallCmds[0]]);
                        }
                        else if (IsExitStatement(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsSeqComposableParCallCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            // Add state number CallCmd of ParallelCmd
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            initialStates.Add(abysToNode[nextCmd.CallCmds[0]]);

                        }
                        // ParallelCallCmdYield
                        else if (IsParallelCallCmdYield(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsParallelCallCmdYield(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            int source = abysToNode[currentCmd.CallCmds[0]];
                            int dest = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsParallelCallCmdYield(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsSeqComposableParCallCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            int source = abysToNode[currentCmd.CallCmds[0]];
                            int dest = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsParallelCallCmdYield(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsExitStatement(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            //create dummy state as next state
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            int source = abysToNode[currentCmd.CallCmds[0]];
                            int dest = Math.Abs(Guid.NewGuid().GetHashCode()); // Generate unique dummy node 
                            finalStates.Add(dest);
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsParallelCallCmdYield(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsProperActionCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            int source = abysToNode[currentCmd.CallCmds[0]];
                            int dest = abysToNode[block.Cmds[i + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        //SeqComposable Parallel Cmd
                        else if (IsSeqComposableParCallCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsSeqComposableParCallCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                            {
                                int source = abysToNode[currentCmd.CallCmds[j]];
                                int dest = abysToNode[currentCmd.CallCmds[j + 1]];
                                Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                                edges.Add(edge);
                                edgeLabels.Add(edge, GetEdgeType(block.Cmds[j]));
                            }
                            // Peelout last iteration
                            int sourceBtwCalls = abysToNode[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                            int destBtwCalls = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                            edges.Add(edgeBtw);
                            edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));
                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsParallelCallCmdYield(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                            {
                                int source = abysToNode[currentCmd.CallCmds[j]];
                                int dest = abysToNode[currentCmd.CallCmds[j + 1]];
                                Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                                edges.Add(edge);
                                edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                            }
                            // Peelout last iteration
                            int sourceBtwCalls = abysToNode[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                            int destBtwCalls = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                            edges.Add(edgeBtw);
                            edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));
                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsExitStatement(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                            {
                                int source = abysToNode[currentCmd.CallCmds[j]];
                                int dest = abysToNode[currentCmd.CallCmds[j + 1]];
                                Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                                edges.Add(edge);
                                edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                            }
                            // Peelout last iteration
                            int sourceBtwCalls = abysToNode[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                            int destBtwCalls = Math.Abs(Guid.NewGuid().GetHashCode()); // Generate unique dummy node 
                            finalStates.Add(destBtwCalls);
                            Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                            edges.Add(edgeBtw);
                            edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));

                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum, moverTypeChecker) && IsProperActionCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;

                            for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                            {
                                int source = abysToNode[currentCmd.CallCmds[j]];
                                int dest = abysToNode[currentCmd.CallCmds[j + 1]];
                                Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                                edges.Add(edge);
                                edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                            }
                            // Peelout last iteration
                            int sourceBtwCalls = abysToNode[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                            int destBtwCalls = abysToNode[block.Cmds[i + 1]]; // Generate unique dummy node 
                            Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                            edges.Add(edgeBtw);
                            edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));
                        }
                    }
                    if (IsExitStatement(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                    { // put b.TransferCmd into initial states
                        initialStates.Add(abysToNode[block.TransferCmd]);
                    }
                    else if (IsParallelCallCmdYield(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                    {
                        ParCallCmd currentCmd = block.Cmds[block.Cmds.Count - 1] as ParCallCmd;
                        int source = abysToNode[currentCmd.CallCmds[0]];
                        int dest = abysToNode[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[block.Cmds.Count - 1]));
                    }
                    else if (IsSeqComposableParCallCmd(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                    {
                        ParCallCmd currentCmd = block.Cmds[block.Cmds.Count - 1] as ParCallCmd;
                        for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                        {
                            int source = abysToNode[currentCmd.CallCmds[j]];
                            int dest = abysToNode[currentCmd.CallCmds[j + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                        }

                        int sourceBtwCalls = abysToNode[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                        int destBtwCalls = abysToNode[block.TransferCmd]; // Generate unique dummy node 
                        Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                        edges.Add(edgeBtw);
                        edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));

                    }
                    else if (IsProperActionCmd(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                    {
                        // proper transition to state before transfer command
                        int source = abysToNode[block.Cmds[block.Cmds.Count - 1]];
                        int dest = abysToNode[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[block.Cmds.Count - 1]));
                    }
                }
                else if (block.Cmds.Count == 1)
                {
                    if (IsExitStatement(block.Cmds[0], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                    { // put b.TransferCmd into initial states
                        initialStates.Add(abysToNode[block.TransferCmd]);
                    }
                    else if (IsProperActionCmd(block.Cmds[0], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                    { // proper transition to state before transfer command
                        int source = abysToNode[block.Cmds[0]];
                        int dest = abysToNode[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[0]));
                    }
                    else if (IsParallelCallCmdYield(block.Cmds[0], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                    {
                        ParCallCmd currentCmd = block.Cmds[0] as ParCallCmd;
                        int source = abysToNode[currentCmd.CallCmds[0]];
                        int dest = abysToNode[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[0]));
                    }
                    else if (IsSeqComposableParCallCmd(block.Cmds[0], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                    {
                        ParCallCmd currentCmd = block.Cmds[0] as ParCallCmd;
                        for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                        {
                            int source = abysToNode[currentCmd.CallCmds[j]];
                            int dest = abysToNode[currentCmd.CallCmds[j + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                        }

                        int sourceBtwCalls = abysToNode[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                        int destBtwCalls = abysToNode[block.TransferCmd]; // Generate unique dummy node 
                        Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                        edges.Add(edgeBtw);
                        edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));

                    }
                }
                else if (block.Cmds.Count == 0)
                {// Target block Entry state will be fetched
                }
                // Handle
                HashSet<int> targetBlockEntryStates = GetStateOfTargetBlock(block.TransferCmd, yTypeCheckCurrentPhaseNum, abysToNode, finalStates, moverTypeChecker);
                foreach (int entryState in targetBlockEntryStates)
                {
                    int source = abysToNode[block.TransferCmd];
                    Tuple<int, int> transferEdge = new Tuple<int, int>(source, entryState);
                    edges.Add(transferEdge);
                    edgeLabels.Add(transferEdge, "E");
                }
            }
            Graph<int> automatonGraphOfImplPerPhase = new Graph<int>(edges);
            return automatonGraphOfImplPerPhase;
        }

        private static HashSet<int> GetStateOfTargetBlock(TransferCmd tc, int yTypeCheckCurrentPhaseNum, Dictionary<Absy, int> abysToNode, HashSet<int> finalStates, MoverTypeChecker moverTypeChecker)
        {
            HashSet<int> targetBlockEntryStates = new HashSet<int>();
            if (tc is ReturnCmd)
            {
                ReturnCmd returnCmd = tc as ReturnCmd;
                int source = abysToNode[tc];
                finalStates.Add(source);
            }
            else if (tc is GotoCmd)
            {
                GotoCmd transferCmd = tc as GotoCmd;
                foreach (Block block in transferCmd.labelTargets)
                {
                    if (block.Cmds.Count == 0)
                    {
                        targetBlockEntryStates.Add(abysToNode[block.TransferCmd]); //Target block is empty. Add state of target block's transfer command (Goto or Return) 
                    }
                    else if (block.Cmds.Count >= 1)
                    {
                        if (IsExitStatement(block.Cmds[0], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            int targetState = Math.Abs(Guid.NewGuid().GetHashCode());
                            finalStates.Add(targetState);
                            targetBlockEntryStates.Add(targetState);
                        }
                        else if (IsProperActionCmd(block.Cmds[0], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            targetBlockEntryStates.Add(abysToNode[block.Cmds[0]]);
                        }
                        else if (IsParallelCallCmdYield(block.Cmds[0], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd targetCmd = block.Cmds[0] as ParCallCmd;
                            targetBlockEntryStates.Add(abysToNode[targetCmd.CallCmds[0]]);
                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[0], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                        {
                            ParCallCmd targetCmd = block.Cmds[0] as ParCallCmd;
                            targetBlockEntryStates.Add(abysToNode[targetCmd.CallCmds[0]]);
                        }
                        else if (IsAsyncCallCmd(block.Cmds[0]))
                        {
                            if (block.Cmds.Count == 1)
                            {
                                targetBlockEntryStates.Add(abysToNode[block.TransferCmd]);
                            }
                            else if (block.Cmds.Count > 1)
                            {
                                int existsNonAsync;
                                for (existsNonAsync = 0; existsNonAsync < block.Cmds.Count; existsNonAsync++)
                                {
                                    if (IsAsyncCallCmd(block.Cmds[existsNonAsync])) continue;
                                    else if (IsParallelCallCmdYield(block.Cmds[existsNonAsync], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                                    {
                                        ParCallCmd targetCmd = block.Cmds[existsNonAsync] as ParCallCmd;
                                        targetBlockEntryStates.Add(abysToNode[targetCmd.CallCmds[0]]);
                                        break;
                                    }
                                    else if (IsSeqComposableParCallCmd(block.Cmds[existsNonAsync], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                                    {
                                        ParCallCmd targetCmd = block.Cmds[existsNonAsync] as ParCallCmd;
                                        targetBlockEntryStates.Add(abysToNode[targetCmd.CallCmds[0]]);
                                        break;

                                    }
                                    else if (IsExitStatement(block.Cmds[existsNonAsync], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                                    {
                                        int targetState = Math.Abs(Guid.NewGuid().GetHashCode());
                                        finalStates.Add(targetState);
                                        targetBlockEntryStates.Add(targetState);
                                        break;
                                    }
                                    else if (IsExitStatement(block.Cmds[existsNonAsync], yTypeCheckCurrentPhaseNum, moverTypeChecker))
                                    {
                                        targetBlockEntryStates.Add(abysToNode[block.Cmds[existsNonAsync]]);
                                        break;
                                    }
                                }
                                if (existsNonAsync == block.Cmds.Count)
                                {
                                    // put target 
                                    targetBlockEntryStates.Add(abysToNode[block.TransferCmd]); //Target block is empty. Add state of target block's transfer command (Goto or Return)
                                }
                            }
                        }
                    }
                }
            }
            return targetBlockEntryStates;
        }

        private static bool IsAccessToNonQedVar(Cmd cmd, MoverTypeChecker moverTypeChecker)
        {
            HashSet<Variable> qedGlobalVariables = moverTypeChecker.QedGlobalVariables();
            Set globalAccesOfCmd = ComputeGlobalAccesses(cmd);

            HashSet<Variable> glbAccessOfCmd = new HashSet<Variable>();
            foreach (object var in globalAccesOfCmd)
            {
                Variable v = (Variable)var;
                glbAccessOfCmd.Add(v);
            }
            if (glbAccessOfCmd.IsSubsetOf(qedGlobalVariables))
            {
                return false;
            }
            return true;
        }

        //        
        private static Set FilterGlobalVariables(Set vars)
        {
            Set globals = new Set();
            foreach (object var in vars)
            {
                if (var is GlobalVariable)
                {
                    globals.Add((GlobalVariable)var);
                }
            }
            return globals;
        }

        private static Set ComputeGlobalAccesses(Cmd cmd)
        {
            Set s = ComputeGlobalReads(cmd);
            s.AddRange(ComputeGlobalWrites(cmd));
            return s;
        }

        private static Set ComputeGlobalReads(Cmd cmd)
        {
            return FilterGlobalVariables(ComputeReads(cmd));
        }

        private static Set ComputeGlobalWrites(Cmd cmd)
        {
            return FilterGlobalVariables(ComputeWrites(cmd));
        }

        private static Set ComputeReads(Cmd cmd)
        {
            Set vars = new Set();

            if (cmd is AssertCmd)
            { // noop
                // AssertCmd assertCmd = cmd as AssertCmd;
                //assertCmd.Expr.ComputeFreeVariables(vars);  // We can ignore assert cmds
            }
            else if (cmd is AssumeCmd)
            {
                AssumeCmd assumeCmd = cmd as AssumeCmd;
                assumeCmd.Expr.ComputeFreeVariables(vars);
            }
            else if (cmd is AssignCmd)
            {
                AssignCmd assignCmd = cmd as AssignCmd;
                foreach (AssignLhs assignLhs in assignCmd.Lhss)
                {
                    if (assignLhs is MapAssignLhs)
                    {
                        MapAssignLhs mapLhs = assignLhs as MapAssignLhs;
                        foreach (Expr index in mapLhs.Indexes)
                        {
                            index.ComputeFreeVariables(vars);
                        }
                    }
                }
                foreach (Expr rhs in assignCmd.Rhss)
                {
                    rhs.ComputeFreeVariables(vars);
                }
            }

            else if (cmd is HavocCmd)
            {
                // noop
            }
            return vars;
        }
        // Discuss and remove
        private static Set ComputeWrites(Cmd cmd)
        {
            Set vars = new Set();
            if (cmd is AssertCmd)
            {
                // noop
            }
            else if (cmd is AssumeCmd)
            {
                // noop
            }
            else if (cmd is AssignCmd)
            {
                AssignCmd assignCmd = cmd as AssignCmd;
                foreach (AssignLhs assignLhs in assignCmd.Lhss)
                {
                    vars.Add(assignLhs.DeepAssignedVariable);
                }
            }
            else if (cmd is HavocCmd)
            {
                HavocCmd havocCmd = cmd as HavocCmd;
                foreach (Expr var in havocCmd.Vars) { var.ComputeFreeVariables(vars); }
            }
            return vars;
        }

        //
        private static bool IsProperActionCmd(Cmd cmd, int yTypeCheckCurrentPhaseNum, MoverTypeChecker moverTypeChecker)
        {
            if (!IsExitStatement(cmd, yTypeCheckCurrentPhaseNum, moverTypeChecker) &&
                !IsParallelCallCmdYield(cmd, yTypeCheckCurrentPhaseNum, moverTypeChecker) &&
                !IsSeqComposableParCallCmd(cmd, yTypeCheckCurrentPhaseNum, moverTypeChecker) &&
                !IsAsyncCallCmd(cmd))
            {
                return true;
            }
            return false;

        }
        private static bool IsExitStatement(Cmd cmd, int yTypeCheckCurrentPhaseNum, MoverTypeChecker moverTypeChecker)
        {
            if (IsCallCmdExitPoint(cmd, yTypeCheckCurrentPhaseNum, moverTypeChecker) || IsAccessToNonQedVar(cmd, moverTypeChecker)) { return true; }
            return false;
        }

        private static bool IsCallCmdExitPoint(Cmd cmd, int yTypeCheckCurrentPhaseNum, MoverTypeChecker moverTypeChecker)
        {
            if (cmd is CallCmd && !IsAsyncCallCmd(cmd))
            {
                CallCmd callee = cmd as CallCmd;
                int phaseSpecCallee = moverTypeChecker.FindPhaseNumber(callee.Proc);
                if (phaseSpecCallee >= yTypeCheckCurrentPhaseNum)
                {
                    return true;
                }
            }
            return false;
        }

        private static bool IsParallelCallCmdYield(Cmd cmd, int yTypeCheckCurrentPhaseNum, MoverTypeChecker moverTypeChecker)
        {
            if (cmd is ParCallCmd)
            {
                ParCallCmd callee = cmd as ParCallCmd;
                foreach (CallCmd parCallee in callee.CallCmds)
                {
                    int phaseSpecCallee = moverTypeChecker.FindPhaseNumber(parCallee.Proc);
                    if (phaseSpecCallee >= yTypeCheckCurrentPhaseNum)
                    {
                        return true;
                    }
                }
            }
            return false;
        }

        private static bool IsSeqComposableParCallCmd(Cmd cmd, int yTypeCheckCurrentPhaseNum, MoverTypeChecker moverTypeChecker)
        {
            if (cmd is ParCallCmd && !IsParallelCallCmdYield(cmd, yTypeCheckCurrentPhaseNum, moverTypeChecker)) { return true; }
            return false;
        }
        private static bool IsAsyncCallCmd(Cmd cmd)
        {
            if (cmd is CallCmd)
            {
                CallCmd calle = cmd as CallCmd;
                if (calle.IsAsync) { return true; }
            }
            return false;
        }
        private static string GetEdgeType(Cmd cmd)
        {
            if (cmd is YieldCmd)
            {
                return "Y";
            }
            else if (cmd is HavocCmd)
            {
                return "Q";
            }
            else if (cmd is AssumeCmd)
            {
                return "P";
            }
            else if (cmd is AssertCmd)
            {
                return "E";
            }

            else if (cmd is CallCmd)
            {
                CallCmd callCmd = cmd as CallCmd;
                foreach (Ensures e in callCmd.Proc.Ensures)
                {
                    int pnum;
                    MoverType actionType = MoverCheck.GetMoverType(e, out pnum);
                    if (actionType == MoverType.Atomic) return "A";
                    else if (actionType == MoverType.Both) return "B";
                    else if (actionType == MoverType.Left) return "L";
                    else if (actionType == MoverType.Right) return "R";
                    else if (actionType == MoverType.Top) continue; // Ask this to Shaz                
                }
            }
            else if (cmd is ParCallCmd) // A small trick here : While getting type of SeqCompositional_parCall_commands we pass CallCmd typed parameter
            {
                return "Y";
            }
            return "Q";
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

        private static HashSet<Tuple<int, int>> CollectEdgesReachableFromAction(Graph<int> graph, int source)
        {
            HashSet<Tuple<int, int>> edgesReachable = new HashSet<Tuple<int, int>>(); // Collect edges that are backward reachable from source vertex of yield a edge,source ---Y---> sink, in backward direction
            HashSet<int> gray = new HashSet<int>();
            HashSet<int> black = new HashSet<int>();
            HashSet<int> white = new HashSet<int>();
            // Add all vertices except s into 
            foreach (int v in graph.Nodes)
            {
                if (!v.Equals(source))
                    white.Add(v);
            }
            Queue<int> frontier = new Queue<int>(); //
            // n is given as start vertex 
            gray.Add(source);
            frontier.Enqueue(source);

            while (frontier.Count > 0)
            {
                int u = frontier.Dequeue();
                foreach (int v in graph.Successors(u))
                {
                    if (white.Contains(v) && !gray.Contains(v) && !black.Contains(v))
                    {
                        gray.Add(v);
                        frontier.Enqueue(v);
                        // Add to yielding edges
                        edgesReachable.Add(new Tuple<int, int>(u, v));
                    }
                }
                black.Add(u);
            }
            return edgesReachable;
        }

        private static void IsExitOrRetReachableFromAtomicOrLeft(Implementation yTypeChecked, Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels, HashSet<int> finalStates, MoverTypeChecker moverTypeChecker)
        {
            foreach (var e in graph.Edges)
            {
                if (edgeLabels[e] == "A" || edgeLabels[e] == "L")
                {
                    HashSet<Tuple<int, int>> edgesReachable = CollectEdgesReachableFromAction(graph, e.Item1);

                    if (!(ReachesFinalState(finalStates, edgesReachable) || ReachesYieldState(edgeLabels, edgesReachable)))
                    {
                        moverTypeChecker.Error(yTypeChecked, "Implementation Yield Reachable " + yTypeChecked.Proc.Name);
                    }
                }
            }
        }
        private static void IsExitOrReachableFromBoth(Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels, HashSet<int> finalStates)
        {
            foreach (var e in graph.Edges)
            {
                if (edgeLabels[e] == "B")
                {
                    HashSet<Tuple<int, int>> edgesReachable = CollectEdgesReachableFromAction(graph, e.Item1);
                    if (!(ReachesFinalState(finalStates, edgesReachable) || ReachesYieldState(edgeLabels, edgesReachable)))
                    {
                        edgeLabels[e] = "R";
                    }
                }
            }

        }
        private static void IsExitOrReachableFromLocal(Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels, HashSet<int> finalStates)
        {
            foreach (var e in graph.Edges)
            {
                if (edgeLabels[e] == "Q")
                {
                    HashSet<Tuple<int, int>> edgesReachable = CollectEdgesReachableFromAction(graph, e.Item1);
                    if (!(ReachesFinalState(finalStates, edgesReachable) || ReachesYieldState(edgeLabels, edgesReachable)))
                    {
                        edgeLabels[e] = "P";
                    }
                    edgeLabels[e] = "E";
                }
            }
        }
        private static bool ReachesFinalState(HashSet<int> finalStates, HashSet<Tuple<int, int>> edges)
        {

            foreach (Tuple<int, int> e in edges)
            {
                if (finalStates.Contains(e.Item1) || finalStates.Contains(e.Item2)) return true;
            }
            return false;
        }
        private static bool ReachesYieldState(Dictionary<Tuple<int, int>, string> edgeLabels, HashSet<Tuple<int, int>> edges)
        {
            foreach (var e in edges)
            {

                if (edgeLabels[e] == "Y") return true;
            }
            return false;
        }

        private static Automaton<BvSet> BuildOptAutomatonYieldReachSafe(Implementation yTypeChecked, Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels, HashSet<int> initialStates, HashSet<int> finalStates, MoverTypeChecker moverTypeChecker, CharSetSolver solver)
        {
            IsExitOrRetReachableFromAtomicOrLeft(yTypeChecked, graph, edgeLabels, finalStates, moverTypeChecker); ;
            IsExitOrReachableFromBoth(graph, edgeLabels, finalStates);
            IsExitOrReachableFromLocal(graph, edgeLabels, finalStates);
            return BuildAutomatonYieldSafe(graph, initialStates, finalStates, edgeLabels, solver);
        }

        private static int[] ComputeFinalStates(HashSet<int> finalStates)
        {
            return finalStates.ToArray();
        }
        private static int[] ComputeInitialStates(HashSet<int> initialStates)
        {
            return initialStates.ToArray();
        }

        private static Automaton<BvSet> BuildAutomatonYieldSafe(Graph<int> graph, HashSet<int> initialStates, HashSet<int> finalStates, Dictionary<Tuple<int, int>, string> edgeLabels, CharSetSolver solver)
        {
            List<int[]> transitions = new List<int[]>();
            foreach (Tuple<int, int> e in graph.Edges)
            {
                if (edgeLabels[e] == "Q")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 51; // ASCII 3
                    transition[2] = 51;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "P")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 49; // ASCII 1
                    transition[2] = 49;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "B")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 55; // ASCII 7
                    transition[2] = 55;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "R")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 53; // ASCII 5
                    transition[2] = 53;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "L")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 57; // ASCII 9
                    transition[2] = 57;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "A")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 65; // ASCII A
                    transition[2] = 65;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "Y")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 68; // ASCII D
                    transition[2] = 68;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "E")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = -1;
                    transition[2] = -1;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }

            }

            // get final states
            int[] finalSts = ComputeFinalStates(finalStates);
            int dummyInitial = Math.Abs(Guid.NewGuid().GetHashCode());
            foreach (int s in initialStates)
            {
                int[] transition = new int[4];
                transition[0] = dummyInitial;
                transition[1] = -1;
                transition[2] = -1;
                transition[3] = s;
                transitions.Add(transition);
            }
            // create Automaton
            Automaton<BvSet> yieldTypeCheckAutomaton = solver.ReadFromRanges(dummyInitial, finalSts, transitions);
            return yieldTypeCheckAutomaton;
        }

        private static string PrintEpsilon(BvSet cond, CharSetSolver slvr)
        {
            if (cond == null)
            {
                return "E";
            }
            else return slvr.PrettyPrint(cond);

        }
    }


}

#endif