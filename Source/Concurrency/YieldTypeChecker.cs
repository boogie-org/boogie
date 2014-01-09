#if QED

#define DEBUG
#define OPTIMIZED
#define NONOPTIMIZED

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
        /*static subfields of yieldtypesafe(YTS) property language*/
        static CharSetSolver yieldCheckerAutomatonSolver;
#if OPTIMIZED
        static string yieldReachabilityOptCheckerRegex = @"^1*([D]+([571])*A?([97])*)*$";
        static Automaton<BvSet> yieldReachabilityOptCheckerAutomaton;
        static Automaton<BvSet> minimizedReachabilityOptCheckerAutomaton;
#endif
#if !NONOPTIMIZED
        static string yieldReachabilityCheckerRegex = @"^([1234])*([D]+([56781234])*A?([973])*)*$";// regex of property to build automaton of YTS language   
        static Automaton<BvSet> yieldReachabilityCheckerAutomaton;
        static Automaton<BvSet> minimizedReachabilityCheckerAutomaton;
#endif
        static Automaton<BvSet> yieldTypeSafeCheckerAutomaton;
        static Automaton<BvSet> minimizedYieldTypeSafeCheckerAutomaton;

        static YieldTypeChecker()
        {
            yieldCheckerAutomatonSolver = new CharSetSolver(BitWidth.BV7);
#if !NONOPTIMIZED
            yieldReachabilityCheckerAutomaton =
            Automaton<BvSet>.MkProduct(yieldCheckerAutomatonSolver.Convert(yieldReachabilityCheckerRegex),
                                           yieldCheckerAutomatonSolver.Convert(@"^[1-9A-D]*$"), // result of product with this Automaton provides us an automaton that has (*) existence alphanum chars in our property automaton 
                                           yieldCheckerAutomatonSolver);
            minimizedReachabilityCheckerAutomaton = yieldReachabilityCheckerAutomaton.Determinize(yieldCheckerAutomatonSolver).Minimize(yieldCheckerAutomatonSolver);
#endif

#if OPTIMIZED
            yieldReachabilityOptCheckerAutomaton =
           Automaton<BvSet>.MkProduct(yieldCheckerAutomatonSolver.Convert(yieldReachabilityOptCheckerRegex),
                                          yieldCheckerAutomatonSolver.Convert(@"^[1-9A-D]*$"), // result of product with this Automaton provides us an automaton that has (*) existence alphanum chars in our property automaton 
                                          yieldCheckerAutomatonSolver);
            minimizedReachabilityOptCheckerAutomaton = yieldReachabilityOptCheckerAutomaton.Determinize(yieldCheckerAutomatonSolver).Minimize(yieldCheckerAutomatonSolver);

#endif
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

        private static Tuple<Automaton<BvSet>, bool> IsYieldReachabilitySafe(Automaton<BvSet> implReachabilityCheckAutomaton, Implementation impl, MoverTypeChecker moverTypeChecker, int phaseNum)
        {
            List<BvSet> witnessSet;
#if !NONOPTIMIZED
            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                           implReachabilityCheckAutomaton,
                                                           yieldReachabilityCheckerAutomaton,
                                                           0,
                                                           yieldCheckerAutomatonSolver,
                                                           out witnessSet);
            var diffAutomaton = implReachabilityCheckAutomaton.Minus(yieldReachabilityCheckerAutomaton, yieldCheckerAutomatonSolver);
#endif

#if OPTIMIZED
            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                          implReachabilityCheckAutomaton,
                                                          yieldReachabilityOptCheckerAutomaton,
                                                          0,
                                                          yieldCheckerAutomatonSolver,
                                                          out witnessSet);

            var diffAutomaton = implReachabilityCheckAutomaton.Minus(yieldReachabilityOptCheckerAutomaton, yieldCheckerAutomatonSolver);
#endif

            if (isNonEmpty)
            {
                var witness = new String(Array.ConvertAll(witnessSet.ToArray(), bvset => (char)yieldCheckerAutomatonSolver.Choose(bvset)));
                Tuple<Automaton<BvSet>, bool> errTraceExists = new Tuple<Automaton<BvSet>, bool>(diffAutomaton, false);
                return errTraceExists;
            }
            Tuple<Automaton<BvSet>, bool> errTraceNotExist = new Tuple<Automaton<BvSet>, bool>(diffAutomaton, true);
            return errTraceNotExist;
        }

        private static Tuple<Automaton<BvSet>, bool> IsYieldTypeSafe(Automaton<BvSet> implTypeSafeCheckAutomaton, Implementation impl, MoverTypeChecker moverTypeChecker, int phaseNum)
        {
            List<BvSet> witnessSet;
            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                           implTypeSafeCheckAutomaton,
                                                           yieldTypeSafeCheckerAutomaton,
                                                           0,
                                                           yieldCheckerAutomatonSolver,
                                                           out witnessSet);
            var diffAutomaton = implTypeSafeCheckAutomaton.Minus(yieldTypeSafeCheckerAutomaton, yieldCheckerAutomatonSolver);

            if (isNonEmpty)
            {
                var witness = new String(Array.ConvertAll(witnessSet.ToArray(), bvset => (char)yieldCheckerAutomatonSolver.Choose(bvset)));
                Tuple<Automaton<BvSet>, bool> errTraceExists = new Tuple<Automaton<BvSet>, bool>(diffAutomaton, false);
                return errTraceExists;
            }
            Tuple<Automaton<BvSet>, bool> errTraceNotExist = new Tuple<Automaton<BvSet>, bool>(diffAutomaton, true);
            return errTraceNotExist;
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
            Program yieldTypeCheckedProgram = moverTypeChecker.program;
            YieldTypeChecker regExprToAuto = new YieldTypeChecker();

            YieldTypeCheckerCore yieldTypeCheckerPerImpl = new YieldTypeCheckerCore(moverTypeChecker);

            foreach (int yTypeCheckCurrentPhaseNum in moverTypeChecker.allPhaseNums) // take current phase check num from each interval
            {
                foreach (var decl in yieldTypeCheckedProgram.TopLevelDeclarations)
                {
                    Implementation impl = decl as Implementation;
                    if (impl == null) continue;
                    int phaseNumSpecImpl = moverTypeChecker.FindPhaseNumber(impl.Proc);
                    if (yTypeCheckCurrentPhaseNum > phaseNumSpecImpl) continue;

                    Tuple<Tuple<Dictionary<int, Absy>, Automaton<BvSet>>, Tuple<Dictionary<int, Absy>, Automaton<BvSet>>> yieldCheckAutomatons =
                            yieldTypeCheckerPerImpl.YieldTypeCheckAutomaton(impl, phaseNumSpecImpl, yTypeCheckCurrentPhaseNum);

                    Tuple<Automaton<BvSet>, bool> isYieldReachable = IsYieldReachabilitySafe(yieldCheckAutomatons.Item2.Item2, impl, moverTypeChecker, yTypeCheckCurrentPhaseNum);
                    Tuple<Automaton<BvSet>, bool> isYieldTypeSafe = IsYieldTypeSafe(yieldCheckAutomatons.Item1.Item2, impl, moverTypeChecker, yTypeCheckCurrentPhaseNum);
                    Automaton<BvSet> isYieldTypeSafeErrorAut = isYieldTypeSafe.Item1;
                    Automaton<BvSet> isYieldReachableErrorAut = isYieldReachable.Item1;

                    Dictionary<int, Absy> isYieldTypeSafeCmds = yieldCheckAutomatons.Item1.Item1;
                    Dictionary<int, Absy> isYieldReachableSafeCmds = yieldCheckAutomatons.Item2.Item1;

                    if (!isYieldReachable.Item2 && !isYieldTypeSafe.Item2)
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_type_safe at phase " + yTypeCheckCurrentPhaseNum.ToString() + "\n");
                        PrintErrorTrace(isYieldTypeSafeCmds, isYieldTypeSafeErrorAut, impl);
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_reachable_safe at phase " + yTypeCheckCurrentPhaseNum.ToString() + "\n");
                        PrintErrorTrace(isYieldReachableSafeCmds, isYieldReachableErrorAut, impl);
                    }
                    else if (isYieldReachable.Item2 && !isYieldTypeSafe.Item2)
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_type_safe at phase " + yTypeCheckCurrentPhaseNum.ToString() + "\n");
                        PrintErrorTrace(isYieldTypeSafeCmds, isYieldTypeSafeErrorAut, impl);
                    }
                    else if (!isYieldReachable.Item2 && isYieldTypeSafe.Item2)
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_reachable_safe at phase " + yTypeCheckCurrentPhaseNum.ToString() + "\n");
                        PrintErrorTrace(isYieldReachableSafeCmds, isYieldReachableErrorAut, impl);
                    }
                    else if (isYieldReachable.Item2 && isYieldTypeSafe.Item2)
                    {

                    }
                }
            }
        }
    }

    class YieldTypeCheckerCore
    {
        int stateCounter;
        MoverTypeChecker moverTypeChecker;
        CharSetSolver solver;
        Dictionary<Tuple<int, int>, string> edgeLabels;
        HashSet<int> finalStates;
        HashSet<int> initialStates;
        Dictionary<Absy, int> abysToNode;
        Graph<int> graph;
        int specPhaseNumImpl, yTypeCheckCurrentPhaseNum;
        Implementation yTypeChecked;

        public YieldTypeCheckerCore(MoverTypeChecker moverTypeChecker)
        {
            solver = new CharSetSolver(BitWidth.BV7);
            this.moverTypeChecker = moverTypeChecker;

        }

        public Tuple<Tuple<Dictionary<int, Absy>, Automaton<BvSet>>, Tuple<Dictionary<int, Absy>, Automaton<BvSet>>> YieldTypeCheckAutomaton(Implementation ytypeChecked, int specPhsNumImpl, int yTypeCheckCurPhaseNum)
        {
            edgeLabels = new Dictionary<Tuple<int, int>, string>(); // Tuple<int,int> --> "Y" : State(k) --Y--> State(k+1)

            finalStates = new HashSet<int>();
            initialStates = new HashSet<int>();
            stateCounter = 0;
            yTypeChecked = ytypeChecked;
            specPhaseNumImpl = specPhsNumImpl;
            yTypeCheckCurrentPhaseNum = yTypeCheckCurPhaseNum;
            initialStates.Add(stateCounter); // First state is added to initial states
            abysToNode = CreateStateNumbers();
            graph = BuildAutomatonGraph(); // build component of graph for a phase interval            

            Automaton<BvSet> implYieldTypeSafeCheckAut = BuildAutomatonYieldTypeSafe();
            Dictionary<int, Absy> nodeToAbysYieldTypeSafe = new Dictionary<int, Absy>();
            foreach (KeyValuePair<Absy, int> state in abysToNode)
            {
                nodeToAbysYieldTypeSafe[state.Value] = state.Key;
            }
            Tuple<Dictionary<int, Absy>, Automaton<BvSet>> implYieldTypeSafeCheckAutomaton = new Tuple<Dictionary<int, Absy>, Automaton<BvSet>>(nodeToAbysYieldTypeSafe, implYieldTypeSafeCheckAut);
#if !NONOPTIMIZED
             // Update edges w.r.t yield reaching. VocabX{True,False} 
            PostProcessGraph(bodyGraphForImplPhaseJ, edgeLabels);
            Automaton<BvSet> implYieldReachCheckAut = BuildAutomatonYieldReachSafe(bodyGraphForImplPhaseJ, edgeLabels, initialStates, finalStates, ytypeChecked, yTypeCheckCurrentPhaseNum); // Last to arguments are just only for showGraph of automaton lib
#endif
#if OPTIMIZED
            Automaton<BvSet> implYieldReachCheckAut = BuildOptAutomatonYieldReachSafe();
#endif
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

        public Dictionary<Absy, int> CreateStateNumbers()
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

        private Graph<int> BuildAutomatonGraph()
        {
            HashSet<Tuple<int, int>> edges = new HashSet<Tuple<int, int>>();
            foreach (Block block in yTypeChecked.Blocks)
            {
                if (block.Cmds.Count >= 2)
                {
                    for (int i = 0; i < block.Cmds.Count - 1; i++)
                    {
                        //IsProper
                        if (IsProperActionCmd(block.Cmds[i]) && IsProperActionCmd(block.Cmds[i + 1]))// this is handled in else but keep this branch now
                        { // proper state transition
                            int source = abysToNode[block.Cmds[i]];
                            int dest = abysToNode[block.Cmds[i + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsProperActionCmd(block.Cmds[i]) && IsExitStatement(block.Cmds[i + 1]))
                        {
                            int source = abysToNode[block.Cmds[i]];
                            // create artificial final state
                            int dest = Math.Abs(Guid.NewGuid().GetHashCode()); // Generate unique dummy node ref: http://msdn.microsoft.com/en-us/library/system.guid(v=vs.110).aspx
                            finalStates.Add(dest);
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsProperActionCmd(block.Cmds[i]) && IsParallelCallCmdYield(block.Cmds[i + 1]))
                        {
                            int source = abysToNode[block.Cmds[i]];
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            int dest = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        else if (IsProperActionCmd(block.Cmds[i]) && IsSeqComposableParCallCmd(block.Cmds[i + 1]))
                        {
                            int source = abysToNode[block.Cmds[i]];
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            int dest = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        // IsCallCmdsExit
                        else if (IsExitStatement(block.Cmds[i]) && IsProperActionCmd(block.Cmds[i + 1]))
                        { // current cmd exit , next cmd will be put as initial state
                            initialStates.Add(abysToNode[block.Cmds[i + 1]]);
                        }
                        else if (IsExitStatement(block.Cmds[i]) && IsExitStatement(block.Cmds[i + 1]))
                        {
                            continue;
                        }
                        else if (IsExitStatement(block.Cmds[i]) && IsParallelCallCmdYield(block.Cmds[i + 1]))
                        {
                            // Add state number CallCmd of ParallelCmd
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            initialStates.Add(abysToNode[nextCmd.CallCmds[0]]);
                        }
                        else if (IsExitStatement(block.Cmds[i]) && IsSeqComposableParCallCmd(block.Cmds[i + 1]))
                        {
                            // Add state number CallCmd of ParallelCmd
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            initialStates.Add(abysToNode[nextCmd.CallCmds[0]]);

                        }
                        // ParallelCallCmdYield
                        else if (IsParallelCallCmdYield(block.Cmds[i]) && IsParallelCallCmdYield(block.Cmds[i + 1]))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            int source = abysToNode[currentCmd.CallCmds[0]];
                            int dest = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsParallelCallCmdYield(block.Cmds[i]) && IsSeqComposableParCallCmd(block.Cmds[i + 1]))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            int source = abysToNode[currentCmd.CallCmds[0]];
                            int dest = abysToNode[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsParallelCallCmdYield(block.Cmds[i]) && IsExitStatement(block.Cmds[i + 1]))
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
                        else if (IsParallelCallCmdYield(block.Cmds[i]) && IsProperActionCmd(block.Cmds[i + 1]))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            int source = abysToNode[currentCmd.CallCmds[0]];
                            int dest = abysToNode[block.Cmds[i + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        //SeqComposable Parallel Cmd
                        else if (IsSeqComposableParCallCmd(block.Cmds[i]) && IsSeqComposableParCallCmd(block.Cmds[i + 1]))
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
                        else if (IsSeqComposableParCallCmd(block.Cmds[i]) && IsParallelCallCmdYield(block.Cmds[i + 1]))
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
                        else if (IsSeqComposableParCallCmd(block.Cmds[i]) && IsExitStatement(block.Cmds[i + 1]))
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
                        else if (IsSeqComposableParCallCmd(block.Cmds[i]) && IsProperActionCmd(block.Cmds[i + 1]))
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
                    if (IsExitStatement(block.Cmds[block.Cmds.Count - 1]))
                    { // put b.TransferCmd into initial states
                        initialStates.Add(abysToNode[block.TransferCmd]);
                    }
                    else if (IsParallelCallCmdYield(block.Cmds[block.Cmds.Count - 1]))
                    {
                        ParCallCmd currentCmd = block.Cmds[block.Cmds.Count - 1] as ParCallCmd;
                        int source = abysToNode[currentCmd.CallCmds[0]];
                        int dest = abysToNode[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[block.Cmds.Count - 1]));
                    }
                    else if (IsSeqComposableParCallCmd(block.Cmds[block.Cmds.Count - 1]))
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
                    else if (IsProperActionCmd(block.Cmds[block.Cmds.Count - 1]))
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
                    if (IsExitStatement(block.Cmds[0]))
                    { // put b.TransferCmd into initial states
                        initialStates.Add(abysToNode[block.TransferCmd]);
                    }
                    else if (IsProperActionCmd(block.Cmds[0]))
                    { // proper transition to state before transfer command
                        int source = abysToNode[block.Cmds[0]];
                        int dest = abysToNode[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[0]));
                    }
                    else if (IsParallelCallCmdYield(block.Cmds[0]))
                    {
                        ParCallCmd currentCmd = block.Cmds[0] as ParCallCmd;
                        int source = abysToNode[currentCmd.CallCmds[0]];
                        int dest = abysToNode[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[0]));
                    }
                    else if (IsSeqComposableParCallCmd(block.Cmds[0]))
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
                HashSet<int> targetBlockEntryStates = GetStateOfTargetBlock(block.TransferCmd);
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

        private HashSet<int> GetStateOfTargetBlock(TransferCmd tc)
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
                        if (IsExitStatement(block.Cmds[0]))
                        {
                            int targetState = Math.Abs(Guid.NewGuid().GetHashCode());
                            finalStates.Add(targetState);
                            targetBlockEntryStates.Add(targetState);
                        }
                        else if (IsProperActionCmd(block.Cmds[0]))
                        {
                            targetBlockEntryStates.Add(abysToNode[block.Cmds[0]]);
                        }
                        else if (IsParallelCallCmdYield(block.Cmds[0]))
                        {
                            ParCallCmd targetCmd = block.Cmds[0] as ParCallCmd;
                            targetBlockEntryStates.Add(abysToNode[targetCmd.CallCmds[0]]);
                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[0]))
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
                                    else if (IsParallelCallCmdYield(block.Cmds[existsNonAsync]))
                                    {
                                        ParCallCmd targetCmd = block.Cmds[existsNonAsync] as ParCallCmd;
                                        targetBlockEntryStates.Add(abysToNode[targetCmd.CallCmds[0]]);
                                        break;
                                    }
                                    else if (IsSeqComposableParCallCmd(block.Cmds[existsNonAsync]))
                                    {
                                        ParCallCmd targetCmd = block.Cmds[existsNonAsync] as ParCallCmd;
                                        targetBlockEntryStates.Add(abysToNode[targetCmd.CallCmds[0]]);
                                        break;

                                    }
                                    else if (IsExitStatement(block.Cmds[existsNonAsync]))
                                    {
                                        int targetState = Math.Abs(Guid.NewGuid().GetHashCode());
                                        finalStates.Add(targetState);
                                        targetBlockEntryStates.Add(targetState);
                                        break;
                                    }
                                    else if (IsExitStatement(block.Cmds[existsNonAsync]))
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

        private bool IsAccessToNonQedVar(Cmd cmd)
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
        private Set FilterGlobalVariables(Set vars)
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

        private Set ComputeGlobalAccesses(Cmd cmd)
        {
            Set s = ComputeGlobalReads(cmd);
            s.AddRange(ComputeGlobalWrites(cmd));
            return s;
        }

        private Set ComputeGlobalReads(Cmd cmd)
        {
            return FilterGlobalVariables(ComputeReads(cmd));
        }

        private Set ComputeGlobalWrites(Cmd cmd)
        {
            return FilterGlobalVariables(ComputeWrites(cmd));
        }

        private Set ComputeReads(Cmd cmd)
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
            // Delegated to Shaz's type checker
            /*else if (cmd is CallCmd)
            {
                CallCmd callCmd = cmd as CallCmd;
                foreach (Expr var in callCmd.Ins) {var.ComputeFreeVariables(vars); }      
                
            }
            else if(cmd is ParCallCmd){
                ParCallCmd parCallCmd = cmd as ParCallCmd;
              
                foreach (CallCmd parCalle in parCallCmd.CallCmds) {
                    foreach (Expr var in parCalle.Ins) {
        //                Console.WriteLine("ParCall rd var " + var.ToString());
                        var.ComputeFreeVariables(vars);
                    }

                }            
            }*/
            return vars;
        }
        // Discuss and remove
        private Set ComputeWrites(Cmd cmd)
        {
            Set vars = new Set();
            /*
            List<Variable> varseq = new List<Variable>();
            cmd.AddAssignedVariables(varseq);
            foreach (Variable var in varseq)
            {
                vars.Add(var);
            }           
            return vars;
            */
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
            // Delegated to Shaz's type checker
            /*
          else if (cmd is CallCmd)
          {
              CallCmd callCmd = cmd as CallCmd;
              foreach (Expr var in callCmd.Proc.Modifies) { var.ComputeFreeVariables(vars); }
              foreach (Expr var in callCmd.Outs) {  var.ComputeFreeVariables(vars); }
          }
          else if (cmd is ParCallCmd) {             
              ParCallCmd parCallCmd = cmd as ParCallCmd;
              foreach (CallCmd parCalle in parCallCmd.CallCmds) {
                  foreach (Expr var in parCalle.Proc.Modifies) { var.ComputeFreeVariables(vars); }
                  foreach (Expr var in parCalle.Outs) { var.ComputeFreeVariables(vars); }
              }            
          }*/
            return vars;
        }

        //
        private bool IsProperActionCmd(Cmd cmd)
        {
            if (!IsExitStatement(cmd) &&
                !IsParallelCallCmdYield(cmd) &&
                !IsSeqComposableParCallCmd(cmd) &&
                !IsAsyncCallCmd(cmd))
            {
                return true;
            }
            return false;

        }
        private bool IsExitStatement(Cmd cmd)
        {
            if (IsCallCmdExitPoint(cmd) || IsAccessToNonQedVar(cmd)) { return true; }
            return false;
        }

        private bool IsCallCmdExitPoint(Cmd cmd)
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

        private bool IsParallelCallCmdYield(Cmd cmd)
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

        private bool IsSeqComposableParCallCmd(Cmd cmd)
        {
            if (cmd is ParCallCmd && !IsParallelCallCmdYield(cmd)) { return true; }
            return false;
        }
        private bool IsAsyncCallCmd(Cmd cmd)
        {
            if (cmd is CallCmd)
            {
                CallCmd calle = cmd as CallCmd;
                if (calle.IsAsync) { return true; }
            }
            return false;
        }
        private string GetEdgeType(Cmd cmd)
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
            //else if (cmd is AssignCmd)
            //{  //rest can only be assigncmd                
            return "Q";
            //}

        }
        private string PrintGraph()
        {
            var s = new StringBuilder();
            s.AppendLine("\nImplementation " + yTypeChecked.Proc.Name + " digraph G {");
            foreach (var e in graph.Edges)
                s.AppendLine("  \"" + e.Item1.ToString() + "\" -- " + edgeLabels[e] + " --> " + "  \"" + e.Item2.ToString() + "\";");
            s.AppendLine("}");
            return s.ToString();
        }
        private HashSet<Tuple<int, int>> CollectBackwardEdgesOfYieldEdge(int source)
        {
            HashSet<Tuple<int, int>> yieldReachingEdges = new HashSet<Tuple<int, int>>(); // Collect edges that are backward reachable from source vertex of yield a edge,source ---Y---> sink, in backward direction
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
                foreach (int v in graph.Predecessors(u))
                {

                    if (white.Contains(v) && !gray.Contains(v) && !black.Contains(v))
                    {

                        gray.Add(v);
                        frontier.Enqueue(v);
                        // Add to yielding edges
                        yieldReachingEdges.Add(new Tuple<int, int>(v, u));
                    }

                }
                black.Add(u);
            }

            return yieldReachingEdges;
        }
        /*
         * Calls CollectBackEdges for each Y edge existing in graph
         */
        private HashSet<Tuple<int, int>> CollectYieldReachingEdgesOfGraph()
        {
            HashSet<Tuple<int, int>> yieldTrueEdges = new HashSet<Tuple<int, int>>(); // Set {forall edges e : e is reaching a Y labeled edge}
            foreach (var e in graph.Edges) // Visits all edges to and do backward yield reachability analysis starting from source vertex of an "Y" labeled edge
            {
                if (edgeLabels[e] == "Y")
                {
                    HashSet<Tuple<int, int>> yieldReachingEdges = CollectBackwardEdgesOfYieldEdge(e.Item1);
                    foreach (Tuple<int, int> yldrch in yieldReachingEdges)
                    {

                        yieldTrueEdges.Add(yldrch);
                    }
                }
            }
            return yieldTrueEdges;
        }

        private HashSet<Tuple<int, int>> CollectEdgesReachableFromAction(int source)
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
        private void IsExitOrRetReachableFromAtomicOrLeft()
        {
            foreach (var e in graph.Edges)
            {
                if (edgeLabels[e] == "A" || edgeLabels[e] == "L")
                {
                    HashSet<Tuple<int, int>> edgesReachable = CollectEdgesReachableFromAction(e.Item1);

                    if (!ReachesFinalState(edgesReachable) || !ReachesYieldState(edgesReachable))
                    {
                        moverTypeChecker.Error(yTypeChecked, "Implementation Yield Reachable " + yTypeChecked.Proc.Name);
                    }
                }
            }
        }
        private void IsExitOrReachableFromBoth()
        {
            foreach (var e in graph.Edges)
            {
                if (edgeLabels[e] == "B")
                {
                    HashSet<Tuple<int, int>> edgesReachable = CollectEdgesReachableFromAction(e.Item1);
                    if (!ReachesFinalState(edgesReachable) || !ReachesYieldState(edgesReachable))
                    {
                        //   Console.WriteLine("Both is converted to R");
                        edgeLabels[e] = "R";
                    }
                }
            }

        }
        private void IsExitOrReachableFromLocal()
        {
            foreach (var e in graph.Edges)
            {
                if (edgeLabels[e] == "Q")
                {
                    HashSet<Tuple<int, int>> edgesReachable = CollectEdgesReachableFromAction(e.Item1);
                    if (!ReachesFinalState(edgesReachable) || !ReachesYieldState(edgesReachable))
                    {
                        // Console.WriteLine("Q is being converted to P");
                        edgeLabels[e] = "P";
                    }
                    edgeLabels[e] = "E";
                }
            }
        }
        private bool ReachesFinalState(HashSet<Tuple<int, int>> edges)
        {

            foreach (Tuple<int, int> e in edges)
            {
                if (finalStates.Contains(e.Item1) || finalStates.Contains(e.Item2)) return true;
            }
            return false;
        }
        private bool ReachesYieldState(HashSet<Tuple<int, int>> edges)
        {
            foreach (var e in edges)
            {

                if (edgeLabels[e] == "Y") return true;
            }
            return false;
        }

        private Automaton<BvSet> BuildOptAutomatonYieldReachSafe()
        {

            IsExitOrRetReachableFromAtomicOrLeft();
            IsExitOrReachableFromBoth();
            IsExitOrReachableFromLocal();
            return BuildAutomatonYieldTypeSafe();
        }

        /*
         * Updates vertices map according to according to yieldReaching edges. If an edge in graph is not yield reaching that its vertices map updated.
         */
        private void PostProcessGraph()
        {
            HashSet<Tuple<int, int>> yieldTrueEdges = CollectYieldReachingEdgesOfGraph();

            foreach (Tuple<int, int> yldrch in yieldTrueEdges)
            {
                if (edgeLabels[yldrch] == "Q")
                {
                    edgeLabels[yldrch] = "3";
                }
                else if (edgeLabels[yldrch] == "P")
                {
                    edgeLabels[yldrch] = "1";
                }
                else if (edgeLabels[yldrch] == "B")
                {
                    edgeLabels[yldrch] = "7";
                }
                else if (edgeLabels[yldrch] == "R")
                {
                    edgeLabels[yldrch] = "5";
                }
                else if (edgeLabels[yldrch] == "L")
                {
                    edgeLabels[yldrch] = "9";
                }
                else if (edgeLabels[yldrch] == "A")
                {
                    edgeLabels[yldrch] = "A";
                }
                else if (edgeLabels[yldrch] == "Y")
                {
                    edgeLabels[yldrch] = "D";
                }
            }
            foreach (Tuple<int, int> nyldrch in graph.Edges)
            {
                if (!yieldTrueEdges.Contains(nyldrch))
                {
                    if (edgeLabels[nyldrch] == "Q")
                    {
                        edgeLabels[nyldrch] = "4";
                    }
                    else if (edgeLabels[nyldrch] == "P")
                    {
                        edgeLabels[nyldrch] = "2";
                    }
                    else if (edgeLabels[nyldrch] == "B")
                    {
                        edgeLabels[nyldrch] = "8";
                    }
                    else if (edgeLabels[nyldrch] == "R")
                    {
                        edgeLabels[nyldrch] = "6";
                    }
                    else if (edgeLabels[nyldrch] == "L")
                    {
                        edgeLabels[nyldrch] = "C";
                    }
                    else if (edgeLabels[nyldrch] == "A")
                    {
                        edgeLabels[nyldrch] = "B";
                    }
                    else if (edgeLabels[nyldrch] == "Y")
                    {
                        edgeLabels[nyldrch] = "D";
                    }
                }
            }
        }

        private int[] ComputeFinalStates()
        {
            return finalStates.ToArray();
        }
        private int[] ComputeInitialStates()
        {
            return initialStates.ToArray();
        }

        private Automaton<BvSet> BuildAutomatonYieldTypeSafe()
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
            int[] finalSts = ComputeFinalStates();
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

        private Automaton<BvSet> BuildAutomatonYieldReachSafe()
        {
            List<int[]> transitions = new List<int[]>();
            foreach (Tuple<int, int> e in graph.Edges)
            {
                if (edgeLabels[e] == "3")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 51; // ASCII 3
                    transition[2] = 51;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "1")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 49; // ASCII 1
                    transition[2] = 49;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "7")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 55; // ASCII 7
                    transition[2] = 55;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "5")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 53; // ASCII 5
                    transition[2] = 53;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "9")
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
                else if (edgeLabels[e] == "D")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 68; // ASCII D
                    transition[2] = 68;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "4")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 52; // ASCII 4
                    transition[2] = 52;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "2")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 50; // ASCII 2
                    transition[2] = 50;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "8")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 56; // ASCII 8
                    transition[2] = 56;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "6")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 54; // ASCII 6
                    transition[2] = 54;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "C")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 67; // ASCII C
                    transition[2] = 67;
                    transition[3] = e.Item2;
                    transitions.Add(transition);
                }
                else if (edgeLabels[e] == "B")
                {
                    int[] transition = new int[4];
                    transition[0] = e.Item1;
                    transition[1] = 66; // ASCII B
                    transition[2] = 66;
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
            int[] finalSts = ComputeFinalStates();
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
        private string PrintEpsilon(BvSet cond, CharSetSolver slvr)
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