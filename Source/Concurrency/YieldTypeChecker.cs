#if QED

#define DEBUG
#define DEBUG_DETAIL

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
    /*
     Summary:
     * 
     */
    class YieldTypeChecker
    {
        /*static subfields of yieldtypesafe(YTS) property language*/
        static CharSetSolver yieldTypeCheckerAutomatonSolver;
        static string yieldTypeCheckerRegex = @"^((1|2)+(3|4))*((D)+(((5|6))+((7|8))+((1|2))+((3|4)))*[A]((9)+(7)+(3))*)*$";// regex of property to build automaton of YTS language
        static Automaton<BvSet> yieldTypeCheckerAutomaton;
        static YieldTypeChecker()
        {
            yieldTypeCheckerAutomatonSolver = new CharSetSolver(BitWidth.BV7);
            yieldTypeCheckerAutomaton =
                Automaton<BvSet>.MkProduct(yieldTypeCheckerAutomatonSolver.Convert(yieldTypeCheckerRegex),
                                           yieldTypeCheckerAutomatonSolver.Convert(@"^[1-9A-D]*$"),
                                           yieldTypeCheckerAutomatonSolver);
        }
        /*Parameter : Implementation impl : Implementation whose phase intervals, statistical data(number of call stmts) are computed*/
        private static List<Tuple<int, int>> ComputePhaseIntervals(Implementation impl, int specPhaseNumImpl, MoverTypeChecker moverTypeChecker)
        {
            HashSet<CallCmd> callCmdsInImpl = new HashSet<CallCmd>(); //  callCmdsInImpl[Implementation] ==> Set = { call1, call2, call3 ... }
            List<Tuple<int, int>> phaseIntervals = new List<Tuple<int, int>>(); // [MinValue ph0 ] [ph0 ph1] [ph1 ph2] ..... [phk phk+1] intervals

            // Compute CallCmds inside impl
            foreach (Block b in impl.Blocks)
            {
                for (int i = 0; i < b.Cmds.Count; i++)
                {
                    CallCmd callCmd = b.Cmds[i] as CallCmd;
                    if (callCmd == null) continue;
                    callCmdsInImpl.Add(callCmd);
                }
            }

            //Collect phase numbers of CallCmds inside impl
            HashSet<int> callCmdPhaseNumSet = new HashSet<int>();
            foreach (CallCmd callCmd in callCmdsInImpl)
            {
                int tmpPhaseNum = moverTypeChecker.FindPhaseNumber(callCmd.Proc);
                callCmdPhaseNumSet.Add(tmpPhaseNum);
            }
            callCmdPhaseNumSet.Add(specPhaseNumImpl);

            List<int> callCmdPhaseNumList = callCmdPhaseNumSet.ToList();
            callCmdPhaseNumList.Sort();
#if (DEBUG && !DEBUG_DETAIL)
            Console.Write("\n CallCmds's phase numbers \n");
            for (int i = 0; i < callCmdInBodyEncImplList.Count; i++)
            {
                Console.Write("\nCallCmd Phase Num " + callCmdPhaseNumIndexList[i].ToString() + " ");
            }
#endif
            //Create Phase Intervals
            for (int i = 0; i < callCmdPhaseNumList.Count; i++)
            {
                //create the initial phase (-inf leastPhaseNum]
                if (i == 0)
                {
                    Tuple<int, int> initTuple = new Tuple<int, int>(int.MinValue, callCmdPhaseNumList[i]);
                    phaseIntervals.Add(initTuple);
                }
                else // create other phase intervals 
                {
                    Tuple<int, int> intervalToInsert = new Tuple<int, int>(callCmdPhaseNumList[i - 1] + 1, callCmdPhaseNumList[i]);
                    phaseIntervals.Add(intervalToInsert);
                }
            }
#if (DEBUG && !DEBUG_DETAIL)
            Console.Write("\n Number of phases is " + phaseIntervals.Count.ToString());
            for (int i = 0;i<phaseIntervals.Count ; i++) {
                Console.Write("\n Phase " + i.ToString() + "[" + phaseIntervals[i].Item1.ToString() + "," + phaseIntervals[i].Item2.ToString() + "]" + "\n");
            }
#endif
            return phaseIntervals;
        }


        /*
         Parameter: Automaton<BvSet> implTypeCheckAutomaton :  Automaton of implementation body build with respect to YTSI.
         Return : if L(YTSI) is subset of L(YTSP) {TRUE} else {FALSE}  
         */
        public static bool IsYieldTypeSafe(Automaton<BvSet> implTypeCheckAutomaton)
        {

            List<BvSet> witnessSet;
            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                           implTypeCheckAutomaton,
                                                           yieldTypeCheckerAutomaton,
                                                           0,
                                                           yieldTypeCheckerAutomatonSolver,
                                                           out witnessSet);
            // Ask Margus, Shaz to be sure !
            if (isNonEmpty)
            {
                // var witness = new String(Array.ConvertAll(witnessSet.ToArray(), bvset => (char)yieldTypeCheckerAutomatonSolver.Choose(bvset)));
                //Console.Write("\n Program is not Yield Type Safe \n");
                //Console.Write("Debugging ... \n Difference of impl and yiled type check automaton  : \n" + witness);
                return false;
            }
            return true;
        }
        /*
         Parameter : LinearTypeChecker linearTypeChecker : YTS Checker is a component of linearTypeChecker.Adds instance of YTS checker into linearType checker
         */
        public static void PerformYieldTypeChecking(MoverTypeChecker moverTypeChecker)
        {
            Program yieldTypeCheckedProgram = moverTypeChecker.program;
            YieldTypeChecker regExprToAuto = new YieldTypeChecker();
            foreach (var decl in yieldTypeCheckedProgram.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null) continue;
                int phaseNumSpecImpl = moverTypeChecker.FindPhaseNumber(impl.Proc);

                YieldTypeCheckerCore yieldTypeCheckerPerImpl = new YieldTypeCheckerCore(moverTypeChecker);
                List<Tuple<int, int>> phaseIntervals = ComputePhaseIntervals(impl, phaseNumSpecImpl, moverTypeChecker); // Compute intervals

                for (int i = 0; i < phaseIntervals.Count; i++) // take current phase check num from each interval
                {
                    int yTypeCheckCurrentPhaseNum = phaseIntervals[i].Item2;
                    Automaton<BvSet> yieldTypeCheckAutoPerPhase = yieldTypeCheckerPerImpl.YieldTypeCheckAutomata(impl, phaseNumSpecImpl, yTypeCheckCurrentPhaseNum);
                    if (!IsYieldTypeSafe(yieldTypeCheckAutoPerPhase))
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield type safe " + "\n");
                    }
                }
            }
        }
    }

    /*
     * Executor class for creating L(YTSI).
     */
    class YieldTypeCheckerCore
    {

        int stateCounter;
        MoverTypeChecker moverTypeChecker;
        public YieldTypeCheckerCore(MoverTypeChecker moverTypeChecker)
        {
            this.moverTypeChecker = moverTypeChecker;
        }

        /*Parameter:YieldTypeCheckerCore yieldTypeCheckerPerImpl: takes an executor object to do all computation to build L(YTSI)
         */
        public Automaton<BvSet> YieldTypeCheckAutomata(Implementation ytypeChecked, int specPhaseNumImpl, int yTypeCheckCurrentPhaseNum)
        {
            Dictionary<Tuple<int, int>, string> edgeLabels = new Dictionary<Tuple<int, int>, string>(); // Tuple<int,int> --> "Y" : State(k) --Y--> State(k+1)
            Dictionary<Absy, int> abysToNode = CreateStateNumbers(ytypeChecked, yTypeCheckCurrentPhaseNum);
            List<int> finalStates = new List<int>();
            List<int> initialStates = new List<int>();
            stateCounter = 0;

            Graph<int> bodyGraphForImplPhaseJ = BuildAutomatonGraph(ytypeChecked, yTypeCheckCurrentPhaseNum, abysToNode, edgeLabels, initialStates, finalStates); // build component of graph for a phase interval            
#if (DEBUG && !DEBUG_DETAIL)
            Console.Write("\n Raw Graph is : \n");
            Console.Write(yieldTypeCheckerPerImpl.PrintGraph(yieldTypeCheckerPerImpl.GetTuplesForGraph()));
#endif
            // Update edges w.r.t yield reaching. VocabX{True,False} 
            PostProcessGraph(bodyGraphForImplPhaseJ, edgeLabels);
#if (DEBUG && !DEBUG_DETAIL)
            Console.Write("\n Refined Graph is : \n");
            Console.Write(yieldTypeCheckerPerImpl.PrintGraph(yieldTypeCheckerPerImpl.GetTuplesForGraph()));
#endif
            //Build Automaton from graph created
            return BuildAutomaton(bodyGraphForImplPhaseJ, edgeLabels, initialStates, finalStates);

        }

        public Dictionary<Absy, int> CreateStateNumbers(Implementation ytypeChecked, int yTypeCheckCurrentPhaseNum)
        {
            Dictionary<Absy, int> abysToNodeNo = new Dictionary<Absy, int>();
            foreach (Block block in ytypeChecked.Blocks)
            {
                foreach (Cmd cmd in block.Cmds)
                {

                    abysToNodeNo[cmd] = stateCounter;
                    stateCounter++;

                }
                abysToNodeNo[block.TransferCmd] = stateCounter;
                stateCounter++;
            }
            return abysToNodeNo;
        }

        /*
         * Implementation visitor call this main-visit-entrance function  
         */
        private Graph<int> BuildAutomatonGraph(Implementation ytypeChecked, int yTypeCheckCurrentPhaseNum, Dictionary<Absy, int> bodyGraphForImplPhaseJ,
                                               Dictionary<Tuple<int, int>, string> edgeLabels, List<int> initialStates, List<int> finalStates)
        {
            HashSet<Tuple<int, int>> edges = new HashSet<Tuple<int, int>>();

            foreach (Block block in ytypeChecked.Blocks)
            {
                if (block.Cmds.Count >= 2)
                {
                    for (int i = 0; i < block.Cmds.Count - 1; i++)
                    {
                        if (!IsCallCmdExitPoint(block.Cmds[i], yTypeCheckCurrentPhaseNum) && !IsCallCmdExitPoint(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))// I think this is handled in else
                        { // proper state transition

                            int source = bodyGraphForImplPhaseJ[block.Cmds[i]];
                            int dest = bodyGraphForImplPhaseJ[block.Cmds[i + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (!IsCallCmdExitPoint(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsCallCmdExitPoint(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        { // create artificial final state 

                            int source = bodyGraphForImplPhaseJ[block.Cmds[i]];
                            int dest = Math.Abs(Guid.NewGuid().GetHashCode());
                            finalStates.Add(dest);
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsCallCmdExitPoint(block.Cmds[i], yTypeCheckCurrentPhaseNum) && !IsCallCmdExitPoint(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        { // current cmd exit , next cmd will be put as initial state
                            initialStates.Add(bodyGraphForImplPhaseJ[block.Cmds[i + 1]]);

                        }
                        else if (IsCallCmdExitPoint(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsCallCmdExitPoint(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            continue;
                        }
                        else
                        {// Do proper transition 

                            int source = bodyGraphForImplPhaseJ[block.Cmds[i]];
                            int dest = bodyGraphForImplPhaseJ[block.Cmds[i + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                    }


                    if (IsCallCmdExitPoint(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum))
                    { // put b.TransferCmd into initial states
                        initialStates.Add(bodyGraphForImplPhaseJ[block.TransferCmd]);
                    }
                    else
                    { // proper transition to state before transfer command

                        int source = bodyGraphForImplPhaseJ[block.Cmds[block.Cmds.Count - 1]];
                        int dest = bodyGraphForImplPhaseJ[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[block.Cmds.Count - 1]));

                    }

                }
                else if (block.Cmds.Count == 1)
                {
                    if (IsCallCmdExitPoint(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                    { // put b.TransferCmd into initial states
                        initialStates.Add(bodyGraphForImplPhaseJ[block.Cmds[0]]);
                    }
                    else
                    { // proper transition to state before transfer command
                        int source = bodyGraphForImplPhaseJ[block.Cmds[0]];
                        int dest = bodyGraphForImplPhaseJ[block.TransferCmd];
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[0]));
                    }
                }
                else if (block.Cmds.Count == 0)
                {

                }
                // Handle
                HashSet<int> targetBlockEntryStates = GetStateOfTargetBlock(block.TransferCmd, bodyGraphForImplPhaseJ, yTypeCheckCurrentPhaseNum, initialStates, finalStates);
                foreach (int entryState in targetBlockEntryStates)
                {
                    int source = bodyGraphForImplPhaseJ[block.TransferCmd];
                    Tuple<int, int> transferEdge = new Tuple<int, int>(source, entryState);
                    edges.Add(transferEdge);
                    edgeLabels.Add(transferEdge, "E");
                }
            }

            Graph<int> automatonGraphOfImplPerPhase = new Graph<int>(edges);
            return automatonGraphOfImplPerPhase;
        }

        private HashSet<int> GetStateOfTargetBlock(TransferCmd tc, Dictionary<Absy, int> bodyGraphForImplPhaseJ, int yTypeCheckCurrentPhaseNum, List<int> initialStates, List<int> finalStates)
        {
            HashSet<int> targetBlockEntryStates = new HashSet<int>();
            if (tc is ReturnCmd)
            {
                // Do Nothing
            }
            else if (tc is GotoCmd)
            {
                GotoCmd transferCmd = tc as GotoCmd;
                foreach (Block block in transferCmd.labelTargets)
                {
                    if (block.Cmds.Count == 0)
                    {
                        targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[block.TransferCmd]);
                    }
                    else if (block.Cmds.Count >= 1)
                    {
                        if (IsCallCmdExitPoint(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                        {// Create artificial final state and put this into final states
                            int targetState = Math.Abs(Guid.NewGuid().GetHashCode());
                            finalStates.Add(targetState);
                            targetBlockEntryStates.Add(targetState);
                        }
                        else
                        {
                            targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[block.Cmds[0]]);
                        }
                    }
                }
            }
            return targetBlockEntryStates;
        }

        private bool IsCallCmdExitPoint(Cmd cmd, int yTypeCheckCurrentPhaseNum)
        {

            if (cmd is CallCmd)
            {
                CallCmd callCmd = cmd as CallCmd;
                int phaseSpecCallCmd = moverTypeChecker.FindPhaseNumber(callCmd.Proc);
                if (phaseSpecCallCmd > yTypeCheckCurrentPhaseNum)
                {
                    return true;

                }
            }
            return false;

        }


        /*
         * Visitor functions of basic commands
         */
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
                    if (QKeyValue.FindBoolAttribute(e.Attributes, "atomic"))
                    {
                        return "A";
                    }
                    else if (QKeyValue.FindBoolAttribute(e.Attributes, "right"))
                    {
                        return "R";
                    }
                    else if (QKeyValue.FindBoolAttribute(e.Attributes, "left"))
                    {
                        return "L";
                    }
                    else if (QKeyValue.FindBoolAttribute(e.Attributes, "both"))
                    {
                        return "B";
                    }
                }
            }
            //rest can only be assigncmd
            AssignCmd assgnCmd = cmd as AssignCmd;
            return "Q";

        }


        public string PrintGraph(Graph<int> graph, Implementation yTypeChecked, Dictionary<Tuple<int, int>, string> edgeLabels)
        {
            var s = new StringBuilder();
            s.AppendLine("\nImplementation " + yTypeChecked.Proc.Name + " digraph G {");
            foreach (var e in graph.Edges)
                s.AppendLine("  \"" + e.Item1.ToString() + "\" -- " + edgeLabels[e] + " --> " + "  \"" + e.Item2.ToString() + "\";");
            s.AppendLine("}");
            return s.ToString();
        }

        // Dragon Book Pagepg 662
        /*
         * Parameter : backEdge : is an Yield transition in the graph. Compute all backward edges based on predecessors of this node.  
         *                        This is called for every edge X, CollectBackEdges(graph,X) that has cond "Y".
         * Return: HashSet<Tuple<int, int>> yieldingEdges : set of edges that can be reached by backEdge which has Y(yield) condition
         */
        private HashSet<Tuple<int, int>> CollectBackEdges(Graph<int> g, Tuple<int, int> backEdge)
        {
            int n = backEdge.Item1;
            int d = backEdge.Item2;

            HashSet<int> loop = new HashSet<int>();
            Stack<int> stack = new Stack<int>();
            HashSet<Tuple<int, int>> yieldReachingEdges = new HashSet<Tuple<int, int>>();
            loop.Add(d);
            if (!n.Equals(d)) // then n is not in loop
            {
                loop.Add(n);
                stack.Push(n); // push n onto stack
#if (DEBUG && !DEBUG_DETAIL)
                Console.Write("\n First pushed item on stack is " + n.ToString());
#endif
            }
            while (stack.Count > 0) // not empty
            {
                int m = stack.Peek();
#if (DEBUG && !DEBUG_DETAIL)
                Console.Write("\n Back is : " + m.ToString() + "\n");
#endif
                stack.Pop(); // pop stack
                foreach (int p in g.Predecessors(m))
                {
                    // Contract.Assert(p!= null);
                    if (!(loop.Contains(p)))
                    {
                        Tuple<int, int> yieldReaching = new Tuple<int, int>(p, m);
                        yieldReachingEdges.Add(yieldReaching);
#if (DEBUG && !DEBUG_DETAIL)
                        Console.Write("\n " + p.ToString() + " --> " + m.ToString() + "\n");
#endif
                        loop.Add(p);
                        stack.Push(p); // push p onto stack
                    }
                }
            }
            return yieldReachingEdges;
        }
        /*
         * Calls CollectBackEdges for each Y edge existing in graph
         */
        private HashSet<Tuple<int, int>> BackwardEdgesOfYields(Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels)
        {
            HashSet<Tuple<int, int>> yieldTrueEdges = new HashSet<Tuple<int, int>>();
            foreach (var e in graph.Edges)
            {
                if (edgeLabels[e] == "Y")
                {
                    HashSet<Tuple<int, int>> yieldReachingEdges = CollectBackEdges(graph, e);
                    foreach (Tuple<int, int> yldrch in yieldReachingEdges)
                    {
#if (DEBUG && !DEBUG_DETAIL)
                        Console.Write("\n" + " From :" + yldrch.Item1.ToString() + " To :" + yldrch.Item2.ToString() + "\n");
#endif
                        yieldTrueEdges.Add(yldrch);
                    }
                }
            }
            return yieldTrueEdges;
        }

        /*
         * Updates vertices map according to according to yieldReaching edges. If an edge in graph is not yield reaching that its vertices map updated.
         */
        private void PostProcessGraph(Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels)
        {
            HashSet<Tuple<int, int>> yieldTrueEdges = BackwardEdgesOfYields(graph, edgeLabels);


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

        private int[] ComputeFinalStates(List<int> finalStates)
        {
            int[] finalS = new int[finalStates.Count];
            for (int i = 0; i < finalStates.Count; i++)
            {
                finalS[i] = finalStates[i];
            }
#if (DEBUG && !DEBUG_DETAIL)
            for (int i = 0; i < finalStates.Count; i++)
            {
                Console.Write("\nAn final state : \n");
                Console.Write(finalStates[i].ToString() + " ");
            }
#endif
            return finalS;
        }

        private List<int> ComputeInitalStates(List<int> initialStates)
        {

#if (DEBUG && !DEBUG_DETAIL)
            for (int i = 0; i<initialStates.Count;i++ )
            {
                Console.Write("\nAn initial state : \n");
                Console.Write(initialStates[i].ToString() + " ");
        }
#endif
            return initialStates;
        }

        private Automaton<BvSet> BuildAutomaton(Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels, List<int> initialStates, List<int> finalStates)
        {
            //List<Move<YieldTypeSet>> transitions = new List<Move<YieldTypeSet>>();
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

#if (DEBUG && !DEBUG_DETAIL)
            Console.Write(" \n Transitions before EPSILONS are added\n ");
            for (int i = 0; i < transitions.Count; i++)
            {
                int[] trans = transitions[i];
                Console.Write("\n From : " + trans[0].ToString() + "--- " + trans[1] + " --- " + " to : " + trans[3].ToString());
            }
#endif
            var solver = new CharSetSolver();

            // get initial states 
            List<int> initialSts = ComputeInitalStates(initialStates);

            // get final states
            int[] finalSts = ComputeFinalStates(finalStates);

            // Take one initial state from initial states
            int source = initialStates[0];
            foreach (int s in initialStates)
            {
                if (!s.Equals(source))
                {
                    int[] transition = new int[4];
                    transition[0] = source;
                    transition[1] = -1;
                    transition[2] = -1;
                    transition[3] = s;
                    transitions.Add(transition);
                }
            }

#if (DEBUG && !DEBUG_DETAIL)
            Console.Write(" \n Transitions are\n ");
            for (int i = 0; i < transitions.Count; i++)
            {
                int[] trans = transitions[i];
                Console.Write("\n From : " + trans[0].ToString() + "--- " + trans[1] + " --- " + " to : " + trans[3].ToString());
            }
#endif

            // create Automaton
            Automaton<BvSet> yieldTypeCheckAutomaton = solver.ReadFromRanges(source, finalSts, transitions);

#if (DEBUG && DEBUG_DETAIL)
            //   Console.Write("\n" + ytypeChecked.Proc.Name + " Automaton \n");
            Console.Write("\n" + "Number of moves " + yieldTypeCheckAutomaton.MoveCount.ToString() + "\n");
            Console.Write("\n" + "Number of states " + yieldTypeCheckAutomaton.StateCount.ToString() + "\n");
            foreach (var move in yieldTypeCheckAutomaton.GetMoves())
            {
                // Ask Margus,Shaz : BvSet concerns !
                Console.WriteLine(move.SourceState.ToString() + " " + move.Condition.ToString() + " " + move.TargetState.ToString());
                //solver.ShowDAG(yieldTypeCheckAutomaton,ytypeChecked.Proc.Name+" Automaton");
                // solver.ShowGraph(yieldTypeCheckAutomaton,ytypeChecked.Proc.Name+" Automaton");
            }
#endif
            //create Automaton
            //Automaton<YieldTypeSet> yieldTypeCheckAutomaton = Automaton<YieldTypeSet>.Create(concreteInitialState, finalStates, transitions); ;
            return yieldTypeCheckAutomaton;
        }
    }

}


#endif