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
        static CharSetSolver yieldCheckerAutomatonSolver;
        static string yieldReachabilityCheckerRegex = @"^([1234])*([D]+([56781234])*A*([973])*)*$";// regex of property to build automaton of YTS language      
        static Automaton<BvSet> yieldReachabilityCheckerAutomaton;
        static Automaton<BvSet> minimizedReachabilityCheckerAutomaton;
        static Automaton<BvSet> yieldTypeSafeCheckerAutomaton;
        static Automaton<BvSet> minimizedYieldTypeSafeCheckerAutomaton;

        static YieldTypeChecker()
        {
            yieldCheckerAutomatonSolver = new CharSetSolver(BitWidth.BV7);
            yieldReachabilityCheckerAutomaton =
                Automaton<BvSet>.MkProduct(yieldCheckerAutomatonSolver.Convert(yieldReachabilityCheckerRegex),
                                           yieldCheckerAutomatonSolver.Convert(@"^[1-9A-D]*$"), // result of product with this Automaton provides us an automaton that has (*) existence alphanum chars in our property automaton 
                                           yieldCheckerAutomatonSolver);
            minimizedReachabilityCheckerAutomaton = yieldReachabilityCheckerAutomaton.Determinize(yieldCheckerAutomatonSolver).Minimize(yieldCheckerAutomatonSolver);

            yieldTypeSafeCheckerAutomaton = yieldCheckerAutomatonSolver.ReadFromRanges(
                                            0,
                                           new int[] { 0, 2 },
                                           new int[][] { 
                                               // self loop on state 0 transitions
                                                new int[] { 0,51,51,0 }, // Q
                                                new int[] {0,68,68,0},// Y
                                               //0 to 1 transitions
                                                new int[] { 0,65,65,1 },//A
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

#if DEBUG && DEBUG_DETAIL
            yieldCheckerAutomatonSolver.ShowGraph(minimizedReachabilityCheckerAutomaton, "minimizedReachabilityPropertyAutomaton.dgml");
            yieldCheckerAutomatonSolver.ShowGraph(minimizedYieldTypeSafeCheckerAutomaton, "minimizedTypeSafePropertyAutomaton.dgml");
#endif
        }
        /*
         ComputePhaseIntervals :
         1.1 Input parameters : 
           1.1.1 Implementation impl : Implementation whose body is being YTS checked.
           1.1.2 int specPhaseNumImpl : Phase number in which procedure of implementation, impl, reaches its specification,{A,R,L,B}
           1.1.3 MoverTypeChecker moverTypeChecker : moverTypeChecker is the integration point of YieldTypeChecker to OG class. moverTypeChecker has functions enables YieldTypeChecker to find phaseNum and spec of procedures.

         1.2 Return value : is a list of tuples(phase interval start,phase interval end). Every tuple in this list is representing an interval formed by callCmds' phase numbers inside impl.			   
         1.3 Action : This function first traverses the blocks inside impl, collects all CallCmds inside it into a HashSet ,callCmdsInImpl. 
                *      Then it puts all these callCmds' phase numbers into a HashSet,callCmdPhaseNumSet. 
                *     After adding all callCmds' phase numbers' it adds phase number of procedure of impl into the set. 
                *     It sorts all numbers in this set and creates [-inf...n-1] [n...k-1] [k  PhaseNumProcOfImpl] disjoint intervals.
          */
        private static List<Tuple<int, int>> ComputePhaseIntervals(Implementation impl, int specPhaseNumImpl, MoverTypeChecker moverTypeChecker)
        {
            HashSet<CallCmd> callCmdsInImpl = new HashSet<CallCmd>(); //  callCmdsInImpl[Implementation] ==> Set = { call1, call2, call3 ... }
            HashSet<ParCallCmd> parCallCmdsInImpl = new HashSet<ParCallCmd>();
            List<Tuple<int, int>> phaseIntervals = new List<Tuple<int, int>>(); // [MinValue ph0 ] [ph0 ph1] [ph1 ph2] ..... [phk phk+1] intervals

            //Get max of callcmds in 
            foreach (Block b in impl.Blocks)
            {
                for (int i = 0; i < b.Cmds.Count; i++)
                {
                    ParCallCmd parCallCmd = b.Cmds[i] as ParCallCmd;
                    if (parCallCmd == null) continue;
                    parCallCmdsInImpl.Add(parCallCmd);
                }
            }

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

            foreach (ParCallCmd parCallCmd in parCallCmdsInImpl)
            {
                List<int> phaseNumsInParCall = new List<int>();
                foreach (CallCmd callInParCallCmd in parCallCmd.CallCmds)
                {
                    phaseNumsInParCall.Add(moverTypeChecker.FindPhaseNumber(callInParCallCmd.Proc));
                }
                callCmdPhaseNumSet.Add(phaseNumsInParCall.Max());
            }

            foreach (CallCmd callCmd in callCmdsInImpl)
            {
                int tmpPhaseNum = moverTypeChecker.FindPhaseNumber(callCmd.Proc);
                callCmdPhaseNumSet.Add(tmpPhaseNum);
            }
            callCmdPhaseNumSet.Add(specPhaseNumImpl);

            List<int> callCmdPhaseNumList = callCmdPhaseNumSet.ToList();
            callCmdPhaseNumList.Sort();

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
            for (int i = 0; i < phaseIntervals.Count; i++)
            {
                Console.Write("\n Phase " + i.ToString() + "[" + phaseIntervals[i].Item1.ToString() + "," + phaseIntervals[i].Item2.ToString() + "]" + "\n");
            }
#endif
            return phaseIntervals;
        }



        /*
  IsYieldReachabilitySafe :
    2.1 Input parameters :
      2.1.1 Automaton<BvSet> implTypeCheckAutomaton : This input Automaton is generated for a phase of YTS checking of an impl.
    2.2 Return value : returns true if input automaton is subset of YTS property autoamaton.
    2.3 Action : Subset checking for a phase of an implementation. f L(YTSI) is subset of L(YTSP) {TRUE} else {FALSE}  
  */
        public static bool IsYieldReachabilitySafe(Automaton<BvSet> implReachabilityCheckAutomaton, Implementation impl, MoverTypeChecker moverTypeChecker, int phaseNum)
        {

            List<BvSet> witnessSet;

            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                           implReachabilityCheckAutomaton,
                                                           yieldReachabilityCheckerAutomaton,
                                                           0,
                                                           yieldCheckerAutomatonSolver,
                                                           out witnessSet);

#if DEBUG && !DEBUG_DETAIL
            
            var diffAutomaton = implReachabilityCheckAutomaton.Minus(yieldReachabilityCheckerAutomaton, yieldCheckerAutomatonSolver);
            string diffAutomatonGraphName = "diffAutomatonReachabilitySafe" + impl.Proc.Name + phaseNum.ToString();
            yieldCheckerAutomatonSolver.ShowGraph(diffAutomaton, diffAutomatonGraphName+".dgml");
#endif

#if !DEBUG && !DEBUG_DETAIL
            string s = yieldTypeCheckerAutomatonSolver.GenerateMember(implTypeCheckAutomaton);
            Console.WriteLine("\n member " + s+ " \n");
            if(!yieldTypeCheckerAutomatonSolver.Accepts(yieldTypeCheckerAutomaton,s)){
                Console.WriteLine("Property Automaton accepts a random member of impl_automaton " + s);
            }else{
                Console.WriteLine("Property Automaton does not accept a random member of impl_automaton " + s);
            }
#endif
            if (isNonEmpty)
            {
                var witness = new String(Array.ConvertAll(witnessSet.ToArray(), bvset => (char)yieldCheckerAutomatonSolver.Choose(bvset)));
                moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " has invalid trace of actions w.r.t yield reachability :  " + witness + "\n");
                return false;
            }

            return true;
        }

        public static bool IsYieldTypeSafe(Automaton<BvSet> implTypeSafeCheckAutomaton, Implementation impl, MoverTypeChecker moverTypeChecker, int phaseNum)
        {

            List<BvSet> witnessSet;

            var isNonEmpty = Automaton<BvSet>.CheckDifference(
                                                           implTypeSafeCheckAutomaton,
                                                           yieldTypeSafeCheckerAutomaton,
                                                           0,
                                                           yieldCheckerAutomatonSolver,
                                                           out witnessSet);

#if DEBUG && !DEBUG_DETAIL

            var diffAutomaton = implTypeSafeCheckAutomaton.Minus(yieldTypeSafeCheckerAutomaton, yieldCheckerAutomatonSolver);
            string diffAutomatonGraphName = "diffAutomatonTypeSafety" + impl.Proc.Name + phaseNum.ToString();
            yieldCheckerAutomatonSolver.ShowGraph(diffAutomaton, diffAutomatonGraphName + ".dgml");
#endif

#if !DEBUG && !DEBUG_DETAIL
            string s = yieldTypeCheckerAutomatonSolver.GenerateMember(implTypeCheckAutomaton);
            Console.WriteLine("\n member " + s+ " \n");
            if(!yieldTypeCheckerAutomatonSolver.Accepts(yieldTypeCheckerAutomaton,s)){
                Console.WriteLine("Property Automaton accepts a random member of impl_automaton " + s);
            }else{
                Console.WriteLine("Property Automaton does not accept a random member of impl_automaton " + s);
            }
#endif
            if (isNonEmpty)
            {
                var witness = new String(Array.ConvertAll(witnessSet.ToArray(), bvset => (char)yieldCheckerAutomatonSolver.Choose(bvset)));
                moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " has invalid trace of actions w.r.t yield type safety :  " + witness + "\n");
                return false;
            }

            return true;
        }

        /*
PerformYieldSafeCheck : 
 3.1 Input parameters :
   3.1.1 MoverTypeChecker moverTypeChecker : 
 3.2 Action : This function is called in TypeCheck.cs. This is the only function that is externalized. This function traverses the program declarations and performs
        */
        public static void PerformYieldSafeCheck(MoverTypeChecker moverTypeChecker)
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
                    int yTypeCheckCurrentPhaseNum = phaseIntervals[i].Item1;
                    Tuple<Automaton<BvSet>,Automaton<BvSet>> yieldCheckAutomatons=yieldTypeCheckerPerImpl.YieldTypeCheckAutomaton(impl, phaseNumSpecImpl, yTypeCheckCurrentPhaseNum);
                  //  Automaton<BvSet> yieldTypeSafeCheckAutoPerPhase = yieldTypeCheckerPerImpl.YieldTypeCheckAutomaton(impl, phaseNumSpecImpl, yTypeCheckCurrentPhaseNum).Item1;
                    if (!IsYieldReachabilitySafe(yieldCheckAutomatons.Item2, impl, moverTypeChecker, yTypeCheckCurrentPhaseNum) &&
                        !IsYieldTypeSafe(yieldCheckAutomatons.Item1, impl, moverTypeChecker, yTypeCheckCurrentPhaseNum))
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_type safe " + "\n");
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_reachable safe " + "\n");

                    }
                    else if (IsYieldReachabilitySafe(yieldCheckAutomatons.Item2, impl, moverTypeChecker, yTypeCheckCurrentPhaseNum) &&
                            !IsYieldTypeSafe(yieldCheckAutomatons.Item1, impl, moverTypeChecker, yTypeCheckCurrentPhaseNum))
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_type safe " + "\n");
                    }
                    else if (!IsYieldReachabilitySafe(yieldCheckAutomatons.Item2, impl, moverTypeChecker, yTypeCheckCurrentPhaseNum) &&
                           IsYieldTypeSafe(yieldCheckAutomatons.Item1, impl, moverTypeChecker, yTypeCheckCurrentPhaseNum))
                    {
                        moverTypeChecker.Error(impl, "\n Body of " + impl.Proc.Name + " is not yield_reachable safe " + "\n");
                    }
                }
            }
        }
    }

    /*
    * Functionality : This class performs building an automaton for a particular phase on an implementation. 
    * Please don't get confused when you see that its constructor is not called for every phase. 
    * We call YieldTypeCheckAutomata function of this class for every phase, real constructor for us just to have its name more intuitive.
    */
    class YieldTypeCheckerCore
    {

        int stateCounter;
        MoverTypeChecker moverTypeChecker;
        CharSetSolver solver;
        public YieldTypeCheckerCore(MoverTypeChecker moverTypeChecker)
        {
            solver = new CharSetSolver(BitWidth.BV7);
            this.moverTypeChecker = moverTypeChecker;
        }

        /*
 YieldTypeCheckAutomata
   1.1 Input parameters
     1.1.1 Implementation ytypeChecked : impl being YTS checked.
     1.1.2 int specPhaseNumImpl: Phase num that procedure of impl has its specification{A,L,B,R}, last intervals end point.
     1.1.3 int yTypeCheckCurrentPhaseNum : current phase checking number that taken from every phase intervals end point.
     foreach phase [s...e] in PhaseIntervals
     yTypeCheckCurrentPhaseNum = e;
     Please note that we have disjoint intervals. Note : I have to check the comparison. 
   1.2 Return value : Automaton<BvSet>  : returns Automaton for a particular phase.
   1.3 Action : This function is summary of whole YieldTypeCheckerCore class. This function is called for every phase from YieldTypeCheck.PerformYieldTypeCheck function. It has the following flow : It has following local data structure which will be passed into other functions of execution flow to create Automaton of a phase.
         a. Dictionary<Tuple<int, int>, string> edgeLabels : // Tuple<int,int> --> "Y" :  //State(k) --Y--> State(k+1)
         b. Dictionary<Absy, int> abysToNode = CreateStateNumbers(ytypeChecked, yTypeCheckCurrentPhaseNum);
        
         Enumerates states in the body of impl using stateCounter.				
         c. List<int> finalStates 
         d. List<int> initialStates
         e. stateCounter = 0 // Whenever this function is called it to create AutoPerPhase it starts with stateCounter 0.
         Execution flow :
         f. Graph<int> bodyGraphForImplPhaseJ = BuildAutomatonGraph(ytypeChecked, yTypeCheckCurrentPhaseNum,abysToNode,edgeLabels,initialStates, finalStates)
         h. PostProcessGraph(bodyGraphForImplPhaseJ, edgeLabels) : Takes bodyGraphForImplPhaseJ graph and process Yield Reaching Edge (YRE) on this graph and updates Y non-reaching edges' labels and Y reaching edges' labels in edgesLabels dictionary , <Key: Edge, value : EdgeLableString>

        Note : Change name of this function !
								
         g. BuildAutomaton(bodyGraphForImplPhaseJ, edgeLabels, initialStates, finalStates) :Builds Automaton after YRE process.
          */
        public Tuple<Automaton<BvSet>, Automaton<BvSet>> YieldTypeCheckAutomaton(Implementation ytypeChecked, int specPhaseNumImpl, int yTypeCheckCurrentPhaseNum)
        {

            Dictionary<Tuple<int, int>, string> edgeLabels = new Dictionary<Tuple<int, int>, string>(); // Tuple<int,int> --> "Y" : State(k) --Y--> State(k+1)

            Dictionary<Absy, int> abysToNode = CreateStateNumbers(ytypeChecked, yTypeCheckCurrentPhaseNum);
            List<int> finalStates = new List<int>();
            List<int> initialStates = new List<int>();
            stateCounter = 0;
            initialStates.Add(stateCounter); // First state is added to initial states
            Graph<int> bodyGraphForImplPhaseJ = BuildAutomatonGraph(ytypeChecked, yTypeCheckCurrentPhaseNum, abysToNode, edgeLabels, initialStates, finalStates); // build component of graph for a phase interval            

#if (DEBUG && !DEBUG_DETAIL)
            Console.Write("\n Procedure's phase num is " + specPhaseNumImpl.ToString() + " \n");
            Console.Write("\n YieldTypeSafe Graph is created for phase: \n" + yTypeCheckCurrentPhaseNum.ToString());
            Console.Write(PrintGraph(bodyGraphForImplPhaseJ, ytypeChecked, edgeLabels));
#endif
            Automaton<BvSet> implYieldTypeSafeCheckAutomaton = BuildAutomatonYieldTypeSafe(bodyGraphForImplPhaseJ, edgeLabels, initialStates, finalStates, ytypeChecked, yTypeCheckCurrentPhaseNum);


            // Update edges w.r.t yield reaching. VocabX{True,False} 
            PostProcessGraph(bodyGraphForImplPhaseJ, edgeLabels);
#if (DEBUG && !DEBUG_DETAIL)
            Console.Write("\n Procedure's phase num is " + specPhaseNumImpl.ToString() +" \n");
            Console.Write("\n YieldReachabilityCheck Graph is created for phase : \n" + yTypeCheckCurrentPhaseNum.ToString());
            Console.Write(PrintGraph(bodyGraphForImplPhaseJ, ytypeChecked, edgeLabels));
#endif
            //Build Automaton from graph created
            Automaton<BvSet> implYieldReachCheckAutomaton = BuildAutomatonYieldReachSafe(bodyGraphForImplPhaseJ, edgeLabels, initialStates, finalStates, ytypeChecked, yTypeCheckCurrentPhaseNum); // Last to arguments are just only for showGraph of automaton lib

            Tuple<Automaton<BvSet>, Automaton<BvSet>> yieldCheckImplAutomaton = new Tuple<Automaton<BvSet>, Automaton<BvSet>>(implYieldTypeSafeCheckAutomaton, implYieldReachCheckAutomaton);
            return yieldCheckImplAutomaton;
        }

        /*
        CreateStateNumbers
        2.1 Input parameters : 
        2.1.1 Implementation ytypeChecked
        2.1.2 int yTypeCheckCurrentPhaseNum
        2.2 Return value :Dictionary<Absy, int> : returns KeyValuePair as <Key:Command ::= TransferCmd | SimpleCmd | ParCallCmd , Value: state as int>
        2.3 Action :This function creates state numbers of a given body of an impl using incrementing stateCounter. It keeps KeyValuePair as <Key:Command ::= TransferCmd | SimpleCmd , Value: state as int, absy2NodeNo.
        */
        public Dictionary<Absy, int> CreateStateNumbers(Implementation ytypeChecked, int yTypeCheckCurrentPhaseNum)
        {
            Dictionary<Absy, int> abysToNodeNo = new Dictionary<Absy, int>();
            /*
            * Lets call this impl body traversing framework : ITF
               foreach block in Impl.Blocks 
                   foreach cmd in block.Cmds
                       absy2NodeNo[cmd] = stateCounter
                       stateCouner++
                   absy2NodeNo[block.TransferCmd] = stateCounter
                   stateCounter++

            */
            foreach (Block block in ytypeChecked.Blocks)
            {
                foreach (Cmd cmd in block.Cmds)
                {

                    if (IsAsyncCallCmd(cmd)) continue;
#if DEBUG && !DEBUG_DETAIL 
                    if (IsProperActionCmd(cmd, yTypeCheckCurrentPhaseNum)) {  Console.WriteLine( cmd.ToString() + " proper action"); }
                    if (IsCallCmdExitPoint(cmd,yTypeCheckCurrentPhaseNum)) { Console.WriteLine(cmd.ToString() + " call exit action"); }
                    if (IsParallelCallCmdYield(cmd, yTypeCheckCurrentPhaseNum)) { Console.WriteLine( cmd.ToString() + " call parallel action"); }
                    if (IsSeqComposableParCallCmd(cmd, yTypeCheckCurrentPhaseNum)) { Console.WriteLine( cmd.ToString() + " call composable parallel action"); }
#endif
                    if (cmd is ParCallCmd)
                    {
                        ParCallCmd calle = cmd as ParCallCmd;
                        for (int i = 0; i < calle.CallCmds.Count; i++)
                        {
                            abysToNodeNo[calle.CallCmds[i]] = stateCounter;
#if DEBUG && !DEBUG_DETAIL
                            Console.WriteLine("ParCmd " + calle.CallCmds[i].Proc.Name + " state " + stateCounter.ToString());
#endif
                            stateCounter++;
                        }

                    }
                    else
                    {
                        abysToNodeNo[cmd] = stateCounter;
                        // Console.WriteLine("Cmd " + cmd.ToString() + " state " + stateCounter.ToString());
                        stateCounter++;
                    }

                }
                abysToNodeNo[block.TransferCmd] = stateCounter;
                // Console.WriteLine("Cmd " + block.TransferCmd.ToString() + " state " + stateCounter.ToString());
                stateCounter++;
            }
            return abysToNodeNo;
        }

        /*
BuildAutomatonGraph: 
3.1 Input parameters : Parameters are mentioned above.
3.1.1 Implementation ytypeChecked : 
3.1.2 int yTypeCheckCurrentPhaseNum
3.1.3 Dictionary<Absy, int> bodyGraphForImplPhaseJ
3.1.4 Dictionary<Tuple<int, int>, string> edgeLabels
3.1.5 List<int> initialStates
3.1.6 List<int> finalStates
3.2 Return value: Graph<int> : This function keeps internal data structure ,HashSet<Tuple<int,int>>edges, to store edges that are formed using 
      an edge =Tuple< bodyGraphForImplPhaseJ[  Command ::= TransferCmdS | SimpleCmdS ] -> stateS,bodyGraphForImplPhaseJ[  Command ::= TransferCmdD | SimpleCmdD ] -> stateD>
      returns Grap<int> grph = new Graph<int>(HashSet<edge>).

3.3 Action: In this function we use ITF framework to traverse body of implementation. get states as mentioned 3.2, form edges, put them into set edges and form graph from this set of edges. So many complexities can arise while forming edges if CallCmds are encountered during traversing with ITF.
We use bool IsCallCmdExitPoint(Cmd cmd, int yTypeCheckCurrentPhaseNum)  returns true if cmd is CallCmd and its phase specification num is greater than the current type check phase num passed as second argument.This means that this call cmd forms an exit point for this YTS check.

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
                        //IsProper
                        if (IsProperActionCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsProperActionCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))// this is handled in else but keep this branch now
                        { // proper state transition
                            int source = bodyGraphForImplPhaseJ[block.Cmds[i]];
                            int dest = bodyGraphForImplPhaseJ[block.Cmds[i + 1]];
                            //Console.Write("\n >=2 Adding proper transition " + source.ToString() + " --> " + dest.ToString());
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsProperActionCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsCallCmdExitPoint(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            int source = bodyGraphForImplPhaseJ[block.Cmds[i]];
                            // create artificial final state
                            int dest = Math.Abs(Guid.NewGuid().GetHashCode()); // Generate unique dummy node ref: http://msdn.microsoft.com/en-us/library/system.guid(v=vs.110).aspx
                            //Console.Write("\n >=2 Adding next is EXT transition " + source.ToString() + " --> " + dest.ToString());
                            finalStates.Add(dest);
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsProperActionCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsParallelCallCmdYield(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            int source = bodyGraphForImplPhaseJ[block.Cmds[i]];
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            int dest = bodyGraphForImplPhaseJ[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        else if (IsProperActionCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsSeqComposableParCallCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            int source = bodyGraphForImplPhaseJ[block.Cmds[i]];
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;
                            int dest = bodyGraphForImplPhaseJ[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        // IsCallCmdsExit
                        else if (IsCallCmdExitPoint(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsProperActionCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        { // current cmd exit , next cmd will be put as initial state
                            //Console.Write("\n >=2 Adding current cmd is EXT next initial" + bodyGraphForImplPhaseJ[block.Cmds[i + 1]].ToString());
                            initialStates.Add(bodyGraphForImplPhaseJ[block.Cmds[i + 1]]);

                        }
                        else if (IsCallCmdExitPoint(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsCallCmdExitPoint(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            continue;
                        }
                        else if (IsCallCmdExitPoint(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsParallelCallCmdYield(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            // Add state number CallCmd of ParallelCmd
                            ParCallCmd nextCmd = block.Cmds[i+1] as ParCallCmd;
                            initialStates.Add(bodyGraphForImplPhaseJ[nextCmd.CallCmds[0]]);
                        }
                        else if (IsCallCmdExitPoint(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsSeqComposableParCallCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            // Add state number CallCmd of ParallelCmd
                            ParCallCmd nextCmd = block.Cmds[i+1] as ParCallCmd;
                            initialStates.Add(bodyGraphForImplPhaseJ[nextCmd.CallCmds[0]]);

                        }
                        // ParallelCallCmdYield
                        else if (IsParallelCallCmdYield(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsParallelCallCmdYield(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[0]];
                            int dest = bodyGraphForImplPhaseJ[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsParallelCallCmdYield(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsSeqComposableParCallCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[0]];
                            int dest = bodyGraphForImplPhaseJ[nextCmd.CallCmds[0]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsParallelCallCmdYield(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsCallCmdExitPoint(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            //create dummy state as next state
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[0]];
                            int dest = Math.Abs(Guid.NewGuid().GetHashCode()); // Generate unique dummy node 
                            //Console.Write("\n >=2 Adding next is EXT transition " + source.ToString() + " --> " + dest.ToString());
                            finalStates.Add(dest);
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }
                        else if (IsParallelCallCmdYield(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsProperActionCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[0]];
                            int dest = bodyGraphForImplPhaseJ[block.Cmds[i + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));
                        }
                        //SeqComposable Parallel Cmd
                        else if (IsSeqComposableParCallCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsSeqComposableParCallCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                            {
                                int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j]];
                                int dest = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j + 1]];
                                Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                                edges.Add(edge);
                                edgeLabels.Add(edge, GetEdgeType(block.Cmds[j]));
                            }

                            // Peelout last iteration
                            int sourceBtwCalls = bodyGraphForImplPhaseJ[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                            int destBtwCalls = bodyGraphForImplPhaseJ[nextCmd.CallCmds[0]];
                            Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                            edges.Add(edgeBtw);
                            edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));
                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsParallelCallCmdYield(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            ParCallCmd nextCmd = block.Cmds[i + 1] as ParCallCmd;

                            for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                            {
                                int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j]];
                                int dest = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j + 1]];
                                Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                                edges.Add(edge);
                                edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                            }
                            // Peelout last iteration
                            int sourceBtwCalls = bodyGraphForImplPhaseJ[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                            int destBtwCalls = bodyGraphForImplPhaseJ[nextCmd.CallCmds[0]];
                            Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                            edges.Add(edgeBtw);
                            edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));
                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsCallCmdExitPoint(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;
                            for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                            {
                                int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j]];
                                int dest = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j + 1]];
                                Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                                edges.Add(edge);
                                edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                            }
                            // Peelout last iteration
                            int sourceBtwCalls = bodyGraphForImplPhaseJ[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                            int destBtwCalls = Math.Abs(Guid.NewGuid().GetHashCode()); // Generate unique dummy node 
                            //Console.Write("\n >=2 Adding next is EXT transition " + source.ToString() + " --> " + dest.ToString());
                            finalStates.Add(destBtwCalls);
                            Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                            edges.Add(edgeBtw);
                            edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));

                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[i], yTypeCheckCurrentPhaseNum) && IsProperActionCmd(block.Cmds[i + 1], yTypeCheckCurrentPhaseNum))
                        {
                            ParCallCmd currentCmd = block.Cmds[i] as ParCallCmd;

                            for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                            {
                                int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j]];
                                int dest = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j + 1]];
                                Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                                edges.Add(edge);
                                edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                            }
                            // Peelout last iteration
                            int sourceBtwCalls = bodyGraphForImplPhaseJ[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                            int destBtwCalls = bodyGraphForImplPhaseJ[block.Cmds[i + 1]]; // Generate unique dummy node 
                            Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                            edges.Add(edgeBtw);
                            edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));
                        }/*
                        else
                        {// Do proper transition 
                            int source = bodyGraphForImplPhaseJ[block.Cmds[i]];
                            int dest = bodyGraphForImplPhaseJ[block.Cmds[i + 1]];
                            //  Console.Write("\n >=2 Adding proper transitionels " + source.ToString() + " --> " + dest.ToString());
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(block.Cmds[i]));

                        }*/
                    }


                    if (IsCallCmdExitPoint(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum))
                    { // put b.TransferCmd into initial states
                        //Console.Write("\n >=2 Last cmd is EXT put current as initial " + bodyGraphForImplPhaseJ[block.TransferCmd].ToString());

                        initialStates.Add(bodyGraphForImplPhaseJ[block.TransferCmd]);
                    }
                    /* else if (IsAsyncCallCmd(block.Cmds[block.Cmds.Count - 1])) { }*/
                    else if (IsParallelCallCmdYield(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum))
                    {
                        ParCallCmd currentCmd = block.Cmds[block.Cmds.Count - 1] as ParCallCmd;
                        int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[0]];
                        int dest = bodyGraphForImplPhaseJ[block.TransferCmd];
                        //Console.Write("\n >=2 Adding proper transitionels " + source.ToString() + " --> " + dest.ToString());                            
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[block.Cmds.Count - 1]));

                    }
                    else if (IsSeqComposableParCallCmd(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum))
                    {
                        ParCallCmd currentCmd = block.Cmds[block.Cmds.Count - 1] as ParCallCmd;

                        for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                        {
                            int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j]];
                            int dest = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                        }

                        int sourceBtwCalls = bodyGraphForImplPhaseJ[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                        int destBtwCalls = bodyGraphForImplPhaseJ[block.TransferCmd]; // Generate unique dummy node 
                        Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                        edges.Add(edgeBtw);
                        edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));

                    }
                    else if (IsProperActionCmd(block.Cmds[block.Cmds.Count - 1], yTypeCheckCurrentPhaseNum))
                    {
                        // proper transition to state before transfer command
                        int source = bodyGraphForImplPhaseJ[block.Cmds[block.Cmds.Count - 1]];
                        int dest = bodyGraphForImplPhaseJ[block.TransferCmd];
                        //Console.Write("\n >=2 Adding proper transitionels " + source.ToString() + " --> " + dest.ToString());                            
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[block.Cmds.Count - 1]));

                    }

                }
                else if (block.Cmds.Count == 1)
                {
                    if (IsCallCmdExitPoint(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                    { // put b.TransferCmd into initial states
                        //  Console.Write("\n == 1 current cmd is EXT "+block.Cmds[0].ToString()+" put it as initial " );
                        initialStates.Add(bodyGraphForImplPhaseJ[block.TransferCmd]);
                    }
                    else if (IsProperActionCmd(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                    { // proper transition to state before transfer command
                        int source = bodyGraphForImplPhaseJ[block.Cmds[0]];
                        int dest = bodyGraphForImplPhaseJ[block.TransferCmd];
                        //    Console.Write("\n ==1 Adding proper transition " + source.ToString() + " --> " + dest.ToString());

                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[0]));
                    }
                    else if (IsParallelCallCmdYield(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                    {
                        ParCallCmd currentCmd = block.Cmds[0] as ParCallCmd;
                        int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[0]];
                        int dest = bodyGraphForImplPhaseJ[block.TransferCmd];
                        //Console.Write("\n >=2 Adding proper transitionels " + source.ToString() + " --> " + dest.ToString());                            
                        Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                        edges.Add(edge);
                        edgeLabels.Add(edge, GetEdgeType(block.Cmds[0]));



                    }
                    else if (IsSeqComposableParCallCmd(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                    {
                        ParCallCmd currentCmd = block.Cmds[0] as ParCallCmd;

                        for (int j = 0; j < currentCmd.CallCmds.Count - 1; j++)
                        {
                            int source = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j]];
                            int dest = bodyGraphForImplPhaseJ[currentCmd.CallCmds[j + 1]];
                            Tuple<int, int> edge = new Tuple<int, int>(source, dest);
                            edges.Add(edge);
                            edgeLabels.Add(edge, GetEdgeType(currentCmd.CallCmds[j]));
                        }

                        int sourceBtwCalls = bodyGraphForImplPhaseJ[currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]];
                        int destBtwCalls = bodyGraphForImplPhaseJ[block.TransferCmd]; // Generate unique dummy node 
                        Tuple<int, int> edgeBtw = new Tuple<int, int>(sourceBtwCalls, destBtwCalls);
                        edges.Add(edgeBtw);
                        edgeLabels.Add(edgeBtw, GetEdgeType(currentCmd.CallCmds[currentCmd.CallCmds.Count - 1]));

                    }
                }
                else if (block.Cmds.Count == 0)
                {
                    // Target block Entry state will be fetched 
                    //Console.Write("\n == 0 \n" );

                }
                // Handle
                HashSet<int> targetBlockEntryStates = GetStateOfTargetBlock(block.TransferCmd, bodyGraphForImplPhaseJ, yTypeCheckCurrentPhaseNum, initialStates, finalStates);
                foreach (int entryState in targetBlockEntryStates)
                {
                    int source = bodyGraphForImplPhaseJ[block.TransferCmd];
                    Tuple<int, int> transferEdge = new Tuple<int, int>(source, entryState);
                    //Console.Write("\n Doing TC " + source.ToString() + " --> " + entryState.ToString());

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
                ReturnCmd returnCmd = tc as ReturnCmd;
                int source = bodyGraphForImplPhaseJ[tc];
                finalStates.Add(source);
                //Console.WriteLine(" There is a return baby ! " + source.ToString());                
                // Do Nothing
            }
            else if (tc is GotoCmd)
            {
                GotoCmd transferCmd = tc as GotoCmd;
                foreach (Block block in transferCmd.labelTargets)
                {
                    if (block.Cmds.Count == 0)
                    {
                        targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[block.TransferCmd]); //Target block is empty. Add state of target block's transfer command (Goto or Return) 
                    }
                    else if (block.Cmds.Count >= 1)
                    {
                        if (IsCallCmdExitPoint(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                        {
                            // Create artificial final state and put this into final states
                            int targetState = Math.Abs(Guid.NewGuid().GetHashCode());
                            finalStates.Add(targetState);
                            targetBlockEntryStates.Add(targetState);
                        }
                        else if (IsProperActionCmd(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                        {
                            targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[block.Cmds[0]]);
                        }
                        else if (IsParallelCallCmdYield(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                        {

                            ParCallCmd targetCmd = block.Cmds[0] as ParCallCmd;
                            targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[targetCmd.CallCmds[0]]);
                        }
                        else if (IsSeqComposableParCallCmd(block.Cmds[0], yTypeCheckCurrentPhaseNum))
                        {
                            ParCallCmd targetCmd = block.Cmds[0] as ParCallCmd;
                            targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[targetCmd.CallCmds[0]]);
                        }
                        else if (IsAsyncCallCmd(block.Cmds[0]))
                        {

                            if (block.Cmds.Count == 1)
                            {
                                targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[block.TransferCmd]);
                            }
                            else if (block.Cmds.Count > 1)
                            {
                                int existsNonAsync;
                                for (existsNonAsync = 0; existsNonAsync < block.Cmds.Count; existsNonAsync++)
                                {

                                    if (IsAsyncCallCmd(block.Cmds[existsNonAsync])) continue;

                                    else if (IsParallelCallCmdYield(block.Cmds[existsNonAsync], yTypeCheckCurrentPhaseNum))
                                    {
                                        ParCallCmd targetCmd = block.Cmds[existsNonAsync] as ParCallCmd;
                                        targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[targetCmd.CallCmds[0]]);
                                        break;
                                    }
                                    else if (IsSeqComposableParCallCmd(block.Cmds[existsNonAsync], yTypeCheckCurrentPhaseNum))
                                    {
                                        ParCallCmd targetCmd = block.Cmds[existsNonAsync] as ParCallCmd;
                                        targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[targetCmd.CallCmds[0]]);
                                        break;

                                    }
                                    else if (IsCallCmdExitPoint(block.Cmds[existsNonAsync], yTypeCheckCurrentPhaseNum))
                                    {
                                        int targetState = Math.Abs(Guid.NewGuid().GetHashCode());
                                        finalStates.Add(targetState);
                                        targetBlockEntryStates.Add(targetState);
                                        break;

                                    }
                                    else if (IsProperActionCmd(block.Cmds[existsNonAsync], yTypeCheckCurrentPhaseNum))
                                    {
                                        targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[block.Cmds[existsNonAsync]]);
                                        break;
                                    }

                                }

                                if (existsNonAsync == block.Cmds.Count)
                                {
                                    // put target 
                                    targetBlockEntryStates.Add(bodyGraphForImplPhaseJ[block.TransferCmd]); //Target block is empty. Add state of target block's transfer command (Goto or Return)
                                }
                            }
                        }
                    }
                }
            }
            return targetBlockEntryStates;
        }



        private bool IsProperActionCmd(Cmd cmd, int yTypeCheckCurrentPhaseNum)
        {
            if (!IsCallCmdExitPoint(cmd, yTypeCheckCurrentPhaseNum) &&
                !IsParallelCallCmdYield(cmd, yTypeCheckCurrentPhaseNum) &&
                !IsSeqComposableParCallCmd(cmd, yTypeCheckCurrentPhaseNum) &&
                !IsAsyncCallCmd(cmd))
            {
                return true;
            }
            return false;

        }

        private bool IsCallCmdExitPoint(Cmd cmd, int yTypeCheckCurrentPhaseNum)
        {
            if (cmd is CallCmd /*&& IsParallelCallCmdYield(cmd, yTypeCheckCurrentPhaseNum) &&
                IsSeqComposableParCallCmd(cmd, yTypeCheckCurrentPhaseNum) */&&
                !IsAsyncCallCmd(cmd))
            {
                CallCmd callee = cmd as CallCmd;
                int phaseSpecCallee = moverTypeChecker.FindPhaseNumber(callee.Proc);
                if (phaseSpecCallee >= yTypeCheckCurrentPhaseNum)
                {
#if DEBUG && !DEBUG_DETAIL
                    Console.Write("\nCall Cmd Check is " + callee.Proc.Name + "\n");
#endif
                    return true;

                }
            }
            return false;
        }

        private bool IsParallelCallCmdYield(Cmd cmd, int yTypeCheckCurrentPhaseNum)
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
        private bool IsSeqComposableParCallCmd(Cmd cmd, int yTypeCheckCurrentPhaseNum)
        {
            if (cmd is ParCallCmd && !IsParallelCallCmdYield(cmd, yTypeCheckCurrentPhaseNum))
                return true;
            return false;
        }

        private bool IsAsyncCallCmd(Cmd cmd)
        {
            if (cmd is CallCmd)
            {
                CallCmd calle = cmd as CallCmd;
                if (calle.IsAsync)
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
            else if (cmd is ParCallCmd) // A small trick here : While getting type of SeqCompositional_parCall_commands we pass CallCmd typed parameter
            {
                return "Y";
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


        private HashSet<Tuple<int, int>> CollectBackwardEdgesOfYieldEdge(Graph<int> g, int source)
        {
            HashSet<Tuple<int, int>> yieldReachingEdges = new HashSet<Tuple<int, int>>(); // Collect edges that are backward reachable from source vertex of yield a edge,source ---Y---> sink, in backward direction
            HashSet<int> gray = new HashSet<int>();
            HashSet<int> black = new HashSet<int>();
            HashSet<int> white = new HashSet<int>();
            // Add all vertices except s into 
            foreach (int v in g.Nodes)
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
                foreach (int v in g.Predecessors(u))
                {
#if DEBUG && !DEBUG_DETAIL
                    Console.Write("\nVertex " + u.ToString() + " is currently being explored for " + v.ToString() + "\n");
#endif
                    if (white.Contains(v) && !gray.Contains(v) && !black.Contains(v))
                    {
#if DEBUG && !DEBUG_DETAIL
                        Console.Write(v.ToString() + " is not explored beforehand \n");
#endif
                        gray.Add(v);
                        frontier.Enqueue(v);
                        // Add to yielding edges
                        yieldReachingEdges.Add(new Tuple<int, int>(v, u));
                    }
#if DEBUG && !DEBUG_DETAIL
                    Console.Write(v.ToString() + " is already being explored");
#endif
                }
                black.Add(u);
            }

            return yieldReachingEdges;
        }
        /*
         * Calls CollectBackEdges for each Y edge existing in graph
         */
        private HashSet<Tuple<int, int>> CollectYieldReachingEdgesOfGraph(Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels)
        {
            HashSet<Tuple<int, int>> yieldTrueEdges = new HashSet<Tuple<int, int>>(); // Set {forall edges e : e is reaching a Y labeled edge}
            foreach (var e in graph.Edges) // Visits all edges to and do backward yield reachability analysis starting from source vertex of an "Y" labeled edge
            {
                if (edgeLabels[e] == "Y")
                {
                    HashSet<Tuple<int, int>> yieldReachingEdges = CollectBackwardEdgesOfYieldEdge(graph, e.Item1);
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
            HashSet<Tuple<int, int>> yieldTrueEdges = CollectYieldReachingEdgesOfGraph(graph, edgeLabels);

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
        private Automaton<BvSet> BuildAutomatonYieldTypeSafe(Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels, List<int> initialStates, List<int> finalStates, Implementation ytypeChecked, int yTypeCheckCurrentPhaseNum)
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

#if (DEBUG && !DEBUG_DETAIL)
            Console.Write(" \n Transitions before EPSILONS are added\n ");
            for (int i = 0; i < transitions.Count; i++)
            {
                int[] trans = transitions[i];
                Console.Write("\n From : " + trans[0].ToString() + "--- " + trans[1] + " --- " + " to : " + trans[3].ToString());
            }
#endif


#if DEBUG && !DEBUG_DETAIL
            Console.WriteLine(" ******* Printing initial states\n");
            foreach (int inits in initialStates) {

                Console.WriteLine("initial state is " + inits.ToString());
            }
#endif
            // get final states
            int[] finalSts = ComputeFinalStates(finalStates);
#if DEBUG && !DEBUG_DETAIL
            Console.WriteLine("\n*****Printing Finals states\n");
            foreach (int finals in finalSts)
            {
                Console.WriteLine(" final state " + finals.ToString());
            }
#endif
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

#if (DEBUG && !DEBUG_DETAIL)
            Console.Write(" \n Transitions are\n ");
            for (int i = 0; i < transitions.Count; i++)
            {
                int[] trans = transitions[i];
                Console.Write("\n From : " + trans[0].ToString() + "--- " + trans[1] + " --- " + " to : " + trans[3].ToString());
            }
#endif

            // create Automaton
            Automaton<BvSet> yieldTypeCheckAutomaton = solver.ReadFromRanges(dummyInitial, finalSts, transitions);
#if DEBUG && !DEBUG_DETAIL
            Console.WriteLine("\n--Implementation Automaton for type safe--");
            foreach (var move in yieldTypeCheckAutomaton.GetMoves())
            {
                Console.WriteLine("\n " + move.SourceState.ToString() + " -- " + this.PrintEpsilon(move.Condition, solver) + " --> " + move.TargetState.ToString() + " \n");
            }
            string implAutomatonGraphName = ytypeChecked.Proc.Name + "phaseNum__" + yTypeCheckCurrentPhaseNum.ToString();
            solver.ShowGraph(yieldTypeCheckAutomaton, implAutomatonGraphName + ".dmgl");
#endif


#if DEBUG && !DEBUG_DETAIL
           Console.WriteLine("\n--Epsilons Reduced Automaton--");
           foreach (var move in epsilonReducedAtutomaton.GetMoves()) {
                 Console.WriteLine("\n "+ move.SourceState.ToString() + " -- " +  solver.PrettyPrint(move.Condition)+ " --> " + move.TargetState.ToString() +" \n");
           }
#endif
            return yieldTypeCheckAutomaton;

        }

        private Automaton<BvSet> BuildAutomatonYieldReachSafe(Graph<int> graph, Dictionary<Tuple<int, int>, string> edgeLabels, List<int> initialStates, List<int> finalStates, Implementation ytypeChecked, int yTypeCheckCurrentPhaseNum)
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

#if (DEBUG && !DEBUG_DETAIL)
            Console.Write(" \n Transitions before EPSILONS are added\n ");
            for (int i = 0; i < transitions.Count; i++)
            {
                int[] trans = transitions[i];
                Console.Write("\n From : " + trans[0].ToString() + "--- " + trans[1] + " --- " + " to : " + trans[3].ToString());
            }
#endif


#if DEBUG && !DEBUG_DETAIL
            Console.WriteLine(" ******* Printing initial states\n");
            foreach (int inits in initialStates) {

                Console.WriteLine("initial state is " + inits.ToString());
            }
#endif
            // get final states
            int[] finalSts = ComputeFinalStates(finalStates);
#if DEBUG && !DEBUG_DETAIL
            Console.WriteLine("\n*****Printing Finals states\n");
            foreach (int finals in finalSts)
            {
                Console.WriteLine(" final state " + finals.ToString());
            }
#endif
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

#if (DEBUG && !DEBUG_DETAIL)
            Console.Write(" \n Transitions are\n ");
            for (int i = 0; i < transitions.Count; i++)
            {
                int[] trans = transitions[i];
                Console.Write("\n From : " + trans[0].ToString() + "--- " + trans[1] + " --- " + " to : " + trans[3].ToString());
            }
#endif

            // create Automaton
            Automaton<BvSet> yieldTypeCheckAutomaton = solver.ReadFromRanges(dummyInitial, finalSts, transitions);
#if DEBUG && !DEBUG_DETAIL
           Console.WriteLine("\n--Implementation Automaton--");
           foreach (var move in yieldTypeCheckAutomaton.GetMoves()) {
                 Console.WriteLine("\n "+ move.SourceState.ToString() + " -- " +  this.PrintEpsilon(move.Condition,solver)+ " --> " + move.TargetState.ToString() +" \n");
           }
           string implAutomatonGraphName = ytypeChecked.Proc.Name + "phaseNum__" + yTypeCheckCurrentPhaseNum.ToString();
           solver.ShowGraph(yieldTypeCheckAutomaton, implAutomatonGraphName+".dmgl");
#endif


#if DEBUG && !DEBUG_DETAIL
           Console.WriteLine("\n--Epsilons Reduced Automaton--");
           foreach (var move in epsilonReducedAtutomaton.GetMoves()) {
                 Console.WriteLine("\n "+ move.SourceState.ToString() + " -- " +  solver.PrettyPrint(move.Condition)+ " --> " + move.TargetState.ToString() +" \n");
           }
#endif
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