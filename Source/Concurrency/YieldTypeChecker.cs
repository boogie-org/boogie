#if QED
using System;
using System.Collections;
using System.Collections.Generic;

using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Automata;

namespace Microsoft.Boogie
{
    /*
     Summary:
     * 
     */
    class YieldTypeChecker
    {
        Program typeCheckedProg;
        private YieldTypeCheckerCore yTypeChecker;
        CharSetSolver yieldTypeCheckerAutomatonSolver;
        string yieldTypeCheckerRegex = @"^((1|2)+(3|4))*((D)+(((5|6))+((7|8))+((1|2))+((3|4)))*[A]((9)+(7)+(3))*)*$";
        Char[][] yieldTypeCheckerVocabulary;
        BvSet yielTypeCheckerBvSet;
        Automaton<BvSet> yieldTypeCheckerAutomaton;


        public YieldTypeChecker(Program program)
        {
            typeCheckedProg = program;
            yieldTypeCheckerAutomatonSolver = new CharSetSolver(BitWidth.BV7);
            yieldTypeCheckerVocabulary = new char[][] {
                new char[]{'1','2'},
                new char[]{'3','4'},
                new char[]{'5','6'},
                new char[]{'7','8'},
                new char[]{'9','A'},
                new char[]{'B','C'},
                new char[]{'D','F'}
            };
            yielTypeCheckerBvSet = yieldTypeCheckerAutomatonSolver.MkRangesConstraint(false, yieldTypeCheckerVocabulary);
            yieldTypeCheckerAutomaton = yieldTypeCheckerAutomatonSolver.Convert(yieldTypeCheckerRegex); //accepts strings that match the regex r
            this.Run(typeCheckedProg);
        }

        // Complete after discussing with Shaz!
        // Important function, may be one more function needed ?
        //This Function will process the implementation body's <Interval, list<string>> 
        //1. Map each character in the path string into a character in our Autamaton vocab.
        private Dictionary<Tuple<int, int>, string[]> ProcRawPath(Dictionary<Tuple<int, int>, string[]> rawPaths)
        {

            Dictionary<Tuple<int, int>, string[]> processedPaths = new Dictionary<Tuple<int, int>, string[]>();

            return processedPaths;
        }


        public bool Run(Program program)
        {

            foreach (Implementation impl in program.TopLevelDeclarations)
            {
                // Create YieldTypeChecker
                // Compute Utility Maps for an Implementation
                if (impl.Blocks.Count > 0)
                {
                    int phaseNumSpecImpl = QKeyValue.FindIntAttribute(impl.Proc.Attributes, "phase", 0);
                    yTypeChecker = new YieldTypeCheckerCore(impl, phaseNumSpecImpl);
                    Dictionary<Tuple<int, int>, string[]> inputToAutomata = ProcRawPath(yTypeChecker.PostProcessPaths());
                    foreach (KeyValuePair<Tuple<int, int>, string[]> pair in inputToAutomata)
                    {
                        foreach (string inputPath in pair.Value)
                        {
                            if (!(yieldTypeCheckerAutomatonSolver.Accepts(yieldTypeCheckerAutomaton, inputPath)))
                            {
                                return false;
                            }
                        }
                    }


                }
            }
            return true;
        }
    }

    /*    Dictionary<Implementation, Dictionary<Procedure, int>> phaseNumToCall; */
    // I think I dont need this
    //  phaseNumToCall[Impl] ==> Dictionary dict={ 
    //foreach(CallCmd in callCmdsInImpl[Impl]
    //          ->foreach KeyValPair p in  dict
    //            ->   get p.Second gives phase num in

    class YieldTypeCheckerCore
    {

        CheckingContext checkingContext;
        int errorCount;


        Implementation ytypeChecked; // YieldTypeChecked body
        int numCallInEncImpl;
        int specPhaseNumImpl;
        int yTypeCheckCurrentPhaseNum;

        Dictionary<Implementation, HashSet<CallCmd>> callCmdsInImpl; //  callCmdsInImpl[Implementation] ==> Set = { call1, call2, call3 ... }
        Dictionary<Implementation, int> numCallCmdInEnclosingProc; // Number of CallCmds in       
        Dictionary<Implementation, Dictionary<Tuple<int, int>, string>> yieldTypeCheckPattern; // (-inf ph0 ] (ph0 ph1] (ph1 ph2] ..... (phk phk+1] where phk+1 == atcSpecPhsNumTypeCheckedProc
        Dictionary<Implementation, List<Tuple<int, int>>> phaseIntervals; // (-inf ph0 ] (ph0 ph1] (ph1 ph2] ..... (phk phk+1] intervals

        public YieldTypeCheckerCore(Implementation toTypeCheck, int specPhaseNum)
        {
            ytypeChecked = toTypeCheck;
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            numCallInEncImpl = 0;
            specPhaseNumImpl = specPhaseNum;
            yTypeCheckCurrentPhaseNum = 0;

            /*Utility Maps*/
            phaseIntervals = new Dictionary<Implementation, List<Tuple<int, int>>>();
            yieldTypeCheckPattern = new Dictionary<Implementation, Dictionary<Tuple<int, int>, string>>();
            callCmdsInImpl = new Dictionary<Implementation, HashSet<CallCmd>>();
            numCallCmdInEnclosingProc = new Dictionary<Implementation, int>();

        }

        public Dictionary<Tuple<int, int>, string[]> CreateRawInputToTypeCheck()
        {
            List<Tuple<int, int>> iterOverPhaseList = phaseIntervals[ytypeChecked];
            this.CalculateCallCmds(ytypeChecked);
            this.VisitImplementation(ytypeChecked);

            for (int i = 0;

                yTypeCheckCurrentPhaseNum <= specPhaseNumImpl
                && i < iterOverPhaseList.Count;

                i++)
            {
                VisitImplementation(ytypeChecked);
                yTypeCheckCurrentPhaseNum = yTypeCheckCurrentPhaseNum + iterOverPhaseList[i].Item2 + 1;
            }

            return PostProcessPaths();




        }

        private void CalculateCallCmds(Implementation impl)
        {
            HashSet<CallCmd> callCmdInBodyEncImpl = new HashSet<CallCmd>();
            List<CallCmd> callCmdInBodyEncImplList = new List<CallCmd>();

            foreach (Block b in impl.Blocks)
            {
                List<Cmd> cmds = new List<Cmd>();
                for (int i = 0; i < b.Cmds.Count; i++)
                {
                    Cmd cmd = b.Cmds[i];
                    if (cmd is CallCmd)
                    {
                        CallCmd callCmd = b.Cmds[i] as CallCmd;
                        numCallInEncImpl = numCallInEncImpl + 1;
                        numCallCmdInEnclosingProc.Add(impl, numCallInEncImpl);


                        if (!(callCmdInBodyEncImpl.Contains(callCmd)))
                        {
                            callCmdInBodyEncImpl.Add(callCmd);
                            callCmdInBodyEncImplList.Add(callCmd);// 

                        }

                    }
                }

            }

            //Sort all PhaseNum of callCmds inside Implementation 
            List<int> callCmdPhaseNumIndexList = new List<int>();
            for (int i = 0; i < callCmdInBodyEncImplList.Count; i++)
            {
                int tmpPhaseNum = QKeyValue.FindIntAttribute(callCmdInBodyEncImplList[i].Proc.Attributes, "phase", 0);
                callCmdPhaseNumIndexList.Add(tmpPhaseNum);
            }

            callCmdPhaseNumIndexList.Sort();

            List<Tuple<int, int>> phsIntrvs = new List<Tuple<int, int>>();
            //Create Phase Intervals
            for (int i = 0; i < callCmdPhaseNumIndexList.Count; i++)
            {
                //set the initial 
                if (i == 0)
                {
                    Tuple<int, int> initTuple = new Tuple<int, int>(int.MinValue, callCmdPhaseNumIndexList[i]);
                    phsIntrvs.Add(initTuple);
                }
                else
                {
                    Tuple<int, int> intervalToInsert = new Tuple<int, int>(callCmdPhaseNumIndexList[i - 1] + 1, callCmdPhaseNumIndexList[i]);
                    phsIntrvs.Add(intervalToInsert);
                }
            }

            //Set Implementation -> List<Tuple> map
            phaseIntervals.Add(ytypeChecked, phsIntrvs);
            //Set Implelentation -> CallCmds
            callCmdsInImpl.Add(ytypeChecked, callCmdInBodyEncImpl);
            //Set Implementation -> numberofCalls
            numCallCmdInEnclosingProc.Add(ytypeChecked, numCallInEncImpl);

        }
        public void ComputePaths(Block b)
        {

            foreach (Cmd cmd in b.Cmds)
            {
                if (cmd is AssignCmd)
                {
                    AssignCmd assnCmd = cmd as AssignCmd;
                    AddCheckAssignCmd(assnCmd);
                }
                else if (cmd is CallCmd)
                {
                    CallCmd callCmd = cmd as CallCmd;
                    AddCheckCallCmd(callCmd, yTypeCheckCurrentPhaseNum);
                }
                else if (cmd is AssumeCmd)
                {
                    AssumeCmd assmCmd = cmd as AssumeCmd;
                    AddCheckAssumeCmd(assmCmd);
                }
                else if (cmd is HavocCmd)
                {
                    HavocCmd havocCmd = cmd as HavocCmd;
                    AddCheckHavocCmd(havocCmd);
                }
                else if (cmd is YieldCmd)
                {
                    YieldCmd yldCmd = cmd as YieldCmd;
                    AddCheckYieldCmd(yldCmd);
                }
                else if (cmd is AssertCmd)
                {
                    AssertCmd assertCmd = cmd as AssertCmd;
                    AddCheckAssertCmd(assertCmd);
                }
            }
        }

        /*
         (-inf 4] -> "PQBAL" "..." 
         [3 7] -> "PQB" , "PQYA " ...
         ..
         ..
         (k  specReachPoint] -> ....
         */
        public Dictionary<Tuple<int, int>, string[]> PostProcessPaths()
        {
            Dictionary<Tuple<int, int>, string[]> pathsPerPhase = new Dictionary<Tuple<int, int>, string[]>();
            Dictionary<Tuple<int, int>, string> pathPerPhase = yieldTypeCheckPattern[ytypeChecked];
            List<Tuple<int, int>> iterOverPhaseList = phaseIntervals[ytypeChecked];

            for (int i = 0; i < iterOverPhaseList.Count; i++)
            {
                string[] pathsPerPhs = pathPerPhase[iterOverPhaseList[i]].Split('S');
                pathsPerPhase.Add(iterOverPhaseList[i], pathsPerPhs);
            }
            //Discuss with Shaz in detail !
            return pathsPerPhase;
        }

        public void AddCheckCallCmd(CallCmd cmd, int currentCheckPhsNum)
        {
            List<Tuple<int, int>> iterOverPhaseList = phaseIntervals[ytypeChecked];
            for (int i = 0; i < iterOverPhaseList.Count; i++)
            {

                if (currentCheckPhsNum <= iterOverPhaseList[i].Item2)
                {
                    yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] = yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] + "S";
                }
                else
                {
                    foreach (Ensures e in ytypeChecked.Proc.Ensures)
                    {
                        if (QKeyValue.FindBoolAttribute(e.Attributes, "atomic"))
                        {
                            yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] = yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] + "A";

                        }
                        else if (QKeyValue.FindBoolAttribute(e.Attributes, "right"))
                        {
                            yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] = yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] + "R";
                        }
                        else if (QKeyValue.FindBoolAttribute(e.Attributes, "left"))
                        {
                            yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] = yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] + "L";
                        }
                        else if (QKeyValue.FindBoolAttribute(e.Attributes, "both"))
                        {
                            yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] = yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] + "B";
                        }

                    }

                }
            }
        }

        public void AddCheckYieldCmd(YieldCmd cmd)
        {
            List<Tuple<int, int>> iterOverPhaseList = phaseIntervals[ytypeChecked];
            for (int i = 0; i < iterOverPhaseList.Count; i++)
            {
                yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] =
                     yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] + "Y";
            }
        }
        //Assuming that "AssumeCmd can not include Global variable" check done in previous typechecks 
        public void AddCheckAssumeCmd(AssumeCmd cmd)
        {

            List<Tuple<int, int>> iterOverPhaseList = phaseIntervals[ytypeChecked];
            for (int i = 0; i < iterOverPhaseList.Count; i++)
            {
                yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] =
                     yieldTypeCheckPattern[ytypeChecked][iterOverPhaseList[i]] + "Y";
            }
        }

        // Go through with Shaz
        //public void AddCheckNaryExpr() { }

        // Go through with Shaz
        public void AddCheckAssignCmd(AssignCmd cmd) { }

        //Go through with Shaz
        public void AddCheckHavocCmd(HavocCmd cmd) { }

        // Go through with Shaz
        public void AddCheckAssertCmd(AssertCmd cmd) { }


        public void VisitImplementation(Implementation node)
        {
            if (node != ytypeChecked)
            {

                Error(node, "The visited implementation must be" + ytypeChecked.Name);
            }

            specPhaseNumImpl = QKeyValue.FindIntAttribute(node.Proc.Attributes, "phase", 0);

            //
            Stack<Block> dfsStack = new Stack<Block>();
            HashSet<Block> dfsStackAsSet = new HashSet<Block>();
            dfsStack.Push(node.Blocks[0]);
            dfsStackAsSet.Add(node.Blocks[0]);
            while (dfsStack.Count > 0)
            {
                Block b = dfsStack.Pop();
                dfsStackAsSet.Remove(b);
                ComputePaths(b);

                if (b.TransferCmd is ReturnCmd)
                {
                    continue;
                }
                GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    dfsStack.Push(target);
                    dfsStackAsSet.Add(target);
                }
            }
        }


        private void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
            errorCount++;
        }


    }
}
#endif