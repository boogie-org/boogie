using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.IO;
using Microsoft.Boogie;
using Graphing;
using AI = Microsoft.AbstractInterpretationFramework;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{
    using Bpl = Microsoft.Boogie;

    public class StratifiedVCGen : VCGen
    {
        private Dictionary<string, StratifiedInliningInfo> implName2StratifiedInliningInfo;
        public bool PersistCallTree;
        public static Dictionary<string, int> callTree = null;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
        }

        /// <summary>
        /// Constructor.  Initializes the theorem prover.
        /// </summary>
        [NotDelayed]
        public StratifiedVCGen(Program program, string/*?*/ logFilePath, bool appendLogFile)
            : base(program, logFilePath, appendLogFile)
        {
            Contract.Requires(program != null);
            implName2StratifiedInliningInfo = new Dictionary<string, StratifiedInliningInfo>();
            this.GenerateVCsForStratifiedInlining(program);
            PersistCallTree = false;
        }

        public class StratifiedInliningInfo : LazyInliningInfo
        {
            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(cce.NonNullElements(privateVars));
                Contract.Invariant(cce.NonNullElements(interfaceExprVars));
                Contract.Invariant(cce.NonNullElements(interfaceExprVars));
            }

            public bool initialized;
            public int inline_cnt;
            public List<VCExprVar> privateVars;
            public List<VCExprVar> interfaceExprVars;
            public VCExpr funcExpr;
            public VCExpr falseExpr;

            public StratifiedInliningInfo(Implementation impl, Program program, ProverContext ctxt, int uniqueid)
                : base(impl, program, ctxt, uniqueid)
            {
                Contract.Requires(impl != null);
                Contract.Requires(program != null);
                inline_cnt = 0;
                privateVars = new List<VCExprVar>();
                interfaceExprVars = new List<VCExprVar>();
                initialized = false;
            }

        }

        public void GenerateVCsForStratifiedInlining(Program program)
        {
            Contract.Requires(program != null);
            Checker checker = FindCheckerFor(null, CommandLineOptions.Clo.ProverKillTime);
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Contract.Assert(decl != null);
                Implementation impl = decl as Implementation;
                if (impl == null)
                    continue;
                Procedure proc = cce.NonNull(impl.Proc);
                if (proc.FindExprAttribute("inline") != null)
                {
                    StratifiedInliningInfo info = new StratifiedInliningInfo(impl, program, checker.TheoremProver.Context, QuantifierExpr.GetNextSkolemId());
                    implName2StratifiedInliningInfo[impl.Name] = info;
                    // We don't need controlFlowVariable for stratified Inlining
                    //impl.LocVars.Add(info.controlFlowVariable);
                    ExprSeq exprs = new ExprSeq();
                    foreach (Variable v in program.GlobalVariables())
                    {
                        Contract.Assert(v != null);
                        exprs.Add(new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                    }
                    foreach (Variable v in proc.InParams)
                    {
                        Contract.Assert(v != null);
                        exprs.Add(new IdentifierExpr(Token.NoToken, v));
                    }
                    foreach (Variable v in proc.OutParams)
                    {
                        Contract.Assert(v != null);
                        exprs.Add(new IdentifierExpr(Token.NoToken, v));
                    }
                    foreach (IdentifierExpr ie in proc.Modifies)
                    {
                        Contract.Assert(ie != null);
                        if (ie.Decl == null)
                            continue;
                        exprs.Add(ie);
                    }
                    Expr freePostExpr = new NAryExpr(Token.NoToken, new FunctionCall(info.function), exprs);
                    proc.Ensures.Add(new Ensures(Token.NoToken, true, freePostExpr, "", new QKeyValue(Token.NoToken, "si_fcall", new List<object>(), null)));
                }
            }

        }

        private void GenerateVCForStratifiedInlining(Program program, StratifiedInliningInfo info, Checker checker)
        {
            Contract.Requires(program != null);
            Contract.Requires(info != null);
            Contract.Requires(checker != null);
            Contract.Requires(info.impl != null);
            Contract.Requires(info.impl.Proc != null);
            Contract.Requires(!info.initialized);
            Contract.Ensures(info.initialized);

            Implementation impl = info.impl;
            Contract.Assert(impl != null);
            ConvertCFG2DAG(impl, program);
            ModelViewInfo mvInfo;
            info.gotoCmdOrigins = PassifyImpl(impl, program, out mvInfo);
            Contract.Assert(info.exitIncarnationMap != null);
            Hashtable/*<int, Absy!>*/ label2absy;
            VCExpressionGenerator gen = checker.VCExprGen;
            Contract.Assert(gen != null);
            VCExpr vcexpr = gen.Not(GenerateVC(impl, null, out label2absy, checker));
            Contract.Assert(vcexpr != null);
            info.label2absy = label2absy;

            Boogie2VCExprTranslator translator = checker.TheoremProver.Context.BoogieExprTranslator;
            Contract.Assert(translator != null);
            info.privateVars = new List<VCExprVar>();
            foreach (Variable v in impl.LocVars)
            {
                Contract.Assert(v != null);
                info.privateVars.Add(translator.LookupVariable(v));
            }
            foreach (Variable v in impl.OutParams)
            {
                Contract.Assert(v != null);
                info.privateVars.Add(translator.LookupVariable(v));
            }

            info.interfaceExprVars = new List<VCExprVar>();
            List<VCExpr> interfaceExprs = new List<VCExpr>();
            foreach (Variable v in info.interfaceVars)
            {
                Contract.Assert(v != null);
                VCExprVar ev = translator.LookupVariable(v);
                Contract.Assert(ev != null);
                info.interfaceExprVars.Add(ev);
                interfaceExprs.Add(ev);
            }

            Function function = cce.NonNull(info.function);
            Contract.Assert(function != null);
            info.funcExpr = gen.Function(function, interfaceExprs);
            info.vcexpr = vcexpr;

            info.initialized = true;
        }

        public class CoverageGraphManager
        {
            public static int timeStamp = 0;


            public class Task
            {
                public enum TaskType { NONE, STEP, INLINE, BLOCK, REACHABLE };

                public TaskType type;
                private string query_string;
                public List<int> nodes;
                public int queryNode
                {
                    get
                    {
                        Debug.Assert(nodes.Count == 1);
                        return nodes[0];
                    }
                }

                public Task(string q, FCallHandler calls)
                {
                    query_string = q;
                    nodes = new List<int>();
                    if (q.StartsWith("step"))
                    {
                        type = TaskType.STEP;
                        return;
                    }
                    var split = q.Split(' ');
                    switch (split[0].ToLower())
                    {
                        case "inline":
                            type = TaskType.INLINE;
                            break;
                        case "block":
                            type = TaskType.BLOCK;
                            break;
                        case "reachable":
                            type = TaskType.REACHABLE;
                            break;
                        default:
                            Debug.Assert(false);
                            break;
                    }
                    for (int i = 1; i < split.Length; i++)
                    {
                        var node = calls.getCandidateFromGraphNode(split[i]);
                        if (node != -1)
                        {
                            nodes.Add(node);
                        }

                    }
                    // Prune nodes according to which are current candidates
                    var pruned = new List<int>();
                    foreach (var n in nodes)
                    {
                        if (calls.currCandidates.Contains(n))
                        {
                            if (type == TaskType.INLINE || type == TaskType.BLOCK)
                            {
                                pruned.Add(n);
                            }
                        }
                        else
                        {
                            if (type == TaskType.REACHABLE)
                            {
                                pruned.Add(n);
                            }
                        }
                    }

                    nodes = pruned;
                    if (type == TaskType.REACHABLE && nodes.Count != 1)
                    {
                        type = TaskType.NONE;
                    }
                    else if (nodes.Count == 0)
                    {
                        type = TaskType.NONE;
                    }
                }

                public bool isStep()
                {
                    return (type == TaskType.STEP);
                }

                public override string ToString()
                {
                    return query_string;
                }
            }

            public string getQuery(int ts)
            {
                var ret = "";
                while (true)
                {
                    string str = coverageProcess.StandardOutput.ReadLine();
                    if (str.StartsWith("query "))
                    {
                        var split = str.Split(' ');
                        if (split.Length < 1) continue;
                        if (ts.ToString() == split[1])
                        {
                            for (int i = 2; i < split.Length; i++) ret = ret + split[i] + " ";
                            break;
                        }
                    }
                }
                return ret;
            }

            public static Process coverageProcess;
            public bool stopCoverageProcess;
            //private System.Threading.Thread readerThread;
            private FCallHandler calls;
            // Set of edges to send off to the coverageProcess
            private List<KeyValuePair<int, int>> edges;
            // Set of nodes to send off to the coverageProcess
            private HashSet<int> newNodes;
            // Set of nodes already declared
            private HashSet<int> declaredNodes;

            public CoverageGraphManager(FCallHandler calls)
            {
                stopCoverageProcess = true;
                coverageProcess = null;
                this.calls = calls;
                this.edges = new List<KeyValuePair<int, int>>();
                declaredNodes = new HashSet<int>();
                newNodes = new HashSet<int>();

                coverageProcess = CommandLineOptions.Clo.coverageReporter;
                if (coverageProcess != null)
                {
                    stopCoverageProcess = false;
                    if (!coverageProcess.StartInfo.RedirectStandardInput)
                    {
                        coverageProcess = null;
                    }
                }
                else
                {
                    if (CommandLineOptions.Clo.CoverageReporterPath != null)
                    {
                        coverageProcess = new Process();
                        var coverageProcessInfo = new ProcessStartInfo();
                        coverageProcessInfo.CreateNoWindow = true;
                        coverageProcessInfo.FileName = CommandLineOptions.Clo.CoverageReporterPath + @"\CoverageGraph.exe";
                        coverageProcessInfo.RedirectStandardInput = true;
                        coverageProcessInfo.RedirectStandardOutput = true;
                        coverageProcessInfo.RedirectStandardError = false;
                        coverageProcessInfo.UseShellExecute = false;
                        coverageProcessInfo.Arguments = "interactive";

                        coverageProcess.StartInfo = coverageProcessInfo;
                        try
                        {
                            coverageProcess.Start();
                        }
                        catch (System.ComponentModel.Win32Exception)
                        {
                            coverageProcess.Dispose();
                            coverageProcess = null;
                        }
                        //readerThread = new System.Threading.Thread(new System.Threading.ThreadStart(CoverageGraphInterface));
                        //readerThread.Start();
                    }
                }

                if (coverageProcess != null)
                {
                    coverageProcess.StandardInput.WriteLine("clear-all");
                }
            }

            public void addMain()
            {
                if (coverageProcess == null) return;
                newNodes.Add(0);
                foreach (var n in calls.currCandidates)
                {
                    addEdge(0, n);
                }
                calls.recentlyAddedCandidates = new HashSet<int>();
            }

            public void addNode(int src)
            {
                newNodes.Add(src);
            }

            public void addEdge(int src_id, int tgt_id)
            {
                newNodes.Add(src_id);
                newNodes.Add(tgt_id);
                edges.Add(new KeyValuePair<int, int>(src_id, tgt_id));
            }

            public void addRecentEdges(int src_id)
            {
                newNodes.Add(src_id);
                foreach (var tgt in calls.recentlyAddedCandidates)
                {
                    addEdge(src_id, tgt);
                }
                calls.recentlyAddedCandidates = new HashSet<int>();
            }

            private void declareNodes()
            {
                var send = false;
                var declarenode = "declare-node";
                foreach (var n in newNodes)
                {
                    if (declaredNodes.Contains(n)) continue;
                    declaredNodes.Add(n);
                    send = true;
                    declarenode += string.Format(" {0} {1}", calls.getPersistentId(n), calls.getProc(n));
                }
                if(send)
                  coverageProcess.StandardInput.WriteLine(declarenode);
            }

            private void declareEdges()
            {
                if (edges.Count == 0) return;

                var declareedge = "declare-edge";
                foreach (var e in edges)
                {
                    declareedge += string.Format(" {0} {1}", calls.getPersistentId(e.Key), calls.getPersistentId(e.Value));
                }
                coverageProcess.StandardInput.WriteLine(declareedge);
            }

            public void syncGraph()
            {
                if (coverageProcess == null || newNodes.Count == 0)
                {
                    edges.Clear();
                    return;
                }

                coverageProcess.StandardInput.WriteLine("batch-graph-command-begin");
                coverageProcess.StandardInput.WriteLine("reset-color");

                // Go through the edges
                var greenNodes = new HashSet<int>();
                var redNodes = new HashSet<int>();
                foreach (var node in calls.currCandidates)
                {
                    if (calls.getRecursionBound(node) > CommandLineOptions.Clo.RecursionBound)
                    {
                        redNodes.Add(node);
                    }
                    else
                    {
                        greenNodes.Add(node);
                    }

                }
                // Send data across
                declareNodes();
                declareEdges();

                if (greenNodes.Count != 0)
                {
                    var color = "color green";
                    foreach (var n in greenNodes)
                    {
                        color += string.Format(" {0}", calls.getPersistentId(n));
                    }
                    coverageProcess.StandardInput.WriteLine(color);
                }

                if (redNodes.Count != 0)
                {
                    var color = "color red";
                    foreach (var n in redNodes)
                    {
                        color += string.Format(" {0}", calls.getPersistentId(n));
                    }
                    coverageProcess.StandardInput.WriteLine(color);
                }

                coverageProcess.StandardInput.WriteLine("batch-graph-command-end");

                edges.Clear();
                newNodes = new HashSet<int>();
            }

            public void reportBug()
            {
                if (coverageProcess == null) return;
                coverageProcess.StandardInput.WriteLine("set-status bug");
            }

            public void reportCorrect()
            {
                if (coverageProcess == null) return;
                coverageProcess.StandardInput.WriteLine("set-status correct");
            }

            public void reportCorrect(int bound)
            {
                if (coverageProcess == null) return;
                coverageProcess.StandardInput.WriteLine("set-status bound {0}", bound);
            }

            public void reportError()
            {
                if (coverageProcess == null) return;
                coverageProcess.StandardInput.WriteLine("set-status error");
            }

            public Task getNextTask()
            {
                if (coverageProcess == null) return new Task("step", calls);
                if (coverageProcess.HasExited)
                {
                    coverageProcess = null;
                    return new Task("step", calls);
                }

                var ts = getNextTimeStamp();
                coverageProcess.StandardInput.WriteLine("get-input " + ts.ToString());
                string q = getQuery(ts);
                return new Task(q, calls);
            }

            public void stop()
            {
                if (coverageProcess != null)
                {
                    if (stopCoverageProcess)
                    {
                        coverageProcess.StandardInput.WriteLine("done");
                        do
                        {
                            coverageProcess.WaitForExit(100);
                            coverageProcess.StandardInput.WriteLine();
                        } while (!coverageProcess.HasExited);
                    }
                }
            }

            public int getNextTimeStamp()
            {
                timeStamp++;
                return timeStamp - 1;
            }

        }

        // Unifies the interface between standard checker and z3api-based checker
        abstract public class StratifiedCheckerInterface
        {
            // Underlying checker
            public Checker underlyingChecker;
            // Statistics
            public int numQueries;

            abstract public Outcome CheckVC();
            abstract public void Push();
            abstract public void Pop();
            abstract public void AddAxiom(VCExpr vc);
            abstract public void LogComment(string str);
            virtual public Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore)
            {
                Outcome ret;

                unsatCore = new List<int>();
                for (int i = 0; i < assumptions.Count; i++)
                    unsatCore.Add(i);

                if (assumptions.Count == 0)
                {
                    return CheckVC();
                }

                Push();

                foreach (var a in assumptions)
                {
                    AddAxiom(a);
                }
                ret = CheckVC();

                Pop();

                return ret;
            }
        }

        public class NormalChecker : StratifiedCheckerInterface
        {
            // The VC of main
            public VCExpr vcMain;
            // Error reporter (stores models)
            public ProverInterface.ErrorHandler reporter;
            // The theorem prover interface
            public Checker checker;
            // stores the number of axioms pushed since pervious backtracking point
            private List<int> numAxiomsPushed;

            public NormalChecker(VCExpr vcMain, ProverInterface.ErrorHandler reporter, Checker checker)
            {
                this.vcMain = vcMain;
                this.reporter = reporter;
                this.checker = checker;
                this.underlyingChecker = checker;
                numAxiomsPushed = new List<int>();
                numQueries = 0;
            }

            public override Outcome CheckVC()
            {
                Contract.Requires(vcMain != null);
                Contract.Requires(reporter != null);
                Contract.Requires(checker != null);
                Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

                checker.TheoremProver.FlushAxiomsToTheoremProver();
                checker.BeginCheck("the_main", vcMain, reporter);
                checker.ProverDone.WaitOne();

                ProverInterface.Outcome outcome = (checker).ReadOutcome();
                numQueries++;

                switch (outcome)
                {
                    case ProverInterface.Outcome.Valid:
                        return Outcome.Correct;
                    case ProverInterface.Outcome.Invalid:
                        return Outcome.Errors;
                    case ProverInterface.Outcome.OutOfMemory:
                        return Outcome.OutOfMemory;
                    case ProverInterface.Outcome.TimeOut:
                        return Outcome.TimedOut;
                    case ProverInterface.Outcome.Undetermined:
                        return Outcome.Inconclusive;
                    default:
                        Contract.Assert(false);
                        throw new cce.UnreachableException();
                }

            }

            public override void Push()
            {
                numAxiomsPushed.Add(0);
            }

            public override void Pop()
            {
                Debug.Assert(numAxiomsPushed.Count > 0);
                checker.TheoremProver.FlushAxiomsToTheoremProver();
                var n = numAxiomsPushed.Last();
                numAxiomsPushed.RemoveAt(numAxiomsPushed.Count - 1);

                for (int i = 0; i < n; i++)
                {
                    checker.TheoremProver.Pop();
                }
            }

            public override void AddAxiom(VCExpr vc)
            {
                Debug.Assert(numAxiomsPushed.Count > 0);
                int oldnum = checker.TheoremProver.NumAxiomsPushed();
                
                checker.TheoremProver.PushVCExpression(vc);

                int newnum = checker.TheoremProver.NumAxiomsPushed();
                numAxiomsPushed[numAxiomsPushed.Count - 1] += (newnum - oldnum);
            }

            public override void LogComment(string str)
            {
                checker.TheoremProver.LogComment(str);
            }

        }


        public class ApiChecker : StratifiedCheckerInterface
        {
            // The VC of main
            private VCExpr vcMain;
            // Error reporter (stores models)
            private ProverInterface.ErrorHandler reporter;
            // The theorem prover interface
            public Checker checker;
            // stores the number of axioms pushed since pervious backtracking point
            private List<int> numAxiomsPushed;
            // Api-based theorem prover
            private ApiProverInterface TheoremProver;
            // Use checkAssumptions?
            public static bool UseCheckAssumptions = true;

            public ApiChecker(VCExpr vcMain, ProverInterface.ErrorHandler reporter, Checker checker)
            {
                this.vcMain = vcMain;
                this.reporter = reporter;
                this.checker = checker; 
                this.underlyingChecker = checker;
                numAxiomsPushed = new List<int>();
                numQueries = 0;
                TheoremProver = checker.TheoremProver as ApiProverInterface;
                Debug.Assert(TheoremProver != null);

                // Add main to the TP stack
                TheoremProver.Assert(vcMain, false);
            }

            public override Outcome CheckVC()
            {
                Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

                TheoremProver.AssertAxioms();
                TheoremProver.Check();
                ProverInterface.Outcome outcome = TheoremProver.CheckOutcome(reporter);
                numQueries++;

                switch (outcome)
                {
                    case ProverInterface.Outcome.Valid:
                        return Outcome.Correct;
                    case ProverInterface.Outcome.Invalid:
                        return Outcome.Errors;
                    case ProverInterface.Outcome.OutOfMemory:
                        return Outcome.OutOfMemory;
                    case ProverInterface.Outcome.TimeOut:
                        return Outcome.TimedOut;
                    case ProverInterface.Outcome.Undetermined:
                        return Outcome.Inconclusive;
                    default:
                        Contract.Assert(false);
                        throw new cce.UnreachableException();
                }

            }

            public override void Push()
            {
                TheoremProver.Push();
            }

            public override void Pop()
            {
                TheoremProver.AssertAxioms();
                TheoremProver.Pop();
            }

            public override void AddAxiom(VCExpr vc)
            {
                TheoremProver.Assert(vc, true);
            }

            public override void LogComment(string str)
            {
                checker.TheoremProver.LogComment(str);
            }
            
            public override Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore)
            {
                if (!UseCheckAssumptions)
                {
                    return base.CheckAssumptions(assumptions, out unsatCore);
                }

                if (assumptions.Count == 0)
                {
                    unsatCore = new List<int>();
                    return CheckVC();
                }

                //TheoremProver.Push();
                TheoremProver.AssertAxioms();
                TheoremProver.CheckAssumptions(assumptions, out unsatCore);
                ProverInterface.Outcome outcome = TheoremProver.CheckOutcome(reporter);
                //TheoremProver.Pop();
                numQueries++;

                switch (outcome)
                {
                    case ProverInterface.Outcome.Valid:
                        return Outcome.Correct;
                    case ProverInterface.Outcome.Invalid:
                        return Outcome.Errors;
                    case ProverInterface.Outcome.OutOfMemory:
                        return Outcome.OutOfMemory;
                    case ProverInterface.Outcome.TimeOut:
                        return Outcome.TimedOut;
                    case ProverInterface.Outcome.Undetermined:
                        return Outcome.Inconclusive;
                    default:
                        Contract.Assert(false);
                        throw new cce.UnreachableException();
                }
            }
             
        }

        // Store important information related to a single VerifyImplementation query
        public class VerificationState
        {
            // The VC of main
            public VCExpr vcMain;
            // The call tree
            public FCallHandler calls;
            // Error reporter (stores models)
            public StratifiedInliningErrorReporter reporter;
            // The theorem prover interface
            //public Checker checker;
            public StratifiedCheckerInterface checker;
            // The coverage graph reporter
            public CoverageGraphManager coverageManager;
            // For statistics
            public int vcSize;
            public int expansionCount;
            public int numQueries
            {
                get
                {
                    return checker.numQueries;
                }
            }

            public VerificationState(VCExpr vcMain, FCallHandler calls,
                StratifiedInliningErrorReporter reporter, Checker checker)
            {
                this.vcMain = vcMain;
                this.calls = calls;
                this.reporter = reporter;
                if (checker.TheoremProver is ApiProverInterface)
                {
                    this.checker = new ApiChecker(vcMain, reporter , checker);
                }
                else
                {
                    this.checker = new NormalChecker(vcMain, reporter, checker);
                }
                vcSize = 0;
                expansionCount = 0;
            }
        }

        public Outcome FindLeastToVerify(Implementation impl, Program program, ref HashSet<string> allBoolVars)
        {
            Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

            // Record current time
            var startTime = DateTime.Now;

            // Get the checker
            Checker checker = FindCheckerFor(impl, CommandLineOptions.Clo.ProverKillTime); Contract.Assert(checker != null);

            Contract.Assert(implName2StratifiedInliningInfo != null);
            this.program = program;

            // Get the VC of the current procedure
            VCExpr vcMain;
            Hashtable/*<int, Absy!>*/ mainLabel2absy;
            ModelViewInfo mvInfo;

            ConvertCFG2DAG(impl, program);
            Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = PassifyImpl(impl, program, out mvInfo);
            vcMain = GenerateVC(impl, null, out mainLabel2absy, checker);

            StratifiedCheckerInterface apiChecker = null;

            if (checker.TheoremProver is ApiProverInterface)
            {
                apiChecker = new ApiChecker(vcMain, new EmptyErrorHandler(), checker);
            }
            else
            {
                apiChecker = new NormalChecker(vcMain, new EmptyErrorHandler(), checker);
            }

            // Find all the boolean constants
            var allConsts = new HashSet<VCExprVar>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                var constant = decl as Constant;
                if (constant == null) continue;
                if (!allBoolVars.Contains(constant.Name)) continue;
                allConsts.Add(checker.TheoremProver.Context.BoogieExprTranslator.LookupVariable(constant));
            }

            // Now, lets start the algo
            var min = refinementLoop(apiChecker, new HashSet<VCExprVar>(), allConsts, allConsts);

            var ret = new HashSet<string>();
            foreach (var v in min)
            {
                //Console.WriteLine(v.Name);
                ret.Add(v.Name);
            }
            allBoolVars = ret;
            return Outcome.Correct;
        }

        private HashSet<VCExprVar> refinementLoop(StratifiedCheckerInterface apiChecker, HashSet<VCExprVar> trackedVars, HashSet<VCExprVar> trackedVarsUpperBound, HashSet<VCExprVar> allVars)
        {
            Debug.Assert(trackedVars.IsSubsetOf(trackedVarsUpperBound));

            // If we already know the fate of all vars, then we're done.
            if (trackedVars.Count == trackedVarsUpperBound.Count)
                return new HashSet<VCExprVar>(trackedVars);

            // See if we already have enough variables tracked
            var success = refinementLoopCheckPath(apiChecker, trackedVars, allVars);
            if (success)
            {
                // We have enough
                return new HashSet<VCExprVar>(trackedVars);
            }

            // If all that remains is 1 variable, then we know that we must track it
            if (trackedVars.Count + 1 == trackedVarsUpperBound.Count)
                return new HashSet<VCExprVar>(trackedVarsUpperBound);

            // Partition the remaining set of variables
            HashSet<VCExprVar> part1, part2;
            var temp = new HashSet<VCExprVar>(trackedVarsUpperBound);
            temp.ExceptWith(trackedVars);
            Partition<VCExprVar>(temp, out part1, out part2);
            
            // First half
            var fh = new HashSet<VCExprVar>(trackedVars); fh.UnionWith(part2);
            var s1 = refinementLoop(apiChecker, fh, trackedVarsUpperBound, allVars);

            var a = new HashSet<VCExprVar>(part1); a.IntersectWith(s1);
            var b = new HashSet<VCExprVar>(part1); b.ExceptWith(s1);
            var c = new HashSet<VCExprVar>(trackedVarsUpperBound); c.ExceptWith(b);
            a.UnionWith(trackedVars);

            // Second half
            return refinementLoop(apiChecker, a, c, allVars);
        }

        private bool refinementLoopCheckPath(StratifiedCheckerInterface apiChecker, HashSet<VCExprVar> varsToSet, HashSet<VCExprVar> allVars)
        {
            var assumptions = new List<VCExpr>();
            List<int> temp = null;

            //Console.Write("Query: ");
            foreach (var c in allVars)
            {
                if (varsToSet.Contains(c))
                {
                    //Console.Write(c.Name + " ");
                    assumptions.Add(c); //apiChecker.underlyingChecker.VCExprGen.Eq(c, VCExpressionGenerator.True));
                }
                else
                {
                    assumptions.Add(apiChecker.underlyingChecker.VCExprGen.Not(c));
                }
            }
            //Console.WriteLine();

            var o = apiChecker.CheckAssumptions(assumptions, out temp);
            Debug.Assert(o == Outcome.Correct || o == Outcome.Errors);
            //Console.WriteLine("Result = " + o.ToString());

            if (o == Outcome.Correct) return true;
            return false;
        }

        public static void Partition<T>(HashSet<T> values, out HashSet<T> part1, out HashSet<T> part2)
        {
            part1 = new HashSet<T>();
            part2 = new HashSet<T>();
            var size = values.Count;
            var crossed = false;
            var curr = 0;
            foreach (var s in values)
            {
                if (crossed) part2.Add(s);
                else part1.Add(s);
                curr++;
                if (!crossed && curr >= size / 2) crossed = true;
            }
        }


        public override Outcome VerifyImplementation(Implementation/*!*/ impl, Program/*!*/ program, VerifierCallback/*!*/ callback)
        {
            Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

            #region stratified inlining options
            // This flag control the nature of queries made by Stratified VerifyImplementation
            // true: incremental search; false: in-place inlining
            bool incrementalSearch = true;
            // This flag allows the VCs (and live variable analysis) to be created on-demand
            bool createVConDemand = true;

            switch (CommandLineOptions.Clo.StratifiedInliningOption)
            {
                case 0:
                    incrementalSearch = true;
                    createVConDemand = true;
                    break;
                case 1:
                    incrementalSearch = false;
                    createVConDemand = true;
                    break;
                case 2:
                    incrementalSearch = true;
                    createVConDemand = false;
                    break;
                case 3:
                    incrementalSearch = false;
                    createVConDemand = false;
                    break;
            }
            #endregion

            // Get the checker
            Checker checker = FindCheckerFor(null, CommandLineOptions.Clo.ProverKillTime); Contract.Assert(checker != null);
            
            // Record current time
            var startTime = DateTime.Now;

            // Run live variable analysis
            if (CommandLineOptions.Clo.LiveVariableAnalysis == 2)
            {
                Microsoft.Boogie.InterProcGenKill.ComputeLiveVars(impl, program);
            }

            // Build VCs for all procedures
            Contract.Assert(implName2StratifiedInliningInfo != null);
            this.program = program;

            if (!createVConDemand)
            {
                foreach (StratifiedInliningInfo info in implName2StratifiedInliningInfo.Values)
                {
                    Contract.Assert(info != null);
                    GenerateVCForStratifiedInlining(program, info, checker);
                }
            }

            // Get the VC of the current procedure
            VCExpr vc;
            StratifiedInliningErrorReporter reporter;
            Hashtable/*<int, Absy!>*/ mainLabel2absy;
            GetVC(impl, program, callback, out vc, out mainLabel2absy, out reporter);

            // Find all procedure calls in vc and put labels on them      
            FCallHandler calls = new FCallHandler(checker.VCExprGen, implName2StratifiedInliningInfo, impl.Name, mainLabel2absy);
            calls.setCurrProcAsMain();
            vc = calls.Mutate(vc, true);
            reporter.SetCandidateHandler(calls);

            // create a process for displaying coverage information
            var coverageManager = new CoverageGraphManager(calls);
            coverageManager.addMain();

            // Put all of the necessary state into one object
            var vState = new VerificationState(vc, calls, reporter, checker);
            vState.vcSize += SizeComputingVisitor.ComputeSize(vc);
            vState.coverageManager = coverageManager;

            // We'll restore the original state of the theorem prover at the end
            // of this procedure
            vState.checker.Push();

            Outcome ret = Outcome.ReachedBound;

            #region eager inlining
            for (int i = 1; i < CommandLineOptions.Clo.StratifiedInlining && calls.currCandidates.Count > 0; i++)
            {
                List<int> toExpand = new List<int>();

                foreach (int id in calls.currCandidates)
                {
                    if (calls.isNonTrivialCandidate(id) && calls.getRecursionBound(id) <= CommandLineOptions.Clo.RecursionBound)
                    {
                        toExpand.Add(id);
                    }
                }
                DoExpansion(incrementalSearch, toExpand, vState);
            }
            #endregion

            #region Repopulate call tree, if there is one
            if (PersistCallTree && callTree != null)
            {
                bool expand = true;
                while (expand)
                {
                    List<int> toExpand = new List<int>();
                    foreach (int id in calls.currCandidates)
                    {
                        if (callTree.ContainsKey(calls.getPersistentId(id)))
                        {
                            toExpand.Add(id);
                        }
                    }
                    if (toExpand.Count == 0) expand = false;
                    else DoExpansion(incrementalSearch, toExpand, vState);
                }
            }
            #endregion

            #region Coverage reporter
            if (CommandLineOptions.Clo.CoverageReporterPath == "Console")
            {
                Console.WriteLine("Stratified Inlining: Size of VC after eager inlining: {0}", vState.vcSize);
            }
            #endregion

            // Under-approx query is only needed if something was inlined since
            // the last time an under-approx query was made
            // TODO: introduce this
            // bool underApproxNeeded = true;

            // The recursion bound for stratified search
            int bound = 1;

            int done = 0;

            // Process tasks while not done. We're done when:
            //   case 1: (correct) We didn't find a bug (either an over-approx query was valid
            //                     or we reached the recursion bound) and the task is "step"
            //   case 2: (bug)     We find a bug
            //   case 3: (internal error)   The theorem prover TimesOut of runs OutOfMemory
            while (true)
            {
                // Check timeout
                if (CommandLineOptions.Clo.ProverKillTime != -1)
                {
                    if ((DateTime.Now - startTime).TotalSeconds > CommandLineOptions.Clo.ProverKillTime)
                    {
                        ret = Outcome.TimedOut;
                        break;
                    }
                }

                // Note: in the absence of a coverage graph process, the task is always "step"
                coverageManager.syncGraph();
                var task = coverageManager.getNextTask();
                if (task.type == CoverageGraphManager.Task.TaskType.INLINE)
                {
                    if (done == 2) continue;
                    foreach (var id in task.nodes)
                    {
                        calls.setRecursionIncrement(id, 0);
                        coverageManager.addNode(id);
                    }
                    DoExpansion(incrementalSearch, task.nodes, vState);
                }
                else if (task.type == CoverageGraphManager.Task.TaskType.BLOCK)
                {
                    if (done == 2) continue;
                    foreach (var id in task.nodes)
                    {
                        calls.setRecursionIncrement(id, CommandLineOptions.Clo.RecursionBound + 1);
                        coverageManager.addNode(id);
                    }
                }
                else if (task.type == CoverageGraphManager.Task.TaskType.STEP)
                {
                    if (done > 0)
                    {
                        break;
                    }

                    // Stratified Step
                    ret = stratifiedStep(bound, vState);

                    // Sorry, out of luck (time/memory)
                    if (ret == Outcome.Inconclusive || ret == Outcome.OutOfMemory || ret == Outcome.TimedOut)
                    {
                        done = 3;
                        coverageManager.reportError();
                        continue;
                    }

                    if (ret == Outcome.Errors && reporter.underapproximationMode)
                    {
                        // Found a bug
                        done = 2;
                        coverageManager.reportBug();
                    }
                    else if (ret == Outcome.Correct)
                    {
                        // Correct
                        done = 1;
                        coverageManager.reportCorrect();
                    }
                    else if (ret == Outcome.ReachedBound)
                    {
                        // Increment bound
                        var minRecReached = CommandLineOptions.Clo.RecursionBound + 1;
                        foreach (var id in calls.currCandidates)
                        {
                            var rb = calls.getRecursionBound(id);
                            if (rb <= bound) continue;
                            if (rb < minRecReached) minRecReached = rb;
                        }
                        bound = minRecReached;

                        if (bound > CommandLineOptions.Clo.RecursionBound)
                        {
                            // Correct under bound
                            done = 1;
                            coverageManager.reportCorrect(bound);
                        }
                    }
                    else
                    {
                        // Do inlining
                        Debug.Assert(ret == Outcome.Errors && !reporter.underapproximationMode);
                        Contract.Assert(reporter.candidatesToExpand.Count != 0);

                        #region expand call tree

                        // Expand and try again
                        vState.checker.LogComment(";;;;;;;;;;;; Expansion begin ;;;;;;;;;;");
                        DoExpansion(incrementalSearch, reporter.candidatesToExpand, vState);
                        vState.checker.LogComment(";;;;;;;;;;;; Expansion end ;;;;;;;;;;");

                        #endregion
                    }
                }
                else if (task.type == CoverageGraphManager.Task.TaskType.REACHABLE)
                {
                    if (done == 2) continue;
                    var node = task.queryNode;
                    // assert that any path must pass through this node
                    var expr = calls.getTrueExpr(node);
                    vState.checker.AddAxiom(expr);
                }
                else
                {
                    Console.WriteLine("Ignoring task: " + task.ToString());
                }

            }

            // Pop off everything that we pushed so that there are no side effects from
            // this call to VerifyImplementation
            vState.checker.Pop();

            #region Coverage reporter
            if (CommandLineOptions.Clo.CoverageReporterPath == "Console")
            {
                Console.WriteLine("Stratified Inlining: Calls to Z3: {0}", vState.numQueries);
                Console.WriteLine("Stratified Inlining: Expansions performed: {0}", vState.expansionCount);
                Console.WriteLine("Stratified Inlining: Candidates left: {0}", calls.currCandidates.Count);
                Console.WriteLine("Stratified Inlining: Nontrivial Candidates left: {0}", calls.numNonTrivialCandidates());
                Console.WriteLine("Stratified Inlining: VC Size: {0}", vState.vcSize);
            }
            #endregion
            coverageManager.stop();

            // Store current call tree
            if (PersistCallTree && (ret == Outcome.Correct || ret == Outcome.Errors || ret == Outcome.ReachedBound))
            {
                callTree = new Dictionary<string, int>();
                //var persistentNodes = new HashSet<int>(calls.candidateParent.Values);
                var persistentNodes = new HashSet<int>(calls.candidateParent.Keys);
                persistentNodes.Add(0);
                persistentNodes.ExceptWith(calls.currCandidates);

                foreach (var id in persistentNodes)
                {
                    callTree.Add(calls.getPersistentId(id), 0);
                }
            }

            return ret;
        }

        // A step of the stratified inlining algorithm: both under-approx and over-approx queries
        private Outcome stratifiedStep(int bound, VerificationState vState)
        {
            Outcome ret;
            List<int> unsatCore;

            var reporter = vState.reporter;
            var calls = vState.calls;
            var checker = vState.checker;

            reporter.underapproximationMode = true;
            checker.LogComment(";;;;;;;;;;;; Underapprox mode begin ;;;;;;;;;;");
            List<VCExpr> assumptions;
            List<int> ids;

            while (true)
            {
                assumptions = new List<VCExpr>();
                ids = new List<int>();
                foreach (int id in calls.currCandidates)
                {
                    assumptions.Add(calls.getFalseExpr(id));
                    ids.Add(id);
                }

                ret = checker.CheckAssumptions(assumptions, out unsatCore);
                if (!CommandLineOptions.Clo.UseUnsatCoreForInlining) break;
                if (ret != Outcome.Correct) break;
                Debug.Assert(unsatCore.Count <= assumptions.Count);
                if (unsatCore.Count == assumptions.Count)
                    break;

                var unsatCoreIds = new List<int>();
                foreach (int i in unsatCore)
                    unsatCoreIds.Add(ids[i]);
                vState.checker.LogComment(";;;;;;;;;;;; Expansion begin ;;;;;;;;;;");
                bool incrementalSearch = 
                    CommandLineOptions.Clo.StratifiedInliningOption == 0 ||
                    CommandLineOptions.Clo.StratifiedInliningOption == 2;
                DoExpansion(incrementalSearch, unsatCoreIds, vState);
                vState.calls.forcedCandidates.UnionWith(unsatCoreIds);
                vState.checker.LogComment(";;;;;;;;;;;; Expansion end ;;;;;;;;;;");
            }

            checker.LogComment(";;;;;;;;;;;; Underapprox mode end ;;;;;;;;;;");

            if (ret == Outcome.Errors)
            {
                return ret;
            }

            if (ret != Outcome.Correct && ret != Outcome.Errors)
            {
                // The query ran out of memory or time, that's it,
                // we cannot do better. Give up!
                return ret;
            }

            // If we didn't underapproximate, then we're done
            if (calls.currCandidates.Count == 0)
            {
                Contract.Assert(ret == Outcome.Correct);
                return ret;
            }

            Contract.Assert(ret == Outcome.Correct);

            checker.LogComment(";;;;;;;;;;;; Overapprox mode begin ;;;;;;;;;;");

            // Over-approx query
            reporter.underapproximationMode = false;

            // Push "true" for all, except:
            // push "false" for all candidates that have reached
            // the recursion bounds

            bool allTrue = true;
            bool allFalse = true;

            assumptions = new List<VCExpr>();
            foreach (int id in calls.currCandidates)
            {
                if (calls.getRecursionBound(id) <= bound)
                {
                    //checker.TheoremProver.PushVCExpression(calls.getTrueExpr(id));
                    allFalse = false;
                }
                else
                {
                    //checker.AddAxiom(calls.getFalseExpr(id));
                    assumptions.Add(calls.getFalseExpr(id));
                    allTrue = false;
                }
            }

            if (allFalse)
            {
                // If we made all candidates false, then this is the same
                // as the underapprox query. We already know the answer.
                ret = Outcome.Correct;
            }
            else
            {
                ret = checker.CheckAssumptions(assumptions, out unsatCore);
            }

            if (ret != Outcome.Correct && ret != Outcome.Errors)
            {
                // The query ran out of memory or time, that's it,
                // we cannot do better. Give up!
                return ret;
            }

            if (ret == Outcome.Correct)
            {
                // If nothing was made false, then the program is correct
                if (allTrue)
                {
                    return ret;
                }

                // Nothing more can be done with current recursion bound. 
                return Outcome.ReachedBound;
            }

            Contract.Assert(ret == Outcome.Errors);

            checker.LogComment(";;;;;;;;;;;; Overapprox mode end ;;;;;;;;;;");

            return ret;
        }

        // A counter for adding new variables
        static int newVarCnt = 0;

        // Does on-demand inlining -- pushes procedure bodies on the theorem prover stack.
        private void DoExpansion(bool incremental, List<int>/*!*/ candidates, VerificationState vState)
        {
            vState.expansionCount += candidates.Count;

            if (incremental)
                DoExpansionAndPush(candidates, vState);
            else
                DoExpansionAndInline(candidates, vState);
        }

        // Does on-demand inlining -- pushes procedure bodies on the theorem prover stack.
        private void DoExpansionAndPush(List<int>/*!*/ candidates, VerificationState vState)
        {
            Contract.Requires(candidates != null);
            Contract.Requires(vState.calls != null);
            Contract.Requires(vState.checker != null);
            Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

            var checker = vState.checker.underlyingChecker;
            var calls = vState.calls;

            VCExpr exprToPush = VCExpressionGenerator.True;
            Contract.Assert(exprToPush != null);
            foreach (int id in candidates)
            {
                VCExprNAry expr = calls.id2Candidate[id];
                Contract.Assert(expr != null);
                string procName = cce.NonNull(expr.Op as VCExprBoogieFunctionOp).Func.Name;
                if (!implName2StratifiedInliningInfo.ContainsKey(procName)) continue;

                StratifiedInliningInfo info = implName2StratifiedInliningInfo[procName];
                if (!info.initialized)
                {
                    GenerateVCForStratifiedInlining(program, info, checker);
                }
                //Console.WriteLine("Inlining {0}", procName);
                VCExpr expansion = cce.NonNull(info.vcexpr);

                // Instantiate the "forall" variables
                Dictionary<VCExprVar, VCExpr> substForallDict = new Dictionary<VCExprVar, VCExpr>();
                Contract.Assert(info.interfaceExprVars.Count == expr.Length);
                for (int i = 0; i < info.interfaceExprVars.Count; i++)
                {
                    substForallDict.Add(info.interfaceExprVars[i], expr[i]);
                }
                if (procName == "boogie_si_record_int")
                {
                    Contract.Assert(expr.Length > program.GlobalVariables().Count);
                    calls.argExprMap.Add(id, expr[program.GlobalVariables().Count]);
                }
                VCExprSubstitution substForall = new VCExprSubstitution(substForallDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());

                SubstitutingVCExprVisitor subst = new SubstitutingVCExprVisitor(checker.VCExprGen);
                Contract.Assert(subst != null);
                expansion = subst.Mutate(expansion, substForall);

                // Instantiate and declare the "exists" variables
                Dictionary<VCExprVar, VCExpr> substExistsDict = new Dictionary<VCExprVar, VCExpr>();
                foreach (VCExprVar v in info.privateVars)
                {
                    Contract.Assert(v != null);
                    string newName = v.Name + "_si_" + newVarCnt.ToString();
                    newVarCnt++;
                    checker.TheoremProver.Context.DeclareConstant(new Constant(Token.NoToken, new TypedIdent(Token.NoToken, newName, v.Type)), false, null);
                    substExistsDict.Add(v, checker.VCExprGen.Variable(newName, v.Type));
                }
                VCExprSubstitution substExists = new VCExprSubstitution(substExistsDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());

                subst = new SubstitutingVCExprVisitor(checker.VCExprGen);
                expansion = subst.Mutate(expansion, substExists);

                if (!calls.currCandidates.Contains(id))
                {
                    Console.WriteLine("Don't know what we just expanded");
                }

                calls.currCandidates.Remove(id);

                // Record the new set of candidates and rename absy labels
                calls.currInlineCount = id;
                calls.setCurrProc(procName);
                expansion = calls.Mutate(expansion, true);
                vState.coverageManager.addRecentEdges(id);

                //expansion = checker.VCExprGen.Eq(calls.id2ControlVar[id], expansion);
                expansion = checker.VCExprGen.Implies(calls.id2ControlVar[id], expansion);

                exprToPush = checker.VCExprGen.And(exprToPush, expansion);
            }
            vState.checker.AddAxiom(exprToPush);
            vState.vcSize += SizeComputingVisitor.ComputeSize(exprToPush);
        }

        // Does on-demand inlining -- inlines procedures into the VC of main.
        private void DoExpansionAndInline(List<int>/*!*/ candidates, VerificationState vState)
        {
            Contract.Requires(vState.vcMain != null);
            Contract.Requires(candidates != null);
            Contract.Requires(vState.calls != null);
            Contract.Requires(vState.checker != null);
            Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

            var checker = vState.checker.underlyingChecker;
            var calls = vState.calls;

            FCallInliner inliner = new FCallInliner(checker.VCExprGen);
            Contract.Assert(inliner != null);
            foreach (int id in candidates)
            {
                VCExprNAry expr = calls.id2Candidate[id];
                Contract.Assert(expr != null);

                string procName = (cce.NonNull(expr.Op as VCExprBoogieFunctionOp)).Func.Name;
                if (!implName2StratifiedInliningInfo.ContainsKey(procName)) continue;

                StratifiedInliningInfo info = implName2StratifiedInliningInfo[procName];
                if (!info.initialized)
                {
                    GenerateVCForStratifiedInlining(program, info, checker);
                }

                VCExpr expansion = cce.NonNull(info.vcexpr);

                // Instantiate the "forall" variables
                Dictionary<VCExprVar, VCExpr> substForallDict = new Dictionary<VCExprVar, VCExpr>();
                Contract.Assert(info.interfaceExprVars.Count == expr.Length);
                for (int i = 0; i < info.interfaceExprVars.Count; i++)
                {
                    substForallDict.Add(info.interfaceExprVars[i], expr[i]);
                }
                if (procName == "boogie_si_record_int")
                {
                    Contract.Assert(expr.Length > program.GlobalVariables().Count);
                    calls.argExprMap.Add(id, expr[program.GlobalVariables().Count]);
                }

                VCExprSubstitution substForall = new VCExprSubstitution(substForallDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());

                SubstitutingVCExprVisitor subst = new SubstitutingVCExprVisitor(checker.VCExprGen); Contract.Assert(subst != null);
                expansion = subst.Mutate(expansion, substForall);

                // Instantiate and declare the "exists" variables
                Dictionary<VCExprVar, VCExpr> substExistsDict = new Dictionary<VCExprVar, VCExpr>();
                for (int i = 0; i < info.privateVars.Count; i++)
                {
                    VCExprVar v = info.privateVars[i];
                    string newName = v.Name + "_si_" + newVarCnt.ToString();
                    newVarCnt++;
                    checker.TheoremProver.Context.DeclareConstant(new Constant(Token.NoToken, new TypedIdent(Token.NoToken, newName, v.Type)), false, null);
                    substExistsDict.Add(v, checker.VCExprGen.Variable(newName, v.Type));
                }
                VCExprSubstitution substExists = new VCExprSubstitution(substExistsDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());

                subst = new SubstitutingVCExprVisitor(checker.VCExprGen);
                expansion = subst.Mutate(expansion, substExists);

                if (!calls.currCandidates.Contains(id))
                {
                    Console.WriteLine("Don't know what we just expanded");
                }

                calls.currCandidates.Remove(id);

                // Record the new set of candidates and rename absy labels
                calls.currInlineCount = id;
                calls.setCurrProc(procName);
                expansion = calls.Mutate(expansion, true);
                vState.coverageManager.addRecentEdges(id);

                inliner.subst.Add(id, expansion);

            }

            vState.vcMain = inliner.Mutate(vState.vcMain, true);
            vState.vcSize = SizeComputingVisitor.ComputeSize(vState.vcMain);
        }

        // Return the VC for the impl (don't pass it to the theorem prover).
        // GetVC is a cheap imitation of VerifyImplementation, except that the VC is not passed to the theorem prover.
        private void GetVC(Implementation/*!*/ impl, Program/*!*/ program, VerifierCallback/*!*/ callback, out VCExpr/*!*/ vc, out Hashtable/*<int, Absy!>*//*!*/ label2absy, out StratifiedInliningErrorReporter/*!*/ reporter)
        {
            Contract.Requires(impl != null);
            Contract.Requires(program != null);
            Contract.Requires(callback != null);
            Contract.Ensures(Contract.ValueAtReturn(out vc) != null);
            Contract.Ensures(Contract.ValueAtReturn(out label2absy) != null);
            Contract.Ensures(Contract.ValueAtReturn(out reporter) != null);

            ConvertCFG2DAG(impl, program);
            ModelViewInfo mvInfo;
            Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = PassifyImpl(impl, program, out mvInfo);
            Checker checker = FindCheckerFor(impl, CommandLineOptions.Clo.ProverKillTime);
            Contract.Assert(checker != null);
            
            vc = GenerateVC(impl, null, out label2absy, checker);

            /*
            ErrorReporter errReporter;
            if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local) {
              errReporter = new ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, incarnationOriginMap, callback, implName2LazyInliningInfo, checker.TheoremProver.Context, program);
            } else {
              errReporter = new ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, incarnationOriginMap, callback, implName2LazyInliningInfo, checker.TheoremProver.Context, program);
            }
            */

            reporter = new StratifiedInliningErrorReporter(
               cce.NonNull(implName2StratifiedInliningInfo), checker.TheoremProver, callback, mvInfo,
               checker.TheoremProver.Context, gotoCmdOrigins, program, impl);

        }


        // Uniquely identifies a procedure call (the call expr, instance)
        public class BoogieCallExpr : IEquatable<BoogieCallExpr>
        {
            public NAryExpr expr;
            public int inlineCnt;

            public BoogieCallExpr(NAryExpr expr, int inlineCnt)
            {
                this.expr = expr;
                this.inlineCnt = inlineCnt;
            }

            public override int GetHashCode()
            {
                return expr.GetHashCode() + 131 * inlineCnt.GetHashCode();
            }

            public override bool Equals(object obj)
            {
                BoogieCallExpr that = obj as BoogieCallExpr;
                return (expr == that.expr && inlineCnt == that.inlineCnt);
            }

            public bool Equals(BoogieCallExpr that)
            {
                return (expr == that.expr && inlineCnt == that.inlineCnt);
            }
        }

        // This class is used to traverse VCs and do the following:
        // -- collect the set of FunctionCall nodes and label them with a unique string
        // -- Rename all other labels (so that calling this on the same VC results in 
        //    VCs with different labels each time)
        public class FCallHandler : MutatingVCExprVisitor<bool>
        {
            Dictionary<string/*!*/, StratifiedInliningInfo/*!*/>/*!*/ implName2StratifiedInliningInfo;
            public readonly Hashtable/*<int, Absy!>*//*!*/ mainLabel2absy;
            public Dictionary<BoogieCallExpr/*!*/, int>/*!*/ boogieExpr2Id;
            public Dictionary<int, VCExprNAry/*!*/>/*!*/ id2Candidate;
            public Dictionary<int, VCExprVar/*!*/>/*!*/ id2ControlVar;
            public Dictionary<string/*!*/, int>/*!*/ label2Id;
            // Stores the candidate from which this one originated
            public Dictionary<int, int> candidateParent;
            // Mapping from candidate Id to the "si_unique_call" id that led to 
            // this candidate. This is useful for getting persistent names for
            // candidates
            public Dictionary<int, int> candidate2callId;
            // A cache for candidate id to its persistent name
            public Dictionary<int, string> persistentNameCache;
            // Inverse of the above map
            public Dictionary<string, int> persistentNameInv;
            // Used to record candidates recently added
            public HashSet<int> recentlyAddedCandidates;
            // Name of main procedure
            private string mainProcName;
            // A map from candidate id to the VCExpr that represents its
            // first argument (used for obtaining concrete values in error trace)
            public Dictionary<int, VCExpr> argExprMap;

            public HashSet<int> forcedCandidates;

            // User info -- to decrease/increase calculation of recursion bound
            public Dictionary<int, int> recursionIncrement;

            public HashSet<int> currCandidates;
            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
                Contract.Invariant(mainLabel2absy != null);
                Contract.Invariant(boogieExpr2Id != null);
                Contract.Invariant(cce.NonNullDictionaryAndValues(id2Candidate));
                Contract.Invariant(cce.NonNullDictionaryAndValues(id2ControlVar));
                Contract.Invariant(label2Id != null);
            }

            // Name of the procedure whose VC we're mutating
            string currProc;

            // The 0^th candidate is main
            static int candidateCount = 1;
            public int currInlineCount;

            public FCallHandler(VCExpressionGenerator/*!*/ gen,
                                  Dictionary<string/*!*/, StratifiedInliningInfo/*!*/>/*!*/ implName2StratifiedInliningInfo,
                                  string mainProcName, Hashtable/*<int, Absy!>*//*!*/ mainLabel2absy)
                : base(gen)
            {
                Contract.Requires(gen != null);
                Contract.Requires(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
                Contract.Requires(mainLabel2absy != null);
                this.implName2StratifiedInliningInfo = implName2StratifiedInliningInfo;
                this.mainProcName = mainProcName;
                this.mainLabel2absy = mainLabel2absy;
                id2Candidate = new Dictionary<int, VCExprNAry>();
                id2ControlVar = new Dictionary<int, VCExprVar>();
                boogieExpr2Id = new Dictionary<BoogieCallExpr, int>();
                label2Id = new Dictionary<string, int>();
                currCandidates = new HashSet<int>();
                currInlineCount = 0;
                currProc = null;
                labelRenamer = new Dictionary<string, int>();
                labelRenamerInv = new Dictionary<string, string>();
                candidateParent = new Dictionary<int, int>();
                //callGraphMapping = new Dictionary<int, int>();
                recursionIncrement = new Dictionary<int, int>();
                candidate2callId = new Dictionary<int, int>();
                persistentNameCache = new Dictionary<int, string>();
                persistentNameInv = new Dictionary<string, int>();
                persistentNameCache[0] = "0";
                persistentNameInv["0"] = 0;
                recentlyAddedCandidates = new HashSet<int>();
                argExprMap = new Dictionary<int, VCExpr>();

                forcedCandidates = new HashSet<int>();
            }

            public void Clear()
            {
                currCandidates = new HashSet<int>();
            }

            // Given a candidate "id", let proc(id) be the
            // procedure corresponding to id. This procedure returns
            // the number of times proc(id) appears as an ancestor
            // of id. This is the same as the number of times we've
            // recursed on proc(id)
            public int getRecursionBound(int id)
            {
                int ret = 1;
                var str = getProc(id);

                while (candidateParent.ContainsKey(id))
                {
                    if (recursionIncrement.ContainsKey(id)) ret += recursionIncrement[id];
                    id = candidateParent[id];
                    if (getProc(id) == str && !forcedCandidates.Contains(id)) ret++;
                }
                return ret;
            }

            // Set user-define increment/decrement to recursionBound
            public void setRecursionIncrement(int id, int incr)
            {
                if (recursionIncrement.ContainsKey(id))
                    recursionIncrement[id] = incr;
                else
                    recursionIncrement.Add(id, incr);
            }

            // Returns the name of the procedure corresponding to candidate id
            public string getProc(int id)
            {
                if (id == 0) return mainProcName;

                return (id2Candidate[id].Op as VCExprBoogieFunctionOp).Func.Name;
            }

            // Get a unique id for this candidate (dependent only on the Call
            // graph of the program). The persistent id is:
            // 0: for main
            // a_b_c: where a is the persistent id of parent, and b is the procedure name
            //        and c is the unique call id (if any)
            public string getPersistentId(int top_id)
            {
                if (top_id == 0) return "0";
                Debug.Assert(candidateParent.ContainsKey(top_id));
                if (persistentNameCache.ContainsKey(top_id))
                    return persistentNameCache[top_id];

                var parent_id = getPersistentId(candidateParent[top_id]);
                var call_id = candidate2callId.ContainsKey(top_id) ? candidate2callId[top_id] : -1;
                var ret = string.Format("{0}_131_{1}_131_{2}", parent_id, getProc(top_id), call_id);
                persistentNameCache[top_id] = ret;
                persistentNameInv[ret] = top_id;
                return ret;
            }

            public int getCandidateFromGraphNode(string n)
            {
                if (!persistentNameInv.ContainsKey(n))
                {
                    return -1;
                }
                return persistentNameInv[n];
            }

            private int GetNewId(VCExprNAry vc)
            {
                Contract.Requires(vc != null);
                int id = candidateCount;

                id2Candidate[id] = vc;
                id2ControlVar[id] = Gen.Variable("si_control_var_bool_" + id.ToString(), Microsoft.Boogie.Type.Bool);

                candidateCount++;
                currCandidates.Add(id);
                recentlyAddedCandidates.Add(id);

                return id;
            }

            private string GetLabel(int id)
            {
                Contract.Ensures(Contract.Result<string>() != null);

                string ret = "si_fcall_" + id.ToString();
                if (!label2Id.ContainsKey(ret))
                    label2Id[ret] = id;

                return ret;
            }

            public int GetId(string label)
            {
                Contract.Requires(label != null);
                if (!label2Id.ContainsKey(label))
                    return -1;
                return label2Id[label];
            }

            Dictionary<string, int> labelRenamer;
            Dictionary<string, string> labelRenamerInv;

            public string RenameAbsyLabel(string label)
            {
                Contract.Requires(label != null);
                Contract.Requires(label.Length >= 1);
                Contract.Ensures(Contract.Result<string>() != null);

                // Remove the sign from the label
                string nosign = label.Substring(1);
                var ret = "si_inline_" + currInlineCount.ToString() + "_" + nosign;

                if (!labelRenamer.ContainsKey(ret))
                {
                    var c = labelRenamer.Count + 11; // two digit labels only
                    labelRenamer.Add(ret, c);
                    labelRenamerInv.Add(c.ToString(), ret);
                }
                return labelRenamer[ret].ToString();
            }

            public string ParseRenamedAbsyLabel(string label, int cnt)
            {
                Contract.Requires(label != null);
                if (!labelRenamerInv.ContainsKey(label))
                {
                    return null;
                }
                var str = labelRenamerInv[label];
                var prefix = "si_inline_" + cnt.ToString() + "_";
                if (!str.StartsWith(prefix)) return null;
                return str.Substring(prefix.Length);
            }

            public void setCurrProc(string name)
            {
                Contract.Requires(name != null);
                currProc = name;
                Contract.Assert(implName2StratifiedInliningInfo.ContainsKey(name));
            }

            public void setCurrProcAsMain()
            {
                currProc = "";
            }

            // Return the formula (candidate IFF false)
            public VCExpr getFalseExpr(int candidateId)
            {
                //return Gen.Eq(VCExpressionGenerator.False, id2ControlVar[candidateId]);
                return Gen.Not(id2ControlVar[candidateId]);
            }

            // Return the formula (candidate IFF true)
            public VCExpr getTrueExpr(int candidateId)
            {
                return Gen.Eq(VCExpressionGenerator.True, id2ControlVar[candidateId]);
            }

            private Hashtable/*<int,absy>*/ getLabel2absy()
            {
                Contract.Ensures(Contract.Result<Hashtable>() != null);

                Contract.Assert(currProc != null);
                if (currProc == "")
                {
                    return mainLabel2absy;
                }
                return cce.NonNull(implName2StratifiedInliningInfo[currProc].label2absy);
            }

            // How many of the current candidates represent calls to procedures
            // with non-trivial mod sets.
            // This is only used for statistic purposes
            public bool isNonTrivialCandidate(int id)
            {
                string proc = getProc(id);
                if (proc == "") return false;
                if (!implName2StratifiedInliningInfo.ContainsKey(proc)) return false;
                var info = implName2StratifiedInliningInfo[proc];
                if (info.impl.Proc.Modifies.Length != 0) return true;
                return false;
                /*
                foreach (IdentifierExpr ie in info.impl.Proc.Modifies)
                {
                    if (ie.Decl.Name.StartsWith("Mem_") || ie.Decl.Name.StartsWith("Res_"))
                    {
                        return true;
                    }
                }
                return false;
                 */
            }

            public int numNonTrivialCandidates()
            {
                int ret = 0;
                foreach (int id in currCandidates)
                {
                    if (isNonTrivialCandidate(id)) ret++;
                }
                return ret;
            }

            // Finds labels and changes them:
            //   si_fcall_id:  if "id" corresponds to a tracked procedure call, then
            //                 si_control_var_candidateId
            //   si_fcall_id:  if "id" does not corresponds to a tracked procedure call, then
            //                 delete
            //   num:          si_inline_num
            //  
            protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode,
                                                          List<VCExpr/*!*/>/*!*/ newSubExprs,
                // has any of the subexpressions changed?
                                                          bool changed,
                                                          bool arg)
            {
                //Contract.Requires(originalNode != null);
                //Contract.Requires(cce.NonNullElements(newSubExprs));
                Contract.Ensures(Contract.Result<VCExpr>() != null);

                VCExpr ret;
                if (changed)
                    ret = Gen.Function(originalNode.Op,
                                       newSubExprs, originalNode.TypeArguments);
                else
                    ret = originalNode;

                VCExprLabelOp lop = originalNode.Op as VCExprLabelOp;
                if (lop == null) return ret;
                if (!(ret is VCExprNAry)) return ret;

                VCExprNAry retnary = (VCExprNAry)ret;
                Contract.Assert(retnary != null);
                string prefix = "si_fcall_"; // from Wlp.ssc::Cmd(...)
                if (lop.label.Substring(1).StartsWith(prefix))
                {
                    int id = Int32.Parse(lop.label.Substring(prefix.Length + 1));
                    Hashtable label2absy = getLabel2absy();
                    Absy cmd = label2absy[id] as Absy;
                    //label2absy.Remove(id);

                    Contract.Assert(cmd != null);
                    AssumeCmd acmd = cmd as AssumeCmd;
                    Contract.Assert(acmd != null);
                    NAryExpr naryExpr = acmd.Expr as NAryExpr;
                    Contract.Assert(naryExpr != null);

                    string calleeName = naryExpr.Fun.FunctionName;

                    VCExprNAry callExpr = retnary[0] as VCExprNAry;
                    Contract.Assert(callExpr != null);

                    if (implName2StratifiedInliningInfo.ContainsKey(calleeName))
                    {
                        int candidateId = GetNewId(callExpr);
                        boogieExpr2Id[new BoogieCallExpr(naryExpr, currInlineCount)] = candidateId;
                        candidateParent[candidateId] = currInlineCount;
                        string label = GetLabel(candidateId);
                        var unique_call_id = QKeyValue.FindIntAttribute(acmd.Attributes, "si_unique_call", -1);
                        if (unique_call_id != -1)
                            candidate2callId[candidateId] = unique_call_id;

                        //return Gen.LabelPos(label, callExpr);
                        return Gen.LabelPos(label, id2ControlVar[candidateId]);
                    }
                    else
                    {
                        return callExpr;
                    }
                }

                // Else, rename label
                string newLabel = RenameAbsyLabel(lop.label);
                if (lop.pos)
                {
                    return Gen.LabelPos(newLabel, retnary[0]);
                }
                else
                {
                    return Gen.LabelNeg(newLabel, retnary[0]);
                }

            }

        } // end FCallHandler


        public class FCallInliner : MutatingVCExprVisitor<bool>
        {
            public Dictionary<int, VCExpr/*!*/>/*!*/ subst;
            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(cce.NonNullDictionaryAndValues(subst));
            }


            public FCallInliner(VCExpressionGenerator gen)
                : base(gen)
            {
                Contract.Requires(gen != null);
                subst = new Dictionary<int, VCExpr>();
            }

            public void Clear()
            {
                subst = new Dictionary<int, VCExpr>();
            }

            protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode,
                                                          List<VCExpr/*!*/>/*!*/ newSubExprs,
                // has any of the subexpressions changed?
                                                          bool changed,
                                                          bool arg)
            {
                //Contract.Requires(originalNode != null);Contract.Requires(newSubExprs != null);
                Contract.Ensures(Contract.Result<VCExpr>() != null);

                VCExpr ret;
                if (changed)
                    ret = Gen.Function(originalNode.Op,
                                       newSubExprs, originalNode.TypeArguments);
                else
                    ret = originalNode;

                VCExprLabelOp lop = originalNode.Op as VCExprLabelOp;
                if (lop == null) return ret;
                if (!(ret is VCExprNAry)) return ret;

                string prefix = "si_fcall_"; // from FCallHandler::GetLabel
                if (lop.label.Substring(1).StartsWith(prefix))
                {
                    int id = Int32.Parse(lop.label.Substring(prefix.Length + 1));
                    if (subst.ContainsKey(id))
                    {
                        return subst[id];
                    }
                }
                return ret;
            }

        } // end FCallInliner

        public class EmptyErrorHandler : ProverInterface.ErrorHandler
        {
            public override void OnModel(IList<string> labels, ErrorModel errModel)
            {
                
            }
        }

        public class StratifiedInliningErrorReporter : ProverInterface.ErrorHandler
        {
            Dictionary<string/*!*/, StratifiedInliningInfo/*!*/>/*!*/ implName2StratifiedInliningInfo;
            ProverInterface/*!*/ theoremProver;
            VerifierCallback/*!*/ callback;
            ModelViewInfo mvInfo;
            FCallHandler calls;
            Program/*!*/ program;
            Implementation/*!*/ mainImpl;
            ProverContext/*!*/ context;
            Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins;

            public bool underapproximationMode;
            public List<int>/*!*/ candidatesToExpand;

            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(candidatesToExpand != null);
                Contract.Invariant(context != null);
                Contract.Invariant(mainImpl != null);
                Contract.Invariant(program != null);
                Contract.Invariant(callback != null);
                Contract.Invariant(theoremProver != null);
                Contract.Invariant(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
            }


            public StratifiedInliningErrorReporter(Dictionary<string/*!*/, StratifiedInliningInfo/*!*/>/*!*/ implName2StratifiedInliningInfo,
                                                   ProverInterface/*!*/ theoremProver, VerifierCallback/*!*/ callback, ModelViewInfo mvInfo, ProverContext/*!*/ context,
                                                   Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins,
                                                   Program/*!*/ program, Implementation/*!*/ mainImpl)
            {
                Contract.Requires(cce.NonNullDictionaryAndValues(implName2StratifiedInliningInfo));
                Contract.Requires(theoremProver != null);
                Contract.Requires(callback != null);
                Contract.Requires(context != null);
                Contract.Requires(mainImpl != null);
                this.implName2StratifiedInliningInfo = implName2StratifiedInliningInfo;
                this.theoremProver = theoremProver;
                this.callback = callback;
                this.mvInfo = mvInfo;
                this.context = context;
                this.program = program;
                this.mainImpl = mainImpl;
                this.underapproximationMode = false;
                this.calls = null;
                this.candidatesToExpand = new List<int>();
                this.gotoCmdOrigins = gotoCmdOrigins;
            }

            public void SetCandidateHandler(FCallHandler calls)
            {
                Contract.Requires(calls != null);
                this.calls = calls;
            }

            public override void OnModel(IList<string/*!*/>/*!*/ labels, ErrorModel errModel)
            {
                candidatesToExpand = new List<int>();

                //Contract.Requires(cce.NonNullElements(labels));
                if (underapproximationMode)
                {
                    if (errModel == null)
                        return;
                    var cex = GenerateTraceMain(labels, errModel, mvInfo);
                    Debug.Assert(candidatesToExpand.Count == 0);
                    if(cex != null) callback.OnCounterexample(cex, null);
                    return;
                }
                
                Contract.Assert(calls != null);
                Contract.Assert(errModel != null);

                GenerateTraceMain(labels, errModel, mvInfo);

                /*
                    foreach (string lab in labels)
                    {
                        Contract.Assert(lab != null);
                        int id = calls.GetId(lab);
                        if (id < 0)
                            continue;
                        if (!calls.currCandidates.Contains(id))
                            continue;
                        candidatesToExpand.Add(id);
                    }
                */
            }

            // Construct the interprocedural trace
            private Counterexample GenerateTraceMain(IList<string/*!*/>/*!*/ labels, ErrorModel/*!*/ errModel, ModelViewInfo mvInfo)
            {
                Contract.Requires(errModel != null);
                Contract.Requires(cce.NonNullElements(labels));
                if (CommandLineOptions.Clo.PrintErrorModel >= 1 && errModel != null)
                {
                    errModel.Print(ErrorReporter.ModelWriter);
                    ErrorReporter.ModelWriter.Flush();
                }

                Counterexample newCounterexample =
                  GenerateTrace(labels, errModel, mvInfo, 0, mainImpl);

                if (newCounterexample == null)
                    return null;

                #region Map passive program errors back to original program errors
                ReturnCounterexample returnExample = newCounterexample as ReturnCounterexample;
                if (returnExample != null && gotoCmdOrigins != null)
                {
                    foreach (Block b in returnExample.Trace)
                    {
                        Contract.Assert(b != null);
                        Contract.Assume(b.TransferCmd != null);
                        ReturnCmd cmd = (ReturnCmd)gotoCmdOrigins[b.TransferCmd];
                        if (cmd != null)
                        {
                            returnExample.FailingReturn = cmd;
                            break;
                        }
                    }
                }
                #endregion

                return newCounterexample;
            }

            private Counterexample GenerateTrace(IList<string/*!*/>/*!*/ labels, ErrorModel/*!*/ errModel, ModelViewInfo mvInfo,
                                                 int candidateId, Implementation procImpl)
            {
                Contract.Requires(errModel != null);
                Contract.Requires(cce.NonNullElements(labels));
                Contract.Requires(procImpl != null);

                Hashtable traceNodes = new Hashtable();
                //string procPrefix = "si_inline_" + candidateId.ToString() + "_";

                //Console.WriteLine("GenerateTrace: {0}", procImpl.Name);
                foreach (string s in labels)
                {
                    Contract.Assert(s != null);
                    var absylabel = calls.ParseRenamedAbsyLabel(s, candidateId);

                    if (absylabel == null) continue;

                    Absy absy;

                    if (candidateId == 0)
                    {
                        absy = Label2Absy(absylabel);
                    }
                    else
                    {
                        absy = Label2Absy(procImpl.Name, absylabel);
                    }

                    if (traceNodes.ContainsKey(absy))
                        System.Console.WriteLine("Warning: duplicate label: " + s + " read while tracing nodes");
                    else
                        traceNodes.Add(absy, null);
                }

                BlockSeq trace = new BlockSeq();
                Block entryBlock = cce.NonNull(procImpl.Blocks[0]);
                Contract.Assert(entryBlock != null);
                Contract.Assert(traceNodes.Contains(entryBlock));
                trace.Add(entryBlock);

                var calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();
                Counterexample newCounterexample = GenerateTraceRec(labels, errModel, mvInfo, candidateId, entryBlock, traceNodes, trace, calleeCounterexamples);

                return newCounterexample;

            }

            private Counterexample GenerateTraceRec(
                                  IList<string/*!*/>/*!*/ labels, ErrorModel/*!*/ errModel, ModelViewInfo mvInfo, int candidateId,
                                  Block/*!*/ b, Hashtable/*!*/ traceNodes, BlockSeq/*!*/ trace,
                                  Dictionary<TraceLocation/*!*/, CalleeCounterexampleInfo/*!*/>/*!*/ calleeCounterexamples)
            {
                Contract.Requires(cce.NonNullElements(labels));
                Contract.Requires(errModel != null);
                Contract.Requires(b != null);
                Contract.Requires(traceNodes != null);
                Contract.Requires(trace != null);
                Contract.Requires(cce.NonNullDictionaryAndValues(calleeCounterexamples));
                // After translation, all potential errors come from asserts.
                while (true)
                {
                    CmdSeq cmds = b.Cmds;
                    TransferCmd transferCmd = cce.NonNull(b.TransferCmd);
                    for (int i = 0; i < cmds.Length; i++)
                    {
                        Cmd cmd = cce.NonNull(cmds[i]);

                        // Skip if 'cmd' not contained in the trace or not an assert
                        if (cmd is AssertCmd && traceNodes.Contains(cmd))
                        {
                            Counterexample newCounterexample = AssertCmdToCounterexample((AssertCmd)cmd, transferCmd, trace, errModel, mvInfo, context, new Dictionary<Incarnation, Absy/*!*/>());
                            newCounterexample.AddCalleeCounterexample(calleeCounterexamples);
                            return newCounterexample;
                        }

                        // Counterexample generation for inlined procedures
                        AssumeCmd assumeCmd = cmd as AssumeCmd;
                        if (assumeCmd == null)
                            continue;
                        NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
                        if (naryExpr == null)
                            continue;
                        string calleeName = naryExpr.Fun.FunctionName;
                        Contract.Assert(calleeName != null);
                        if (!implName2StratifiedInliningInfo.ContainsKey(calleeName))
                            continue;

                        Contract.Assert(calls != null);
                        int calleeId = calls.boogieExpr2Id[new BoogieCallExpr(naryExpr, candidateId)];
                        if (calls.currCandidates.Contains(calleeId))
                        {
                            candidatesToExpand.Add(calleeId);
                        }
                        else
                        {
                            var values = new List<object>();
                            if (calleeName == "boogie_si_record_int")
                            {
                                // Record concrete value of the argument to this procedure
                                var args = new List<int>();
                                var expr = calls.argExprMap[calleeId];
                                if (expr is VCExprIntLit)
                                {
                                    args.Add(errModel.valueToPartition[(expr as VCExprIntLit).Val.ToInt]);
                                }
                                else if (expr is VCExprVar)
                                {
                                    var idExpr = expr as VCExprVar;
                                    string name = context.Lookup(idExpr);
                                    Contract.Assert(name != null);
                                    args.Add(errModel.identifierToPartition[name]);
                                }
                                else
                                {
                                    Contract.Assert(false);
                                }
                                values = errModel.PartitionsToValues(args);
                            }

                            calleeCounterexamples[new TraceLocation(trace.Length - 1, i)] =
                                new CalleeCounterexampleInfo(
                                    cce.NonNull(GenerateTrace(labels, errModel, mvInfo, calleeId, implName2StratifiedInliningInfo[calleeName].impl)),
                                    values);
                        }
                    }

                    GotoCmd gotoCmd = transferCmd as GotoCmd;
                    if (gotoCmd != null)
                    {
                        b = null;
                        foreach (Block bb in cce.NonNull(gotoCmd.labelTargets))
                        {
                            Contract.Assert(bb != null);
                            if (traceNodes.Contains(bb))
                            {
                                trace.Add(bb);
                                b = bb;
                                break;
                                //return GenerateTraceRec(labels, errModel, candidateId, bb, traceNodes, trace, calleeCounterexamples);
                            }
                        }
                        if (b != null) continue;
                    }
                    return null;
                }

                //return null;

            }

            public override Absy Label2Absy(string label)
            {
                //Contract.Requires(label != null);
                Contract.Ensures(Contract.Result<Absy>() != null);

                int id = int.Parse(label);
                Contract.Assert(calls != null);
                return cce.NonNull((Absy)calls.mainLabel2absy[id]);
            }

            public Absy Label2Absy(string procName, string label)
            {
                Contract.Requires(label != null);
                Contract.Requires(procName != null);
                Contract.Ensures(Contract.Result<Absy>() != null);

                int id = int.Parse(label);
                Hashtable l2a = cce.NonNull(implName2StratifiedInliningInfo[procName]).label2absy;
                return cce.NonNull((Absy)l2a[id]);
            }

            public override void OnResourceExceeded(string msg)
            {
                //Contract.Requires(msg != null);
                //resourceExceededMessage = msg;
            }

            public override void OnProverWarning(string msg)
            {
                //Contract.Requires(msg != null);
                callback.OnWarning(msg);
            }
        }

        // Used inside PassifyImpl
        protected override void addExitAssert(string implName, Block exitBlock)
        {
            if (implName2StratifiedInliningInfo != null && implName2StratifiedInliningInfo.ContainsKey(implName))
            {
                Expr assertExpr = implName2StratifiedInliningInfo[implName].assertExpr;
                Contract.Assert(assertExpr != null);
                exitBlock.Cmds.Add(new AssertCmd(Token.NoToken, assertExpr));
            }
        }

        protected override void storeIncarnationMaps(string implName, Hashtable exitIncarnationMap)
        {
            if (implName2StratifiedInliningInfo != null && implName2StratifiedInliningInfo.ContainsKey(implName))
            {
                StratifiedInliningInfo info = implName2StratifiedInliningInfo[implName];
                Contract.Assert(info != null);
                info.exitIncarnationMap = exitIncarnationMap;
                info.incarnationOriginMap = this.incarnationOriginMap;
            }
        }

        protected override bool elIsLoop(string procname)
        {
            Contract.Requires(procname != null);

            LazyInliningInfo info = null;
            if (implName2StratifiedInliningInfo.ContainsKey(procname))
            {
                info = implName2StratifiedInliningInfo[procname] as LazyInliningInfo;
            }

            if (info == null) return false;

            var lp = info.impl.Proc as LoopProcedure;

            if (lp == null) return false;
            return true;
        }

    } // class StratifiedVCGen

} // namespace VC
