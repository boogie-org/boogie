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

    // Types whose values can be recorded
    public enum RECORD_TYPES { INT, BOOL, INT_INT, INT_BOOL };

    public class StratifiedVCGen : VCGen
    {
        private Dictionary<string, StratifiedInliningInfo> implName2StratifiedInliningInfo;
        public bool PersistCallTree;
        public static Dictionary<string, int> callTree = null;
        public int numInlined = 0;
        public readonly static string recordProcName = "boogie_si_record";
        private bool useSummary;
        private SummaryComputation summaryComputation;
        private HashSet<string> procsThatReachedRecBound;

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
            useSummary = false;
            procsThatReachedRecBound = new HashSet<string>();
        }

        public static RECORD_TYPES getRecordType(Bpl.Type type)
        {
            if (type.IsInt) return RECORD_TYPES.INT;
            if (type.IsBool) return RECORD_TYPES.BOOL;
            Contract.Assert(type.IsMap);
            var mt = type.AsMap;
            Contract.Assert(mt.MapArity == 1);
            Contract.Assert(mt.Result.IsInt || mt.Result.IsBool);
            Contract.Assert(mt.Arguments[0].IsInt);
            if (mt.Result.IsInt) return RECORD_TYPES.INT_INT;
            return RECORD_TYPES.INT_BOOL;
        }
        /*
        public static string printValue(object val, RECORD_TYPES type)
        {
            switch (type)
            {
                case RECORD_TYPES.BOOL:
                    return ((bool)val).ToString();
                case RECORD_TYPES.INT:
                    return ((int)val).ToString();
                case RECORD_TYPES.INT_BOOL:
                case RECORD_TYPES.INT_INT:
            }
        }
        */
        public class StratifiedInliningInfo : LazyInliningInfo
        {
            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(cce.NonNullElements(privateVars));
                Contract.Invariant(cce.NonNullElements(interfaceExprVars));
            }

            public bool initialized;
            public int inline_cnt;
            public List<VCExprVar> interfaceExprVars;
            public VCExpr funcExpr;
            public VCExpr falseExpr;

            public StratifiedInliningInfo(Implementation impl, Program program, ProverContext ctxt, int uniqueid)
                : base(impl, program, ctxt, uniqueid, null)
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
                Contract.Assert(!impl.Name.StartsWith(recordProcName), "Not allowed to have an implementation for this guy");

                Procedure proc = cce.NonNull(impl.Proc);
                if (proc.FindExprAttribute("inline") != null)
                {
                    StratifiedInliningInfo info = new StratifiedInliningInfo(impl, program, checker.TheoremProver.Context, QuantifierExpr.GetNextSkolemId());
                    implName2StratifiedInliningInfo[impl.Name] = info;

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

            foreach (var decl in program.TopLevelDeclarations)
            {
                var proc = decl as Procedure;
                if (proc == null) continue;
                if (!proc.Name.StartsWith(recordProcName)) continue;
                Contract.Assert(proc.InParams.Length == 1);

                // Make a new function
                TypedIdent ti = new TypedIdent(Token.NoToken, "", Bpl.Type.Bool);
                Contract.Assert(ti != null);
                Formal returnVar = new Formal(Token.NoToken, ti, false);
                Contract.Assert(returnVar != null);

                // Get record type
                var argtype = proc.InParams[0].TypedIdent.Type;

                var ins = new VariableSeq();
                ins.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "x", argtype), true));

                var recordFunc = new Function(Token.NoToken, proc.Name, ins, returnVar);
                checker.TheoremProver.Context.DeclareFunction(recordFunc, "");

                var exprs = new ExprSeq();
                exprs.Add(new IdentifierExpr(Token.NoToken, proc.InParams[0]));

                Expr freePostExpr = new NAryExpr(Token.NoToken, new FunctionCall(recordFunc), exprs);
                proc.Ensures.Add(new Ensures(true, freePostExpr));
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

            var ctx = checker.TheoremProver.Context;
            var exprGen = ctx.ExprGen;
            var bet = ctx.BoogieExprTranslator;
            VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : bet.LookupVariable(info.controlFlowVariable);

            VCExpr vcexpr = gen.Not(GenerateVC(impl, controlFlowVariableExpr, out label2absy, checker));
            Contract.Assert(vcexpr != null);
            if (!CommandLineOptions.Clo.UseLabels) {
              VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(controlFlowVariableExpr, exprGen.Integer(BigNum.ZERO));
              VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
              vcexpr = exprGen.And(eqExpr, vcexpr);
            }
          
            info.label2absy = label2absy;
            info.mvInfo = mvInfo;

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

        public Dictionary<string, List<VCExprVar>> interfaceVarCopies;
        public Dictionary<string, List<VCExprVar>> privateVarCopies;
        Dictionary<string, VCExpr> procVcCopies;

        public struct CallSite {
          public string callerName;
          public string calleeName;
          public VCExprVar callSiteConstant;
          public VCExprNAry callExpr;

          public CallSite(string callerName, string calleeName, VCExprVar callSiteConstant, VCExprNAry callExpr) {
            this.callerName = callerName;
            this.calleeName = calleeName;
            this.callSiteConstant = callSiteConstant;
            this.callExpr = callExpr;
          }
        };

        static public int callSiteConstantCount = 0;
        Dictionary<string, List<CallSite>> calleeToCallSites;
        Dictionary<string, List<CallSite>> callerToCallSites;

        private void CreateProcedureCopies(Implementation impl, Program program, StratifiedCheckerInterface checker, VCExpr vcMain) {
          interfaceVarCopies = new Dictionary<string, List<VCExprVar>>();
          privateVarCopies = new Dictionary<string, List<VCExprVar>>();
          procVcCopies = new Dictionary<string, VCExpr>();
          calleeToCallSites = new Dictionary<string, List<CallSite>>();
          callerToCallSites = new Dictionary<string, List<CallSite>>();

          interfaceVarCopies[impl.Name] = new List<VCExprVar>();
          privateVarCopies[impl.Name] = new List<VCExprVar>();
          calleeToCallSites[impl.Name] = new List<CallSite>();
          callerToCallSites[impl.Name] = new List<CallSite>();
          foreach (var info in implName2StratifiedInliningInfo.Values) {
            Contract.Assert(info != null);
            interfaceVarCopies[info.impl.Name] = new List<VCExprVar>();
            privateVarCopies[info.impl.Name] = new List<VCExprVar>();
            calleeToCallSites[info.impl.Name] = new List<CallSite>();
            callerToCallSites[info.impl.Name] = new List<CallSite>();
            CreateProcedureCopy(info, checker);
          }

          BoundingVCMutator bm = new BoundingVCMutator(checker, impl.Name, interfaceVarCopies, calleeToCallSites, callerToCallSites);
          procVcCopies[impl.Name] = bm.Mutate(vcMain, true);
          foreach (var key in implName2StratifiedInliningInfo.Keys) {
            bm = new BoundingVCMutator(checker, key, interfaceVarCopies, calleeToCallSites, callerToCallSites);
            procVcCopies[key] = bm.Mutate(procVcCopies[key], true);
          }
        }

        // Return i if (prefix::i) is in labels
        public static int pcbFindLabel(IList<string> labels, string prefix)
        {
            foreach (var s in labels)
            {
                if (s.StartsWith(prefix))
                {
                    return Int32.Parse(s.Substring(prefix.Length));
                }
            }
            Contract.Assert(false);
            return -1;
        }

        public class SummaryComputation
        {
            // The verification state
            VerificationState vState;
            // The call tree
            FCallHandler calls;
            // Fully-inlined guys we have already queried
            HashSet<string> fullyInlinedCache;

            // The summary: boolean guards that are true
            HashSet<VCExprVar> trueSummaryConst;
            HashSet<VCExprVar> trueSummaryConstUndeBound;

            // Compute summaries under recursion bound or not?
            bool ComputeUnderBound;

            public SummaryComputation(VerificationState vState, bool ComputeUnderBound)
            {
                this.vState = vState;
                this.calls = vState.calls;
                this.fullyInlinedCache = new HashSet<string>();
                this.trueSummaryConst = new HashSet<VCExprVar>();
                this.trueSummaryConstUndeBound = new HashSet<VCExprVar>();
                this.ComputeUnderBound = false;
            }

            public void boundChanged()
            {
                if (ComputeUnderBound)
                {
                    var s = "";
                    trueSummaryConstUndeBound.Iter(v => s = s + v.ToString() + ",");
                    Console.WriteLine("Clearing summaries: {0}", s);

                    // start from scratch
                    trueSummaryConst.ExceptWith(trueSummaryConstUndeBound);
                    trueSummaryConstUndeBound = new HashSet<VCExprVar>();
                }
            }

            public void compute(HashSet<int> goodCandidates, int bound)
            {
                var start = DateTime.UtcNow;
                goodCandidates = calls.currCandidates;

                var found = 0;

                // Find all nodes that have children only in goodCandidates
                var overApproxNodes = FindNodes(calls.candidateParent, calls.currCandidates, goodCandidates);
                overApproxNodes.IntersectWith(calls.summaryCandidates.Keys);
                
                var roots = FindTopMostAncestors(calls.candidateParent, overApproxNodes);
                var checker2 = vState.checker2;

                checker2.Push();

                // candidates to block
                var block = new HashSet<int>();
                var usesBound = new HashSet<int>();
                if (ComputeUnderBound)
                {
                    calls.currCandidates.Iter(id => { if (calls.getRecursionBound(id) > bound) block.Add(id); });
                    foreach (var id in block)
                    {
                        checker2.AddAxiom(calls.getFalseExpr(id));
                        var curr = id;
                        usesBound.Add(id);
                        while (curr != 0)
                        {
                            curr = calls.candidateParent[curr];
                            usesBound.Add(curr);
                        }
                    }

                }
                
                // Iterate over the roots
                foreach (var id in roots)
                {
                    // inline procedures in post order
                    var post = getPostOrder(calls.candidateParent, id);

                    vState.checker2.Push();
                    foreach (var cid in post)
                    {
                        if (goodCandidates.Contains(cid)) continue;

                        checker2.AddAxiom(calls.id2VC[cid]);
                        if (!overApproxNodes.Contains(cid)) continue;
                        checker2.AddAxiom(calls.id2ControlVar[cid]);

                        foreach (var tup in calls.summaryCandidates[cid])
                        {
                            if (trueSummaryConst.Contains(tup.Item1)) continue;

                            //Console.WriteLine("Going to try ({0} ==> {1}) on {2}", tup.Item1, tup.Item2, id);
                            //Console.WriteLine("Call expr: {0}", calls.id2Candidate[id]);
                            
                            // It is OK to assume the summary while trying to prove it
                            var summary = getSummary(tup.Item1);

                            checker2.Push();
                            checker2.AddAxiom(summary);
                            checker2.AddAxiom(checker2.underlyingChecker.VCExprGen.Not(tup.Item2));
                            var outcome = checker2.CheckVC();
                            checker2.Pop();
                            if (outcome == Outcome.Correct)
                            {
                                //Console.WriteLine("Found summary: {0}", tup.Item1);
                                found++;
                                trueSummaryConst.Add(tup.Item1);
                                if (usesBound.Contains(cid)) trueSummaryConstUndeBound.Add(tup.Item1);
                            }
                        }
                    }
                    checker2.Pop();
                }
                checker2.Pop();

                var end = DateTime.UtcNow;
                Console.WriteLine("Summary computation took {0} sec and inferred {1} of {2} contracts", 
                    (end - start).TotalSeconds, found, calls.allSummaryConst.Count);

            }


            public VCExpr getSummary()
            {
                return getSummary(new HashSet<VCExprVar>());
            }

            public VCExpr getSummary(params VCExprVar[] p)
            {
                var s = new HashSet<VCExprVar>();
                p.Iter(v => s.Add(v));
                return getSummary(s);
            }

            public VCExpr getSummary(HashSet<VCExprVar> extraToSet)
            {
                if (calls.allSummaryConst.Count == 0) return null;
                // TODO: does it matter which checker we use here?
                var Gen = vState.checker.underlyingChecker.VCExprGen;

                var ret = VCExpressionGenerator.True;
                foreach (var c in calls.allSummaryConst)
                {
                    if (trueSummaryConst.Contains(c) || extraToSet.Contains(c))
                    {
                        ret = Gen.And(ret, c);
                    }
                    else
                    {
                        ret = Gen.And(ret, Gen.Not(c));
                    }
                }
                return ret;
            }

            // Return a subset of nodes such that all other nodes are their decendent
            private HashSet<int> FindTopMostAncestors(Dictionary<int, int> parents, HashSet<int> nodes)
            {
                var ret = new HashSet<int>();
                //var ancestorFound = new HashSet<int>();
                foreach (var n in nodes)
                {
                    var ancestor = n;
                    var curr = n;
                    while (curr != 0)
                    {
                        curr = parents[curr];
                        if (nodes.Contains(curr)) ancestor = curr;
                    }
                    ret.Add(ancestor);
                }
                return ret;
            }

            // Returns the set of candidates whose child leaves are all "good". Remove fully inlined ones.
            HashSet<int> FindNodes(Dictionary<int, int> parents, HashSet<int> allLeaves,
                HashSet<int> goodLeaves)
            {
                var ret = new HashSet<int>();
                var leaves = new Dictionary<int, HashSet<int>>();
                leaves.Add(0, new HashSet<int>());
                parents.Keys.Iter(n => leaves.Add(n, new HashSet<int>()));
                allLeaves.Iter(l => leaves[l].Add(l));

                foreach (var l in allLeaves)
                {
                    var curr = l;
                    leaves[curr].Add(l);
                    while (parents.ContainsKey(curr))
                    {
                        curr = parents[curr];
                        leaves[curr].Add(l);
                    }
                }

                foreach (var kvp in leaves)
                {
                    if (kvp.Value.Count == 0)
                    {
                        var proc = calls.getProc(kvp.Key);
                        if (fullyInlinedCache.Contains(proc)) continue;
                        else
                        {
                            ret.Add(kvp.Key);
                            fullyInlinedCache.Add(proc);
                        }
                    }

                    if (kvp.Value.IsSubsetOf(goodLeaves))
                    {
                        ret.Add(kvp.Key);
                    }
                }

                return ret;
            }


            // returns children of root in post order
            static List<int> getPostOrder(Dictionary<int, int> parents, int root)
            {
                var children = new Dictionary<int, HashSet<int>>();
                foreach (var id in parents.Keys) children.Add(id, new HashSet<int>());
                children.Add(0, new HashSet<int>());
                foreach (var kvp in parents) children[kvp.Value].Add(kvp.Key);
                return getPostOrder(children, root);
            }
            static List<int> getPostOrder(Dictionary<int, HashSet<int>> children, int root)
            {
                var ret = new List<int>();
                foreach (var ch in children[root]) ret.AddRange(getPostOrder(children, ch));
                ret.Add(root);
                return ret;
            }

        }

        public class BoundingVCMutator : MutatingVCExprVisitor<bool> {
          StratifiedCheckerInterface checker;
          string implName;
          Dictionary<string, List<VCExprVar>> interfaceVarCopies;
          Dictionary<string, List<CallSite>> calleeToCallSites;
          Dictionary<string, List<CallSite>> callerToCallSites;

          public BoundingVCMutator(
              StratifiedCheckerInterface checker,
              string implName,
              Dictionary<string, List<VCExprVar>> interfaceVarCopies,
              Dictionary<string, List<CallSite>> calleeToCallSites,
              Dictionary<string, List<CallSite>> callerToCallSites)
            : base(checker.underlyingChecker.VCExprGen) {
            this.checker = checker;
            this.implName = implName;
            this.interfaceVarCopies = interfaceVarCopies;
            this.calleeToCallSites = calleeToCallSites;
            this.callerToCallSites = callerToCallSites;
          }

          protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode,
                                                        List<VCExpr/*!*/>/*!*/ newSubExprs,
                                                        bool changed,
                                                        bool arg) {
            Contract.Ensures(Contract.Result<VCExpr>() != null);

            VCExpr node;
            if (changed)
              node = Gen.Function(originalNode.Op, newSubExprs, originalNode.TypeArguments);
            else
              node = originalNode;

            VCExprLabelOp lop = originalNode.Op as VCExprLabelOp;
            if (lop == null) return node;

            string prefix = "si_fcall_"; // from Wlp.ssc::Cmd(...)
            if (!lop.label.Substring(1).StartsWith(prefix)) return node;

            VCExprNAry retnary = node as VCExprNAry;
            Debug.Assert(retnary != null);

            VCExprNAry callExpr = retnary[0] as VCExprNAry;
            Debug.Assert(callExpr != null);

            VCExprBoogieFunctionOp op = callExpr.Op as VCExprBoogieFunctionOp;
            if (op == null) return callExpr;

            if (!interfaceVarCopies.ContainsKey(op.Func.Name)) return callExpr;

            var constName = "pcb_callsite_constant_" + StratifiedVCGen.callSiteConstantCount++;
            var constant = Gen.Variable(constName, Bpl.Type.Bool);
            checker.underlyingChecker.TheoremProver.Context.DeclareConstant(new Constant(Token.NoToken, new TypedIdent(Token.NoToken, constName, Bpl.Type.Bool)), false, null);
            CallSite cs = new CallSite(implName, op.Func.Name, constant, callExpr);
            calleeToCallSites[op.Func.Name].Add(cs);
            callerToCallSites[implName].Add(cs);

            var iv = interfaceVarCopies[op.Func.Name];
            Contract.Assert(op.Arity == iv.Count);

            VCExpr conj = VCExpressionGenerator.True;
            for (int i = 0; i < iv.Count; i++) {
              var c = Gen.Eq(callExpr[i], iv[i]);
              conj = Gen.And(conj, c);
            }

            return Gen.Implies(constant, conj);
          }

        } // end BoundingVCMutator

        private void CreateProcedureCopy(StratifiedInliningInfo info, StratifiedCheckerInterface checker) {
          var translator = checker.underlyingChecker.TheoremProver.Context.BoogieExprTranslator;
          var Gen = checker.underlyingChecker.VCExprGen;
          var expr = info.vcexpr;
          
          // Instantiate the interface variables
          Dictionary<VCExprVar, VCExpr> substForallDict = new Dictionary<VCExprVar, VCExpr>();
          for (int i = 0; i < info.interfaceExprVars.Count; i++) {
            var v = info.interfaceExprVars[i];
            string newName = v.Name + "_iv_" + newVarCnt.ToString();
            newVarCnt++;
            var vp = Gen.Variable(newName, v.Type);
            substForallDict.Add(v, vp);
            interfaceVarCopies[info.impl.Name].Add(vp);
          }
          VCExprSubstitution substForall = new VCExprSubstitution(substForallDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
          SubstitutingVCExprVisitor subst = new SubstitutingVCExprVisitor(Gen);
          Contract.Assert(subst != null);
          expr = subst.Mutate(expr, substForall);

          // Instantiate and declare the private variables
          Dictionary<VCExprVar, VCExpr> substExistsDict = new Dictionary<VCExprVar, VCExpr>();
          foreach (VCExprVar v in info.privateVars) {
            Contract.Assert(v != null);
            string newName = v.Name + "_pv_" + newVarCnt.ToString();
            newVarCnt++;
            checker.underlyingChecker.TheoremProver.Context.DeclareConstant(new Constant(Token.NoToken, new TypedIdent(Token.NoToken, newName, v.Type)), false, null);
            var vp = Gen.Variable(newName, v.Type);
            substExistsDict.Add(v, vp);
            privateVarCopies[info.impl.Name].Add(vp);
          }
          VCExprSubstitution substExists = new VCExprSubstitution(substExistsDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
          subst = new SubstitutingVCExprVisitor(Gen);
          expr = subst.Mutate(expr, substExists);

          procVcCopies[info.impl.Name] = expr;
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
            abstract public void updateMainVC(VCExpr vcMain);
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
            virtual public void SetTimeOut(int msec)
            {
                // default behavior is to ignore this timeout
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

            public override void updateMainVC(VCExpr vcMain)
            {
                this.vcMain = vcMain;
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


        public class ApiChecker : StratifiedCheckerInterface {
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

          public ApiChecker(VCExpr vcMain, ProverInterface.ErrorHandler reporter, Checker checker) {
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

          public override void updateMainVC(VCExpr vcMain) {
            throw new NotImplementedException("Stratified non-incremental search is not yet supported with z3api");
          }

          public override Outcome CheckVC() {
            Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

            TheoremProver.AssertAxioms();
            TheoremProver.Check();
            ProverInterface.Outcome outcome = TheoremProver.CheckOutcome(reporter);
            numQueries++;

            switch (outcome) {
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

          public override void Push() {
            TheoremProver.Push();
          }

          public override void Pop() {
            TheoremProver.AssertAxioms();
            TheoremProver.Pop();
          }

          public override void AddAxiom(VCExpr vc) {
            TheoremProver.Assert(vc, true);
          }

          public override void LogComment(string str) {
            checker.TheoremProver.LogComment(str);
          }

          public override Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore) {
            if (!UseCheckAssumptions) {
              return base.CheckAssumptions(assumptions, out unsatCore);
            }
            
            if (assumptions.Count == 0) {
              unsatCore = new List<int>();
              return CheckVC();
            }

            //TheoremProver.Push();
            TheoremProver.AssertAxioms();
            TheoremProver.CheckAssumptions(assumptions, out unsatCore);
            ProverInterface.Outcome outcome = TheoremProver.CheckOutcome(reporter);
            //TheoremProver.Pop();
            numQueries++;

            switch (outcome) {
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

          public override void SetTimeOut(int msec)
          {
              TheoremProver.SetTimeOut(msec);
          }
        }

        // Store important information related to a single VerifyImplementation query
        public class VerificationState
        {
            // The VC of main
            public VCExpr vcMain { get; private set; }
            // The call tree
            public FCallHandler calls;
            // Error reporter (stores models)
            public ProverInterface.ErrorHandler reporter;
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
            // For making summary queries on the side
            public StratifiedCheckerInterface checker2;

            public VerificationState(VCExpr vcMain, FCallHandler calls,
                ProverInterface.ErrorHandler reporter, Checker checker, Checker checker2)
            {
                this.vcMain = vcMain;
                this.calls = calls;
                this.reporter = reporter;
                if (checker.TheoremProver is ApiProverInterface)
                {
                    this.checker = new ApiChecker(vcMain, reporter , checker);
                    if(checker2 != null)
                      this.checker2 = new ApiChecker(VCExpressionGenerator.False, new EmptyErrorHandler(), checker2); 
                }
                else
                {
                    this.checker = new NormalChecker(vcMain, reporter, checker);
                    if(checker2 != null)
                      this.checker2 = new NormalChecker(VCExpressionGenerator.False, new EmptyErrorHandler(), checker2); 
                }
                vcSize = 0;
                expansionCount = 0;
                
            }

            public void updateMainVC(VCExpr vcMain)
            {
                this.vcMain = vcMain;
                checker.updateMainVC(vcMain);
            }
        }

        public Outcome FindLeastToVerify(Implementation impl, Program program, ref HashSet<string> allBoolVars)
        {
            Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

            // Record current time
            var startTime = DateTime.UtcNow;

            // No Max: avoids theorem prover restarts
            CommandLineOptions.Clo.MaxProverMemory = 0;

            // Initialize cache
            satQueryCache = new Dictionary<int, List<HashSet<string>>>();
            unsatQueryCache = new Dictionary<int, List<HashSet<string>>>();

            // Get the checker
            Checker checker = FindCheckerFor(impl, CommandLineOptions.Clo.ProverKillTime); Contract.Assert(checker != null);

            Contract.Assert(implName2StratifiedInliningInfo != null);
            this.program = program;

            // Build VCs for all procedures
            foreach (StratifiedInliningInfo info in implName2StratifiedInliningInfo.Values)
            {
                Contract.Assert(info != null);
                GenerateVCForStratifiedInlining(program, info, checker);
            }

            // Get the VC of the current procedure
            VCExpr vcMain;
            Hashtable/*<int, Absy!>*/ mainLabel2absy;
            ModelViewInfo mvInfo;

            ConvertCFG2DAG(impl, program);
            Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = PassifyImpl(impl, program, out mvInfo);
            var exprGen = checker.TheoremProver.Context.ExprGen;
            VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : exprGen.Integer(BigNum.ZERO); 
            vcMain = GenerateVC(impl, null, out mainLabel2absy, checker);
            if (!CommandLineOptions.Clo.UseLabels) {
              VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
              VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
              vcMain = exprGen.Implies(eqExpr, vcMain);
            }

            // Find all procedure calls in vc and put labels on them      
            FCallHandler calls = new FCallHandler(checker.VCExprGen, implName2StratifiedInliningInfo, impl.Name, mainLabel2absy);
            calls.setCurrProcAsMain();
            vcMain = calls.Mutate(vcMain, true);

            // Put all of the necessary state into one object
            var vState = new VerificationState(vcMain, calls, new EmptyErrorHandler(), checker, null);
            vState.coverageManager = null;

            // We'll restore the original state of the theorem prover at the end
            // of this procedure
            vState.checker.Push();

            // Do eager inlining
            while (calls.currCandidates.Count > 0)
            {
                List<int> toExpand = new List<int>();

                foreach (int id in calls.currCandidates)
                {
                    Debug.Assert(calls.getRecursionBound(id) <= 1, "Recursion not supported");
                    toExpand.Add(id);
                }
                DoExpansion(true, toExpand, vState);
            }

            // Find all the boolean constants
            var allConsts = new HashSet<VCExprVar>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                var constant = decl as Constant;
                if (constant == null) continue;
                if (!allBoolVars.Contains(constant.Name)) continue;
                var v = checker.TheoremProver.Context.BoogieExprTranslator.LookupVariable(constant);
                allConsts.Add(v);
            }

            // Now, lets start the algo
            var min = refinementLoop(vState.checker, new HashSet<VCExprVar>(), allConsts, allConsts);

            var ret = new HashSet<string>();
            foreach (var v in min)
            {
                //Console.WriteLine(v.Name);
                ret.Add(v.Name);
            }
            allBoolVars = ret;

            vState.checker.Pop();

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

        Dictionary<int, List<HashSet<string>>> satQueryCache;
        Dictionary<int, List<HashSet<string>>> unsatQueryCache;

        private bool refinementLoopCheckPath(StratifiedCheckerInterface apiChecker, HashSet<VCExprVar> varsToSet, HashSet<VCExprVar> allVars)
        {
            var assumptions = new List<VCExpr>();
            List<int> temp = null;

            var query = new HashSet<string>();
            varsToSet.Iter(v => query.Add(v.Name));

            if (checkCache(query, unsatQueryCache))
            {
                apiChecker.LogComment("FindLeast: Query Cache Hit");
                return true;
            }
            if (checkCache(query, satQueryCache))
            {
                apiChecker.LogComment("FindLeast: Query Cache Hit");
                return false;
            }


            apiChecker.LogComment("FindLeast: Query Begin");

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
            apiChecker.LogComment("FindLeast: Query End");

            if (o == Outcome.Correct)
            {
                insertCache(query, unsatQueryCache);
                return true;
            }

            insertCache(query, satQueryCache);
            return false;
        }

        private bool checkCache(HashSet<string> q, Dictionary<int, List<HashSet<string>>> cache)
        {
            if (!cache.ContainsKey(q.Count)) return false;
            foreach (var s in cache[q.Count])
            {
                if (q.SetEquals(s)) return true;
            }
            return false;
        }

        private void insertCache(HashSet<string> q, Dictionary<int, List<HashSet<string>>> cache)
        {
            if (!cache.ContainsKey(q.Count))
            {
                cache.Add(q.Count, new List<HashSet<string>>());
            }
            cache[q.Count].Add(q);
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
            var computeUnderBound = true;

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
                case 6:
                    incrementalSearch = true;
                    createVConDemand = true;
                    useSummary = true;
                    break;
                case 7:
                    incrementalSearch = true;
                    createVConDemand = true;
                    useSummary = true;
                    computeUnderBound = false;
                    break;
            }

            #endregion

            // Get the checker
            Checker checker = FindCheckerFor(null, CommandLineOptions.Clo.ProverKillTime); Contract.Assert(checker != null);
            Checker checker2 = null;
            if (useSummary)
            {
                
                checker2 = new Checker(this, program, "checker2.txt", true, CommandLineOptions.Clo.ProverKillTime);
            }

            // Record current time
            var startTime = DateTime.UtcNow;

            // Run live variable analysis
            if (CommandLineOptions.Clo.LiveVariableAnalysis == 2)
            {
                Microsoft.Boogie.InterProcGenKill.ComputeLiveVars(impl, program);
            }

            // Build VCs for all procedures
            Contract.Assert(implName2StratifiedInliningInfo != null);
            this.program = program;

            if (!createVConDemand || CommandLineOptions.Clo.ProcedureCopyBound > 0)
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
            calls.id2VC.Add(0, vc);

            // Identify summary candidates: Match ensure clauses with the appropriate call site
            if (useSummary) calls.matchSummaries();
            

            // create a process for displaying coverage information
            var coverageManager = new CoverageGraphManager(calls);
            coverageManager.addMain();

            // Put all of the necessary state into one object
            var vState = new VerificationState(vc, calls, reporter, checker, checker2);
            vState.vcSize += SizeComputingVisitor.ComputeSize(vc);
            vState.coverageManager = coverageManager;

            if (useSummary) summaryComputation = new SummaryComputation(vState, computeUnderBound);

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
                    else {
                      DoExpansion(incrementalSearch, toExpand, vState);
                    }
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

            int iters = 0;

            // for blocking candidates (and focussing on a counterexample)
            var block = new HashSet<int>();

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
                    if ((DateTime.UtcNow - startTime).TotalSeconds > CommandLineOptions.Clo.ProverKillTime)
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

                    VCExpr summary = null;
                    if (useSummary) summary = summaryComputation.getSummary();

                    if (useSummary && summary != null)
                    {
                        vState.checker.Push();
                        vState.checker.AddAxiom(summary);
                    }

                    // Stratified Step
                    ret = stratifiedStep(bound, vState, block);
                    iters++;

                    if (useSummary && summary != null)
                    {
                        vState.checker.Pop();
                    }

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
                        if (block.Count == 0)
                        {
                            // Correct
                            done = 1;
                            coverageManager.reportCorrect();
                        }
                        else
                        {
                            Contract.Assert(useSummary);
                            // reset blocked and continue loop
                            block.Clear();
                        }
                    }
                    else if (ret == Outcome.ReachedBound)
                    {
                        if (block.Count == 0)
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
                            if (useSummary) summaryComputation.boundChanged();

                            if (bound > CommandLineOptions.Clo.RecursionBound)
                            {
                                // Correct under bound
                                done = 1;
                                coverageManager.reportCorrect(bound);
                            }
                        }
                        else
                        {
                            Contract.Assert(useSummary);
                            // reset blocked and continue loop
                            block.Clear();
                        }
                    }
                    else
                    {
                        // Do inlining
                        Debug.Assert(ret == Outcome.Errors && !reporter.underapproximationMode);
                        Contract.Assert(reporter.candidatesToExpand.Count != 0);
                        if (useSummary)
                        {
                            // compute candidates to block  
                            block = new HashSet<int>(calls.currCandidates);
                            block.ExceptWith(reporter.candidatesToExpand);
                        }

                        #region expand call tree
                        if (CommandLineOptions.Clo.StratifiedInliningVerbose > 0)
                        {
                            Console.Write(">> SI Inlining: ");
                            reporter.candidatesToExpand.ForEach(c => Console.Write("{0} ", calls.getProc(c)));
                            Console.WriteLine();
                        }
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

            numInlined = (calls.candidateParent.Keys.Count + 1) - (calls.currCandidates.Count);

            var rbound = "Procs that reached bound: ";
            foreach (var s in procsThatReachedRecBound) rbound += "  " + s;
            if(ret == Outcome.ReachedBound) Helpers.ExtraTraceInformation(rbound);

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
            if (checker2 != null) checker2.Close();
            return ret;
        }

        public class PCBInliner : MutatingVCExprVisitor<bool> {
          private VCExprVar callSiteConstant;
          private VCExpr expr;

          public PCBInliner(VCExpressionGenerator gen, VCExprVar callSiteConstant, VCExpr expr)
            : base(gen) {
            Contract.Requires(gen != null);
            this.callSiteConstant = callSiteConstant;
            this.expr = expr;
          }

          protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode,
                                                        List<VCExpr/*!*/>/*!*/ newSubExprs,
                                                        bool changed,
                                                        bool arg) {
            Contract.Ensures(Contract.Result<VCExpr>() != null);

            VCExpr ret;
            if (changed)
              ret = Gen.Function(originalNode.Op, newSubExprs, originalNode.TypeArguments);
            else
              ret = originalNode;

            VCExprNAry naryExpr = ret as VCExprNAry;
            if (naryExpr == null) return ret;
            if (naryExpr.Op != VCExpressionGenerator.ImpliesOp) return ret;
            if (naryExpr[0] != callSiteConstant) return ret;
            return expr;
          }

        } // end PCBInliner

        private void InlineCallSite(CallSite cs, StratifiedCheckerInterface checker) {
          var Gen = checker.underlyingChecker.VCExprGen;
          var callee = cs.calleeName;
          var caller = cs.callerName;
          Helpers.ExtraTraceInformation("inlining call from " + caller + "to " + callee);
          var expr = cs.callExpr;
          VCExpr expansion = procVcCopies[callee];
          List<VCExprVar> interfaceExprVars = interfaceVarCopies[callee];
          List<VCExprVar> privateVars = privateVarCopies[callee];

          // Instantiate the "forall" variables
          Dictionary<VCExprVar, VCExpr> substForallDict = new Dictionary<VCExprVar, VCExpr>();
          Contract.Assert(interfaceExprVars.Count == expr.Length);
          for (int i = 0; i < interfaceExprVars.Count; i++) {
            substForallDict.Add(interfaceExprVars[i], expr[i]);
          }
          VCExprSubstitution substForall = new VCExprSubstitution(substForallDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
          SubstitutingVCExprVisitor subst = new SubstitutingVCExprVisitor(Gen); 
          expansion = subst.Mutate(expansion, substForall);

          // Instantiate and declare the "exists" variables
          Dictionary<VCExprVar, VCExpr> substExistsDict = new Dictionary<VCExprVar, VCExpr>();
          for (int i = 0; i < privateVars.Count; i++) {
            VCExprVar v = privateVars[i];
            string newName = v.Name + "_si_" + newVarCnt.ToString();
            newVarCnt++;
            checker.underlyingChecker.TheoremProver.Context.DeclareConstant(new Constant(Token.NoToken, new TypedIdent(Token.NoToken, newName, v.Type)), false, null);
            var vp = Gen.Variable(newName, v.Type);
            substExistsDict.Add(v, vp);
            privateVarCopies[cs.callerName].Add(vp);
          }
          VCExprSubstitution substExists = new VCExprSubstitution(substExistsDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
          subst = new SubstitutingVCExprVisitor(Gen);
          expansion = subst.Mutate(expansion, substExists);

          Dictionary<VCExprVar, VCExpr> substCallSiteConstantDict = new Dictionary<VCExprVar, VCExpr>();
          foreach (CallSite oldSite in callerToCallSites[callee]) {
            var newConstName = "pcb_callsite_constant_" + StratifiedVCGen.callSiteConstantCount++;
            var newConstant = Gen.Variable(newConstName, Bpl.Type.Bool);
            checker.underlyingChecker.TheoremProver.Context.DeclareConstant(new Constant(Token.NoToken, new TypedIdent(Token.NoToken, newConstName, Bpl.Type.Bool)), false, null);
            substCallSiteConstantDict.Add(oldSite.callSiteConstant, newConstant);
            subst = new SubstitutingVCExprVisitor(Gen);
            var newCallExpr = subst.Mutate(oldSite.callExpr, substForall);
            subst = new SubstitutingVCExprVisitor(Gen);
            newCallExpr = subst.Mutate(newCallExpr, substExists);
            var newSite = new CallSite(caller, oldSite.calleeName, newConstant, (VCExprNAry)newCallExpr);
            callerToCallSites[caller].Add(newSite);
            calleeToCallSites[oldSite.calleeName].Add(newSite);
          }
          VCExprSubstitution substCallSiteConstant = new VCExprSubstitution(substCallSiteConstantDict, new Dictionary<TypeVariable, Microsoft.Boogie.Type>());
          subst = new SubstitutingVCExprVisitor(Gen);
          expansion = subst.Mutate(expansion, substCallSiteConstant);

          PCBInliner inliner = new PCBInliner(Gen, cs.callSiteConstant, expansion);
          procVcCopies[cs.callerName] = inliner.Mutate(procVcCopies[cs.callerName], true);

          callerToCallSites[caller].Remove(cs);
          calleeToCallSites[callee].Remove(cs);
        }

        private Outcome FindUnsatCoreInMainCallees(Implementation impl, StratifiedCheckerInterface checker, VCExpressionGenerator Gen, PCBErrorReporter reporter, List<VCExpr> assumptions, out HashSet<VCExprVar> unsatCore) {
          Debug.Assert(checker is ApiChecker);
          unsatCore = null;
          List<int> unsatCoreIndices;
          Outcome ret;
          ret = checker.CheckAssumptions(assumptions, out unsatCoreIndices);
          if (ret == Outcome.Errors) return ret;
          unsatCore = new HashSet<VCExprVar>();
          HashSet<VCExprVar> implCallees = new HashSet<VCExprVar>();
          foreach (CallSite cs in callerToCallSites[impl.Name]) {
            implCallees.Add(cs.callSiteConstant);
          }
          for (int i = 0; i < unsatCoreIndices.Count; i++) {
            VCExprVar assumption = (VCExprVar)assumptions[unsatCoreIndices[i]];
            if (implCallees.Contains(assumption)) {
              unsatCore.Add(assumption);
            }
          }
          return Outcome.Correct;
        }

        private Outcome FindUnsatCore(Implementation impl, StratifiedCheckerInterface checker, VCExpressionGenerator Gen, PCBErrorReporter reporter, List<VCExpr> assumptions, out HashSet<VCExprVar> unsatCore) {
          Helpers.ExtraTraceInformation("Number of assumptions = " + assumptions.Count);
          unsatCore = null;
          List<int> unsatCoreIndices;
          Outcome ret;
          ret = checker.CheckAssumptions(assumptions, out unsatCoreIndices);
          if (ret == Outcome.Errors) return ret;
          unsatCore = new HashSet<VCExprVar>();
          for (int i = 0; i < unsatCoreIndices.Count; i++) {
            unsatCore.Add((VCExprVar)assumptions[unsatCoreIndices[i]]);
          }

          Helpers.ExtraTraceInformation("Number of elements in unsat core = " + unsatCore.Count);

          HashSet<CallSite> reachableCallSites = new HashSet<CallSite>();
          Stack<string> stack = new Stack<string>();
          HashSet<string> set = new HashSet<string>();
          stack.Push(impl.Name);
          while (stack.Count > 0) {
            string caller = stack.Peek();
            stack.Pop();
            if (set.Contains(caller)) continue;
            set.Add(caller);
            foreach (CallSite cs in callerToCallSites[caller]) {
              if (unsatCore.Contains(cs.callSiteConstant)) {
                reachableCallSites.Add(cs);
                stack.Push(cs.calleeName);
              }
            }
          }

          Graph<CallSite> callGraph = new Graph<CallSite>();
          foreach (CallSite cs1 in reachableCallSites) {
            callGraph.AddSource(cs1);
            foreach (CallSite cs2 in calleeToCallSites[cs1.callerName]) {
              if (reachableCallSites.Contains(cs2)) {
                callGraph.AddEdge(cs1, cs2);
              }
            }
          }

          List<CallSite> sortedCallSites = new List<CallSite>();
          foreach (CallSite cs in callGraph.TopologicalSort()) {
            checker.Push();
            checker.AddAxiom(cs.callSiteConstant);
            sortedCallSites.Add(cs);
          }

          ret = checker.CheckVC();
          Debug.Assert(ret == Outcome.Correct);

          reporter.unsatCoreMode = true;
          VCExpr curr = VCExpressionGenerator.True;
          HashSet<CallSite> relevantCallSites = new HashSet<CallSite>();
          HashSet<VCExprVar> relevantUnsatCore = new HashSet<VCExprVar>();
          int index = sortedCallSites.Count;
          int queries = 0;
          while (index > 0) {
            checker.Pop();
            index--;
            CallSite cs = sortedCallSites[index];
            bool check = (cs.callerName == impl.Name);
            foreach (CallSite x in calleeToCallSites[cs.callerName]) {
              check = check || relevantCallSites.Contains(x);
            }
            if (!check) continue;
            bool relevant = (cs.callerName != impl.Name);
            foreach (CallSite x in calleeToCallSites[cs.calleeName]) {
              if (x.callSiteConstant == cs.callSiteConstant) continue;
              relevant = relevant && !reachableCallSites.Contains(x);
            }
            if (relevant) {
              curr = Gen.And(cs.callSiteConstant, curr);
              relevantCallSites.Add(cs);
              relevantUnsatCore.Add(cs.callSiteConstant);
              continue;
            }

            queries++;
            checker.Push();
            checker.AddAxiom(curr);
            ret = checker.CheckVC();
            checker.Pop();

            if (ret == Outcome.Errors || ret == Outcome.TimedOut) {
              curr = Gen.And(cs.callSiteConstant, curr);
              relevantCallSites.Add(cs);
              relevantUnsatCore.Add(cs.callSiteConstant);
            }
          }
          reporter.unsatCoreMode = false;

          unsatCore = relevantUnsatCore;
          Helpers.ExtraTraceInformation("Number of queries = " + queries);
          Helpers.ExtraTraceInformation("Unsat core after pruning = " + unsatCore.Count);
          return Outcome.Correct;
        }

        HashSet<string> ComputeReachableImplementations(Implementation impl) {
          Stack<string> stack = new Stack<string>();
          HashSet<string> set = new HashSet<string>();
          stack.Push(impl.Name);
          while (stack.Count > 0) {
            string caller = stack.Peek();
            stack.Pop();
            if (set.Contains(caller)) continue;
            set.Add(caller);
            foreach (CallSite cs in callerToCallSites[caller]) {
              stack.Push(cs.calleeName);
            }
          }
          return set;
        }

        private bool Verified(HashSet<VCExprVar> unsatCore) {
          bool verified = true;
          foreach (string name in calleeToCallSites.Keys) {
            int numInlined = 0;
            foreach (CallSite cs in calleeToCallSites[name]) {
              if (unsatCore.Contains(cs.callSiteConstant))
                numInlined++;
            }
            if (numInlined > 1) {
              Helpers.ExtraTraceInformation("callee name = " + name);
              Helpers.ExtraTraceInformation("number of inlines = " + numInlined);
              verified = false;
            }
          }
          return verified;
        }

        private void InlineBottomUp(StratifiedCheckerInterface checker, HashSet<VCExprVar> unsatCore) {
          Graph<string> callGraph = new Graph<string>();
          foreach (string name in calleeToCallSites.Keys) {
            callGraph.AddSource(name);
            foreach (CallSite cs in calleeToCallSites[name]) {
              callGraph.AddEdge(name, cs.callerName);
            }
          }
          foreach (string name in callGraph.TopologicalSort()) {
            HashSet<CallSite> toBeInlined = new HashSet<CallSite>();
            foreach (CallSite cs in calleeToCallSites[name]) {
              if (unsatCore.Contains(cs.callSiteConstant)) {
                Debug.Assert(name == cs.calleeName);
                toBeInlined.Add(cs);
              }
            }
            foreach (CallSite cs in toBeInlined) {
              InlineCallSite(cs, checker);
            }
          }
        }

        private void InlineIntoMain(StratifiedCheckerInterface checker, Implementation impl, HashSet<VCExprVar> unsatCore) {
          HashSet<CallSite> toBeInlined = new HashSet<CallSite>();
          foreach (CallSite cs in callerToCallSites[impl.Name]) {
            if (unsatCore.Contains(cs.callSiteConstant)) {
              toBeInlined.Add(cs);
            }
          }
          foreach (CallSite cs in toBeInlined) {
            InlineCallSite(cs, checker);
          }
        }

        private Outcome SuperAwesomeMethod(Checker underlyingChecker, Implementation impl, VCExpr vcMain) {
          // Create the call graph
          // while (true) 
          // 1. Create boolean variables for each call site
          // 2. Create the implications both at the top level and at the call sites
          // 3. Verify using CheckAssumptions
          // 4. Traverse call graph bottom up. For each procedure, inline all incoming edges in the unsatCore and update call graph
          // 5. If no node had more than one incoming edges set to true, break

          var Gen = underlyingChecker.VCExprGen;
          PCBErrorReporter reporter = new PCBErrorReporter(impl);
          StratifiedCheckerInterface checker;
          checker = new ApiChecker(VCExpressionGenerator.False, reporter, underlyingChecker);
          CreateProcedureCopies(impl, program, checker, vcMain);

          int iter = 0;
          while (true) {
            Helpers.ExtraTraceInformation("Iteration number " + iter++);
            Outcome ret;

            checker.Push();

            var reachableImpls = ComputeReachableImplementations(impl);
            var assumptions = new List<VCExpr>();
            foreach (string name in reachableImpls) {
              VCExpr expr = procVcCopies[name];
              if (name == impl.Name) {
                checker.AddAxiom(Gen.Not(expr));
                continue;
              }
              var cscExpr = VCExpressionGenerator.False;
              foreach (CallSite callSite in calleeToCallSites[name]) {
                if (reachableImpls.Contains(callSite.callerName)) {
                  assumptions.Add(callSite.callSiteConstant);
                  cscExpr = Gen.Or(callSite.callSiteConstant, cscExpr);
                }
              }
              expr = Gen.Implies(cscExpr, expr);
              checker.AddAxiom(expr);
            }
            HashSet<VCExprVar> unsatCore;
            ret = FindUnsatCore(impl, checker, Gen, reporter, assumptions, out unsatCore);
            
            checker.Pop();

            if (ret == Outcome.Errors) 
              return ret;

            if (Verified(unsatCore))
              return Outcome.Correct;

            //InlineBottomUp(checker, unsatCore);
            InlineIntoMain(checker, impl, unsatCore);
          }
        }

        

        // A step of the stratified inlining algorithm: both under-approx and over-approx queries
        private Outcome stratifiedStep(int bound, VerificationState vState, HashSet<int> block)
        {
            Outcome ret;
            List<int> unsatCore;

            // No need of computing Unsat cores for stratified inlining
            if (!CommandLineOptions.Clo.UseUnsatCoreForInlining && CommandLineOptions.Clo.ProverName == "SMTLIB") 
                ApiChecker.UseCheckAssumptions = false;

            var reporter = vState.reporter as StratifiedInliningErrorReporter;
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

            if (ret != Outcome.Correct)
            {
                // The query ran out of memory or time, that's it,
                // we cannot do better. Give up!
                return ret;
            }

            // If we didn't underapproximate, then we're done
            if (calls.currCandidates.Count == 0)
            {
                return ret;
            }

            checker.LogComment(";;;;;;;;;;;; Overapprox mode begin ;;;;;;;;;;");

            // Over-approx query
            reporter.underapproximationMode = false;

            // Push "true" for all, except:
            // push "false" for all candidates that have reached
            // the recursion bounds

            bool allTrue = true;
            bool allFalse = true;

            assumptions = new List<VCExpr>();
            procsThatReachedRecBound.Clear();

            foreach (int id in calls.currCandidates)
            {
                if (calls.getRecursionBound(id) <= bound)
                {
                    if (block.Contains(id))
                    {
                        Contract.Assert(useSummary);
                        //checker.AddAxiom(calls.getFalseExpr(id));
                        assumptions.Add(calls.getFalseExpr(id));
                        allTrue = false;
                    }
                    else
                    {
                        //checker.TheoremProver.PushVCExpression(calls.getTrueExpr(id));
                        allFalse = false;
                    }
                }
                else
                {
                    procsThatReachedRecBound.Add(calls.getProc(id));
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

                if (useSummary)
                {
                    // Find the set of candidates with valid over-approximations
                    var assumeTrueCandidates = new HashSet<int>(vState.calls.currCandidates);
                    assumeTrueCandidates.ExceptWith(block);
                    summaryComputation.compute(assumeTrueCandidates, bound);
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
        private void DoExpansion(bool incremental, List<int>/*!*/ candidates, VerificationState vState) {
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
                
                if (!CommandLineOptions.Clo.UseLabels) {
                  var ctx = checker.TheoremProver.Context;
                  var bet = ctx.BoogieExprTranslator;
                  VCExpr controlFlowVariableExpr = bet.LookupVariable(info.controlFlowVariable);
                  VCExpr eqExpr = ctx.ExprGen.Eq(controlFlowVariableExpr, ctx.ExprGen.Integer(BigNum.FromInt(id)));
                  expansion = ctx.ExprGen.And(eqExpr, expansion);
                }

                // Instantiate the "forall" variables
                Dictionary<VCExprVar, VCExpr> substForallDict = new Dictionary<VCExprVar, VCExpr>();
                Contract.Assert(info.interfaceExprVars.Count == expr.Length);
                for (int i = 0; i < info.interfaceExprVars.Count; i++)
                {
                    substForallDict.Add(info.interfaceExprVars[i], expr[i]);
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
                if (CommandLineOptions.Clo.ModelViewFile != null) {
                  SaveSubstitution(vState, id, substForallDict, substExistsDict);
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
                if (useSummary) calls.matchSummaries();
                if(vState.coverageManager != null) vState.coverageManager.addRecentEdges(id);
                
                //expansion = checker.VCExprGen.Eq(calls.id2ControlVar[id], expansion);
                expansion = checker.VCExprGen.Implies(calls.id2ControlVar[id], expansion);
                calls.id2VC.Add(id, expansion);

                exprToPush = checker.VCExprGen.And(exprToPush, expansion);
            }
            vState.checker.AddAxiom(exprToPush);
            vState.vcSize += SizeComputingVisitor.ComputeSize(exprToPush);
        }

        // Does on-demand inlining -- inlines procedures into the VC of main.
        private void DoExpansionAndInline(List<int>/*!*/ candidates, VerificationState vState)
        {
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
                if (CommandLineOptions.Clo.ModelViewFile != null) {
                  SaveSubstitution(vState, id, substForallDict, substExistsDict);
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

            vState.updateMainVC(inliner.Mutate(vState.vcMain, true));
            vState.vcSize = SizeComputingVisitor.ComputeSize(vState.vcMain);
        }

        private void SaveSubstitution(VerificationState vState, int id, 
          Dictionary<VCExprVar, VCExpr> substForallDict, Dictionary<VCExprVar, VCExpr> substExistsDict) {
          var checker = vState.checker.underlyingChecker;
          var calls = vState.calls;
          Boogie2VCExprTranslator translator = checker.TheoremProver.Context.BoogieExprTranslator;
          VCExprVar mvStateConstant = translator.LookupVariable(ModelViewInfo.MVState_ConstantDef);
          substExistsDict.Add(mvStateConstant, checker.VCExprGen.Integer(BigNum.FromInt(id)));
          Dictionary<VCExprVar, VCExpr> mapping = new Dictionary<VCExprVar, VCExpr>();
          foreach (var key in substForallDict.Keys)
            mapping[key] = substForallDict[key];
          foreach (var key in substExistsDict.Keys)
            mapping[key] = substExistsDict[key];
          calls.id2Vars[id] = mapping;
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

            var exprGen = checker.TheoremProver.Context.ExprGen;
            VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : exprGen.Integer(BigNum.ZERO);

            vc = GenerateVC(impl, controlFlowVariableExpr, out label2absy, checker);

            if (!CommandLineOptions.Clo.UseLabels) {
              VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
              VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
              vc = exprGen.Implies(eqExpr, vc);
            }

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
            public Dictionary<BoogieCallExpr/*!*/, VCExpr>/*!*/ recordExpr2Var;
            public Dictionary<int, VCExprNAry/*!*/>/*!*/ id2Candidate;
            public Dictionary<int, VCExprVar/*!*/>/*!*/ id2ControlVar;
            public Dictionary<int, VCExpr> id2VC;
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

            // map from candidate to summary candidates
            public Dictionary<int, List<Tuple<VCExprVar, VCExpr>>> summaryCandidates;
            private Dictionary<string, List<Tuple<VCExprVar, VCExpr>>> summaryTemp;
            // set of all boolean guards of summaries
            public HashSet<VCExprVar> allSummaryConst;

            public HashSet<int> forcedCandidates;

            ////////////////////////////
            // For Proc-Copy-Bounding

            // candidate Ids for PCB VCs starting from this number. This is to ensure
            // that there is no clash with the usual candidate Ids
            public static readonly int pcbStartingCandidateId = 1000000;

            // Unique ID for BoogieCallExpr
            public Dictionary<BoogieCallExpr, int> pcbBoogieExpr2Id;

            // (Proc, copy number) -> candidate
            public Dictionary<Tuple<string, int>, int> procCopy2Id;

            ////////////////////////////


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

            public Dictionary<int, Dictionary<VCExprVar, VCExpr>> id2Vars;

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
                recordExpr2Var = new Dictionary<BoogieCallExpr, VCExpr>();

                pcbBoogieExpr2Id = new Dictionary<BoogieCallExpr, int>();
                procCopy2Id = new Dictionary<Tuple<string, int>, int>();

                forcedCandidates = new HashSet<int>();

                id2Vars = new Dictionary<int, Dictionary<VCExprVar, VCExpr>>();
                summaryCandidates = new Dictionary<int, List<Tuple<VCExprVar, VCExpr>>>();
                summaryTemp = new Dictionary<string, List<Tuple<VCExprVar, VCExpr>>>();
                allSummaryConst = new HashSet<VCExprVar>();
                id2VC = new Dictionary<int, VCExpr>();
            }

            public void Clear()
            {
                currCandidates = new HashSet<int>();
            }

            public bool isPCBCandidate(int id)
            {
                return (id >= pcbStartingCandidateId);
            }

            // Return the set of all candidates
            public HashSet<int> getAllCandidates()
            {
                var ret = new HashSet<int>(candidateParent.Keys);
                ret.Add(0);
                return ret;
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

            public Hashtable/*<int,absy>*/ getLabel2absy()
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
                    else if (calleeName.StartsWith(recordProcName))
                    {
                        Debug.Assert(callExpr.Length == 1);
                        Debug.Assert(callExpr[0] != null);
                        recordExpr2Var[new BoogieCallExpr(naryExpr, currInlineCount)] = callExpr[0];
                        return callExpr;
                    }
                    else
                    {
                        return callExpr;
                    }
                }

                // summary candidate
                if (lop.label.Substring(1).StartsWith("candidate_"))
                {
                    var pname = lop.label.Substring("candidate_".Length + 1);

                    if (!summaryTemp.ContainsKey(pname))
                        summaryTemp.Add(pname, new List<Tuple<VCExprVar, VCExpr>>());
                    
                    var expr = retnary[0] as VCExprNAry;
                    if (expr == null) return retnary[0];
                    if (expr.Op != VCExpressionGenerator.ImpliesOp) return retnary[0];
                    var tup = Tuple.Create(expr[0] as VCExprVar, expr[1]);
                    summaryTemp[pname].Add(tup);

                    return retnary[0];
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

            // Upgrades summaryTemp to summaryCandidates by matching ensure clauses with
            // the appropriate candidate they came from
            public void matchSummaries()
            {
                var id2Set = new Dictionary<string, List<Tuple<int, HashSet<VCExprVar>>>>();
                foreach (var id in recentlyAddedCandidates)
                {
                    var collect = new CollectVCVars();
                    var proc = getProc(id);
                    if (!id2Set.ContainsKey(proc)) id2Set.Add(proc, new List<Tuple<int, HashSet<VCExprVar>>>());
                    id2Set[proc].Add(Tuple.Create(id, collect.Collect(id2Candidate[id], true)));
                }
                
                foreach (var kvp in summaryTemp)
                {
                    Contract.Assert (id2Set.ContainsKey(kvp.Key));
                    var ls = id2Set[kvp.Key];
                    foreach (var tup in kvp.Value)
                    {
                        var collect = new CollectVCVars();
                        var s1 = collect.Collect(tup.Item2, true);
                        var found = false;
                        foreach (var t in ls)
                        {
                            var s2 = t.Item2;
                            if (s1.IsSubsetOf(s2))
                            {
                                if (!summaryCandidates.ContainsKey(t.Item1))
                                    summaryCandidates.Add(t.Item1, new List<Tuple<VCExprVar, VCExpr>>());
                                summaryCandidates[t.Item1].Add(tup);
                                allSummaryConst.Add(tup.Item1);
                                found = true;
                                break;
                            }
                        }
                        Contract.Assert(found);
                    }
                }
                summaryTemp.Clear();
            }

        } // end FCallHandler

        // Collects the set of all VCExprVar in a given VCExpr
        class CollectVCVars : CollectingVCExprVisitor<HashSet<VCExprVar>, bool>
        {
            public override HashSet<VCExprVar> Visit(VCExprVar node, bool arg)
            {
                var ret = new HashSet<VCExprVar>();
                ret.Add(node);
                return ret;
            }

            protected override HashSet<VCExprVar> CombineResults(List<HashSet<VCExprVar>> results, bool arg)
            {
                var ret = new HashSet<VCExprVar>();
                results.ForEach(s => ret.UnionWith(s));
                return ret;
            }
        }

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
                    ret = Gen.Function(originalNode.Op, newSubExprs, originalNode.TypeArguments);
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

        public class PCBErrorReporter : ProverInterface.ErrorHandler {
          public bool unsatCoreMode;
          public Implementation mainImpl;

          public PCBErrorReporter(Implementation impl) {
            this.unsatCoreMode = false;
            this.mainImpl = impl;
          }

          public override void OnModel(IList<string> labels, ErrorModel errModel) {
            if (unsatCoreMode) return;
            Console.WriteLine("Error in " + mainImpl.Name);
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
            public bool procBoundingMode;
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
                this.procBoundingMode = false;
                this.calls = null;
                this.candidatesToExpand = new List<int>();
                this.gotoCmdOrigins = gotoCmdOrigins;
            }

            public void SetCandidateHandler(FCallHandler calls)
            {
                Contract.Requires(calls != null);
                this.calls = calls;
            }

            List<Tuple<int, int>> orderedStateIds;

            private Model.Element GetModelValue(Model m, Variable v, int candidateId) {
              // first, get the unique name
              string uniqueName;

              VCExprVar vvar = context.BoogieExprTranslator.TryLookupVariable(v);
              if (vvar == null) {
                uniqueName = v.Name;
              }
              else {
                if (candidateId != 0) {
                  Dictionary<VCExprVar, VCExpr> mapping = calls.id2Vars[candidateId];
                  if (mapping.ContainsKey(vvar)) {
                    VCExpr e = mapping[vvar];
                    if (e is VCExprLiteral) {
                      VCExprLiteral lit = (VCExprLiteral)e;
                      return m.MkElement(lit.ToString());
                    }
                    vvar = (VCExprVar)mapping[vvar];
                  }
                }
                uniqueName = context.Lookup(vvar);
              }

              var f = m.TryGetFunc(uniqueName);
              if (f == null)
                return m.MkFunc("@undefined", 0).GetConstant();
              return f.GetConstant();
            }
         
            public readonly static int CALL = -1;
            public readonly static int RETURN = -2;

            public void PrintModel(Model model) {
              var filename = CommandLineOptions.Clo.ModelViewFile;
              if (model == null || filename == null) return;

              if (filename == "-") {
                model.Write(Console.Out);
                Console.Out.Flush();
              }
              else {
                using (var wr = new StreamWriter(filename, !Counterexample.firstModelFile)) {
                  Counterexample.firstModelFile = false;
                  model.Write(wr);
                }
              }
            }

            private void GetModelWithStates(Model m) {
              if (m == null) return;

              var mvstates = m.TryGetFunc("@MV_state");
              if (mvstates == null)
                return;

              Contract.Assert(mvstates.Arity == 2);

              foreach (Variable v in mvInfo.AllVariables) {
                m.InitialState.AddBinding(v.Name, GetModelValue(m, v, 0));
              }

              int lastCandidate = 0;
              int lastCapturePoint = CALL;
              for (int i = 0; i < this.orderedStateIds.Count; ++i) {
                var s = orderedStateIds[i];
                int candidate = s.Item1;
                int capturePoint = s.Item2;
                string implName = calls.getProc(candidate);
                ModelViewInfo info = candidate == 0 ? mvInfo : implName2StratifiedInliningInfo[implName].mvInfo;

                if (capturePoint == CALL || capturePoint == RETURN) {
                  lastCandidate = candidate;
                  lastCapturePoint = capturePoint;
                  continue;
                }

                Contract.Assume(0 <= capturePoint && capturePoint < info.CapturePoints.Count);
                VC.ModelViewInfo.Mapping map = info.CapturePoints[capturePoint];
                var prevInc = (lastCapturePoint != CALL && lastCapturePoint != RETURN && candidate == lastCandidate) 
                  ? info.CapturePoints[lastCapturePoint].IncarnationMap : new Hashtable();
                var cs = m.MkState(map.Description);

                foreach (Variable v in info.AllVariables) {
                  var e = (Expr)map.IncarnationMap[v];

                  if (e == null) {
                    if (lastCapturePoint == CALL || lastCapturePoint == RETURN) {
                      cs.AddBinding(v.Name, GetModelValue(m, v, candidate));
                    }
                    continue;
                  }

                  if (lastCapturePoint != CALL && lastCapturePoint != RETURN && prevInc[v] == e) continue; // skip unchanged variables

                  Model.Element elt;
                  if (e is IdentifierExpr) {
                    IdentifierExpr ide = (IdentifierExpr)e;
                    elt = GetModelValue(m, ide.Decl, candidate);
                  }
                  else if (e is LiteralExpr) {
                    LiteralExpr lit = (LiteralExpr)e;
                    elt = m.MkElement(lit.Val.ToString());
                  }
                  else {
                    Contract.Assume(false);
                    elt = m.MkFunc(e.ToString(), 0).GetConstant();
                  }
                  cs.AddBinding(v.Name, elt);
                }

                lastCandidate = candidate;
                lastCapturePoint = capturePoint;
              }

              return;
            }

            public override void OnModel(Dictionary<int, IList<string>> labels, ErrorModel errModel) {
              Dictionary<int, List<Absy>> id2AbsyList = new Dictionary<int, List<Absy>>();
              foreach (var controlFlowConstant in labels.Keys) {
                IList<string> labelPath = labels[controlFlowConstant];
                List<Absy> absyList = new List<Absy>();
                foreach (var label in labelPath) {
                  if (controlFlowConstant == 0) {
                    absyList.Add(Label2Absy(label));
                  } else {
                    VCExprNAry expr = calls.id2Candidate[controlFlowConstant];
                    string procName = (cce.NonNull(expr.Op as VCExprBoogieFunctionOp)).Func.Name;
                    absyList.Add(Label2Absy(procName, label));
                  }
                }
                id2AbsyList[controlFlowConstant] = absyList;
              }

              orderedStateIds = new List<Tuple<int, int>>();
              candidatesToExpand = new List<int>();

              Model model = null;
              if (errModel != null) model = errModel.ToModel();

              if (underapproximationMode) {
                var cex = NewTrace(0, id2AbsyList, model);
                Debug.Assert(candidatesToExpand.Count == 0);
                if (cex != null) {
                  GetModelWithStates(model);
                  callback.OnCounterexample(cex, null);
                  this.PrintModel(model);
                }
                return;
              }

              NewTrace(0, id2AbsyList, model);
            }

            private Counterexample NewTrace(int candidateId, Dictionary<int, List<Absy>> id2AbsyList, Model model) {
              List<Absy> absyList = id2AbsyList[candidateId];
              BlockSeq trace = new BlockSeq();
              TransferCmd transferCmd = null;
              var calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();
              foreach (Absy absy in absyList) {
                Block b = absy as Block;
                if (b == null) {
                  Counterexample newCounterexample = AssertCmdToCounterexample((AssertCmd)absy, transferCmd, trace, model, mvInfo, context);
                  newCounterexample.AddCalleeCounterexample(calleeCounterexamples); 
                  return newCounterexample;
                }
                transferCmd = b.TransferCmd;
                trace.Add(b);
                CmdSeq cmdSeq = b.Cmds;
                for (int i = 0; i < cmdSeq.Length; i++) {
                  AssumeCmd assumeCmd = cmdSeq[i] as AssumeCmd;
                  if (assumeCmd == null) continue;
                  NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
                  if (naryExpr == null)
                    continue;
                  string calleeName = naryExpr.Fun.FunctionName;
                  Contract.Assert(calleeName != null);

                  BinaryOperator binOp = naryExpr.Fun as BinaryOperator;
                  if (binOp != null && binOp.Op == BinaryOperator.Opcode.And) {
                    Expr expr = naryExpr.Args[0];
                    NAryExpr mvStateExpr = expr as NAryExpr;
                    if (mvStateExpr != null && mvStateExpr.Fun.FunctionName == ModelViewInfo.MVState_FunctionDef.Name) {
                      LiteralExpr x = mvStateExpr.Args[1] as LiteralExpr;
                      orderedStateIds.Add(new Tuple<int, int>(candidateId, x.asBigNum.ToInt));
                    }
                  }

                  if (calleeName.StartsWith(recordProcName) && model != null) {
                    var expr = calls.recordExpr2Var[new BoogieCallExpr(naryExpr, candidateId)];

                    // Record concrete value of the argument to this procedure
                    var args = new List<Model.Element>();
                    if (expr is VCExprIntLit) {
                      args.Add(model.MkElement((expr as VCExprIntLit).Val.ToString()));
                    }
                    else if (expr == VCExpressionGenerator.True) {
                      args.Add(model.MkElement("true"));
                    }
                    else if (expr == VCExpressionGenerator.False) {
                      args.Add(model.MkElement("false"));
                    }
                    else if (expr is VCExprVar) {
                      var idExpr = expr as VCExprVar;
                      string name = context.Lookup(idExpr);
                      Contract.Assert(name != null);
                      Model.Func f = model.TryGetFunc(name);
                      if (f != null) {
                        args.Add(f.GetConstant());
                      }
                    }
                    else {
                      Contract.Assert(false);
                    }
                    calleeCounterexamples[new TraceLocation(trace.Length - 1, i)] =
                         new CalleeCounterexampleInfo(null, args);
                    continue;
                  }

                  if (!implName2StratifiedInliningInfo.ContainsKey(calleeName))
                    continue;

                  int calleeId = calls.boogieExpr2Id[new BoogieCallExpr(naryExpr, candidateId)];

                  if (calls.currCandidates.Contains(calleeId)) {
                    candidatesToExpand.Add(calleeId);
                  }
                  else {
                    orderedStateIds.Add(new Tuple<int, int>(calleeId, StratifiedInliningErrorReporter.CALL));
                    calleeCounterexamples[new TraceLocation(trace.Length - 1, i)] =
                      new CalleeCounterexampleInfo(NewTrace(calleeId, id2AbsyList, model), new List<Model.Element>());
                    orderedStateIds.Add(new Tuple<int, int>(candidateId, StratifiedInliningErrorReporter.RETURN));
                  }
                }
              }
              throw new Exception("Error in creating interprocedural counterexample");
            }

            public override void OnModel(IList<string/*!*/>/*!*/ labels, ErrorModel errModel)
            {
                Contract.Assert(CommandLineOptions.Clo.StratifiedInliningWithoutModels || errModel != null);

                candidatesToExpand = new List<int>();

                Model model = null;
                if (errModel != null) model = errModel.ToModel();

                if (underapproximationMode)
                {
                    var cex = GenerateTraceMain(labels, model, mvInfo);
                    Debug.Assert(candidatesToExpand.Count == 0);
                    if (cex != null) {
                      GetModelWithStates(model);
                      callback.OnCounterexample(cex, null);
                      this.PrintModel(model);
                    }
                    return;
                }
                
                Contract.Assert(calls != null);

                GenerateTraceMain(labels, model, mvInfo);
            }

            // Construct the interprocedural trace
            private Counterexample GenerateTraceMain(IList<string/*!*/>/*!*/ labels, Model/*!*/ errModel, ModelViewInfo mvInfo)
            {
                Contract.Requires(cce.NonNullElements(labels));
                if (CommandLineOptions.Clo.PrintErrorModel >= 1 && errModel != null)
                {
                    errModel.Write(ErrorReporter.ModelWriter);
                    ErrorReporter.ModelWriter.Flush();
                }

                orderedStateIds = new List<Tuple<int,int>>();
                Counterexample newCounterexample =
                  GenerateTrace(labels, errModel, 0, mainImpl);

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

            private Counterexample GenerateTrace(IList<string/*!*/>/*!*/ labels, Model/*!*/ errModel,
                                                 int candidateId, Implementation procImpl)
            {
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
                                  IList<string/*!*/>/*!*/ labels, Model/*!*/ errModel, ModelViewInfo mvInfo, 
                                  int candidateId,
                                  Block/*!*/ b, Hashtable/*!*/ traceNodes, BlockSeq/*!*/ trace,
                                  Dictionary<TraceLocation/*!*/, CalleeCounterexampleInfo/*!*/>/*!*/ calleeCounterexamples)
            {
                Contract.Requires(cce.NonNullElements(labels));
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
                            Counterexample newCounterexample = AssertCmdToCounterexample((AssertCmd)cmd, transferCmd, trace, errModel, mvInfo, context);
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

                        BinaryOperator binOp = naryExpr.Fun as BinaryOperator;
                        if (binOp != null && binOp.Op == BinaryOperator.Opcode.And) {
                          Expr expr = naryExpr.Args[0];
                          NAryExpr mvStateExpr = expr as NAryExpr;
                          if (mvStateExpr != null && mvStateExpr.Fun.FunctionName == ModelViewInfo.MVState_FunctionDef.Name) {
                            LiteralExpr x = mvStateExpr.Args[1] as LiteralExpr;
                            orderedStateIds.Add(new Tuple<int, int>(candidateId, x.asBigNum.ToInt));
                          }
                        }

                        if (calleeName.StartsWith(recordProcName) && errModel != null)
                        {
                            var expr = calls.recordExpr2Var[new BoogieCallExpr(naryExpr, candidateId)];

                            // Record concrete value of the argument to this procedure
                            var args = new List<Model.Element>();
                            if (expr is VCExprIntLit)
                            {
                                args.Add(errModel.MkElement((expr as VCExprIntLit).Val.ToString()));
                            }
                            else if (expr == VCExpressionGenerator.True)
                            {
                                args.Add(errModel.MkElement("true"));
                            }
                            else if (expr == VCExpressionGenerator.False)
                            {
                                args.Add(errModel.MkElement("false"));
                            }
                            else if (expr is VCExprVar)
                            {
                                var idExpr = expr as VCExprVar;
                                string name = context.Lookup(idExpr);
                                Contract.Assert(name != null);
                                Model.Func f = errModel.TryGetFunc(name);
                                if (f != null)
                                {
                                    args.Add(f.GetConstant());
                                }
                            }
                            else
                            {
                                Contract.Assert(false);
                            }
                            calleeCounterexamples[new TraceLocation(trace.Length - 1, i)] =
                                 new CalleeCounterexampleInfo(null, args);
                            continue;
                        }

                        if (!implName2StratifiedInliningInfo.ContainsKey(calleeName))
                            continue;

                        Contract.Assert(calls != null);

                        if (calls.isPCBCandidate(candidateId))
                        {
                            Contract.Assert(procBoundingMode);
                            // We're already inside PCB VCs. The lookup for procedure calls
                            // is different here
                            var uid = calls.pcbBoogieExpr2Id[new BoogieCallExpr(naryExpr, candidateId)];
                            var pcopy = pcbFindLabel(labels, string.Format("PCB_{0}_", uid));
                            var actualId = calls.procCopy2Id[Tuple.Create(calleeName, pcopy)];

                            orderedStateIds.Add(new Tuple<int, int>(actualId, StratifiedInliningErrorReporter.CALL));
                            calleeCounterexamples[new TraceLocation(trace.Length - 1, i)] =
                                new CalleeCounterexampleInfo(
                                    cce.NonNull(GenerateTrace(labels, errModel, actualId, implName2StratifiedInliningInfo[calleeName].impl)),
                                    new List<Model.Element>());
                            orderedStateIds.Add(new Tuple<int, int>(candidateId, StratifiedInliningErrorReporter.RETURN));
                        }
                        else
                        {
                            int calleeId = calls.boogieExpr2Id[new BoogieCallExpr(naryExpr, candidateId)];

                            if (calls.currCandidates.Contains(calleeId)) {
                              if (procBoundingMode) {
                                // Entering PCB VCs
                                var pcopy = pcbFindLabel(labels, string.Format("PCB_CONNECT_{0}_", calleeId));
                                Contract.Assert(pcopy >= 0 && pcopy < CommandLineOptions.Clo.ProcedureCopyBound);
                                var actualId = calls.procCopy2Id[Tuple.Create(calleeName, pcopy)];

                                orderedStateIds.Add(new Tuple<int, int>(actualId, StratifiedInliningErrorReporter.CALL));
                                calleeCounterexamples[new TraceLocation(trace.Length - 1, i)] =
                                    new CalleeCounterexampleInfo(
                                        cce.NonNull(GenerateTrace(labels, errModel, actualId, implName2StratifiedInliningInfo[calleeName].impl)),
                                        new List<Model.Element>());
                                orderedStateIds.Add(new Tuple<int, int>(candidateId, StratifiedInliningErrorReporter.RETURN));
                              }
                              else {
                                candidatesToExpand.Add(calleeId);
                              }
                            }
                            else {
                              orderedStateIds.Add(new Tuple<int, int>(calleeId, StratifiedInliningErrorReporter.CALL));
                              calleeCounterexamples[new TraceLocation(trace.Length - 1, i)] =
                                  new CalleeCounterexampleInfo(
                                      cce.NonNull(GenerateTrace(labels, errModel, calleeId, implName2StratifiedInliningInfo[calleeName].impl)),
                                      new List<Model.Element>());
                              orderedStateIds.Add(new Tuple<int, int>(candidateId, StratifiedInliningErrorReporter.RETURN));
                            }
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

        public override Counterexample extractLoopTrace(Counterexample cex, string mainProcName, Program program, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
        {
            // Construct the set of inlined procs in the original program
            var inlinedProcs = new HashSet<string>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                // Implementations
                if (decl is Implementation)
                {
                    var impl = decl as Implementation;
                    if (!(impl.Proc is LoopProcedure))
                    {
                        inlinedProcs.Add(impl.Name);
                    }
                }

                // And recording procedures
                if (decl is Procedure)
                {
                    var proc = decl as Procedure;
                    if (proc.Name.StartsWith(recordProcName))
                    {
                        Debug.Assert(!(decl is LoopProcedure));
                        inlinedProcs.Add(proc.Name);
                    }
                }
            }

            return extractLoopTraceRec(
                new CalleeCounterexampleInfo(cex, new List<Model.Element>()),
                mainProcName, inlinedProcs, extractLoopMappingInfo).counterexample;
        }

        protected override bool elIsLoop(string procname)
        {
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
