using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public class YieldingProcDuplicator : Duplicator
    { 
        /* This class creates duplicate copies of yielding procedures for a particular layer
         * rewriting calls to procedures that have been converted to atomic actions. 
         * Async calls are also rewritten so that the resulting copies are guaranteed not to
         * have any async calls.  The copy of yielding procedure X shares local variables of X.
         * This sharing is exploited when instrumenting the duplicates in the class
         * YieldProcInstrumentation.
         */
        private CivlTypeChecker civlTypeChecker;
        private LinearTypeChecker linearTypeChecker;
        private int layerNum;

        private Dictionary<Procedure, Procedure> procToDuplicate; /* Original -> Duplicate */
        private Dictionary<Absy, Absy> absyMap; /* Duplicate -> Original */
        private HashSet<Procedure> yieldingProcs;
        private Dictionary<string, Procedure> asyncCallPreconditionCheckers;

        public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, LinearTypeChecker linearTypeChecker, int layerNum)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.layerNum = layerNum;
            this.procToDuplicate = new Dictionary<Procedure, Procedure>();
            this.absyMap = new Dictionary<Absy, Absy>();
            this.yieldingProcs = new HashSet<Procedure>();
            this.asyncCallPreconditionCheckers = new Dictionary<string, Procedure>();
        }

        #region Procedure duplication
        public override Procedure VisitProcedure(Procedure node)
        {
            Debug.Assert(civlTypeChecker.procToYieldingProc.ContainsKey(node));
            if (!procToDuplicate.ContainsKey(node))
            {
                YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[node];
                Debug.Assert(layerNum <= yieldingProc.upperLayer);

                Procedure proc = (Procedure)node.Clone();
                proc.Name = $"{node.Name}_{layerNum}";
                proc.InParams = this.VisitVariableSeq(node.InParams);
                proc.OutParams = this.VisitVariableSeq(node.OutParams);
                proc.Requires = this.VisitRequiresSeq(node.Requires);
                proc.Ensures = this.VisitEnsuresSeq(node.Ensures);
                if (yieldingProc is MoverProc moverProc && yieldingProc.upperLayer == layerNum)
                {
                    proc.Modifies = moverProc.modifiedGlobalVars.Select(g => Expr.Ident(g)).ToList();
                }
                else
                {
                    proc.Modifies = civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList();
                    yieldingProcs.Add(proc);
                }

                procToDuplicate[node] = proc;
                absyMap[proc] = node;
            }

            return procToDuplicate[node];
        }

        public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
        {
            requiresSeq = base.VisitRequiresSeq(requiresSeq);
            requiresSeq.RemoveAll(req => req.Condition.Equals(Expr.True));
            return requiresSeq;
        }

        public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
        {
            ensuresSeq = base.VisitEnsuresSeq(ensuresSeq);
            ensuresSeq.RemoveAll(ens => ens.Condition.Equals(Expr.True));
            return ensuresSeq;
        }

        public override Requires VisitRequires(Requires node)
        {
            Requires requires = base.VisitRequires(node);
            if (node.Free)
                return requires;
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                requires.Condition = Expr.True;
            return requires;
        }

        public override Ensures VisitEnsures(Ensures node)
        {
            Ensures ensures = base.VisitEnsures(node);
            if (node.Free)
                return ensures;
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                ensures.Condition = Expr.True;
            return ensures;
        }
        #endregion

        #region Implementation duplication
        private Implementation enclosingImpl;
        private YieldingProc enclosingYieldingProc;
        private bool IsRefinementLayer => layerNum == enclosingYieldingProc.upperLayer;
        private bool SummaryHasPendingAsyncParam => ((ActionProc)enclosingYieldingProc).refinedAction.HasPendingAsyncs;
        private List<Cmd> newCmdSeq;

        private Variable returnedPAs;
        private Variable ReturnedPAs
        {
            get
            {
                if (returnedPAs == null)
                    returnedPAs = VarHelper.LocalVariable("returnedPAs", civlTypeChecker.pendingAsyncMultisetType);
                return returnedPAs;
            }
        }

        private Variable CollectedPAs
        {
            get
            {
                if (!civlTypeChecker.implToPendingAsyncCollector.TryGetValue(enclosingImpl, out var collectedPAs))
                {
                    collectedPAs = VarHelper.LocalVariable("collectedPAs", civlTypeChecker.pendingAsyncMultisetType);
                    civlTypeChecker.implToPendingAsyncCollector[enclosingImpl] = collectedPAs;
                }
                return collectedPAs;
            }
        }

        public override Implementation VisitImplementation(Implementation impl)
        {
            Debug.Assert(civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc));
            enclosingImpl = impl;
            enclosingYieldingProc = civlTypeChecker.procToYieldingProc[impl.Proc];
            Debug.Assert(layerNum <= enclosingYieldingProc.upperLayer);

            returnedPAs = null;

            Implementation newImpl = base.VisitImplementation(impl);
            newImpl.Name = newImpl.Proc.Name;

            if (returnedPAs != null)
                newImpl.LocVars.Add(returnedPAs);
            if (enclosingYieldingProc is ActionProc && SummaryHasPendingAsyncParam && IsRefinementLayer)
            {
                // TODO: This was copied from InductiveSequentialization property NoPendingAsyncs.
                // Unify pending async stuff in something like PendingAsyncInstrumentation?
                var paBound = VarHelper.BoundVariable("pa", civlTypeChecker.pendingAsyncType);
                var pa = Expr.Ident(paBound);
                var expr = Expr.Eq(Expr.Select(Expr.Ident(CollectedPAs), pa), Expr.Literal(0));
                var forallExpr = new ForallExpr(Token.NoToken, new List<Variable> { paBound }, expr);
                forallExpr.Typecheck(new TypecheckingContext(null));
                newImpl.Blocks.First().Cmds.Insert(0, CmdHelper.AssumeCmd(forallExpr));

                if (!impl.LocVars.Contains(CollectedPAs))
                    newImpl.LocVars.Add(CollectedPAs);
            }

            absyMap[newImpl] = impl;
            return newImpl;
        }

        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            YieldCmd yieldCmd = base.VisitYieldCmd(node);
            absyMap[yieldCmd] = node;
            return yieldCmd;
        }

        public override Block VisitBlock(Block node)
        {
            Block block = base.VisitBlock(node);
            absyMap[block] = node;
            return block;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            AssertCmd assertCmd = (AssertCmd) base.VisitAssertCmd(node);
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                assertCmd.Expr = Expr.True;
            return assertCmd;
        }

        public override Cmd VisitCallCmd(CallCmd call)
        {
            CallCmd newCall = (CallCmd) base.VisitCallCmd(call);
            absyMap[newCall] = call;
            return newCall;
        }
        public override Cmd VisitParCallCmd(ParCallCmd parCall)
        {
            ParCallCmd newParCall = (ParCallCmd) base.VisitParCallCmd(parCall);
            absyMap[newParCall] = parCall;
            foreach (var newCall in newParCall.CallCmds)
            {
                absyMap[newCall] = parCall;
            }
            return newParCall;
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            newCmdSeq = new List<Cmd>();
            foreach(var cmd in cmdSeq)
            {
                Cmd newCmd = (Cmd)Visit(cmd);

                if (newCmd is CallCmd)
                {
                    ProcessCallCmd((CallCmd)newCmd);
                }
                else if (newCmd is ParCallCmd)
                {
                    ProcessParCallCmd((ParCallCmd) newCmd);
                }
                else if (!(newCmd is PredicateCmd predicateCmd && predicateCmd.Expr.Equals(Expr.True)))
                {
                    newCmdSeq.Add(newCmd);
                }
            }

            return newCmdSeq;
        }

        private void ProcessCallCmd(CallCmd newCall)
        {
            if (civlTypeChecker.procToIntroductionAction.ContainsKey(newCall.Proc))
            {
                var introductionAction = civlTypeChecker.procToIntroductionAction[newCall.Proc];
                if (introductionAction.LayerNum == layerNum)
                {
                    InjectGate(introductionAction, newCall);
                    newCmdSeq.Add(newCall);
                }
                return;
            }

            if (civlTypeChecker.procToLemmaProc.ContainsKey(newCall.Proc))
            {
                if (civlTypeChecker.FindLayers(newCall.Attributes)[0] == layerNum)
                {
                    newCmdSeq.Add(newCall);
                }
                return;
            }
            
            // handle calls to yielding procedures in the rest of this method
            YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[newCall.Proc];
            
            if (newCall.IsAsync)
            {
                if (yieldingProc.upperLayer < layerNum)
                {
                    if (newCall.HasAttribute(CivlAttributes.SYNC))
                    {
                        // synchronize the called atomic action
                        Debug.Assert(yieldingProc is ActionProc);
                        AddActionCall(newCall, (ActionProc)yieldingProc);
                    }
                    else if (IsRefinementLayer && yieldingProc is ActionProc actionProc)
                    {
                        AddPendingAsync(newCall, actionProc);
                    }
                }
                else
                {
                    if (yieldingProc is MoverProc && yieldingProc.upperLayer == layerNum)
                    {
                        // synchronize the called mover procedure
                        AddDuplicateCall(newCall);
                    }
                    else
                    {
                        DesugarAsyncCall(newCall);
                        if (IsRefinementLayer && yieldingProc is ActionProc actionProc)
                        {
                            AddPendingAsync(newCall, actionProc);
                        }
                    }
                }
                return;
            }
            
            // handle synchronous calls to skip procedures
            if (yieldingProc is SkipProc)
            {
                if (yieldingProc.upperLayer >= layerNum)
                {
                    AddDuplicateCall(newCall);
                }
                return;
            }

            // handle synchronous calls to mover procedures
            if (yieldingProc is MoverProc)
            {
                AddDuplicateCall(newCall);
                return;
            }
            
            // handle synchronous calls to action procedures
            {
                Debug.Assert(yieldingProc is ActionProc);
                var actionProc = (ActionProc)yieldingProc;
                if (actionProc.upperLayer < layerNum)
                {
                    AddActionCall(newCall, actionProc);
                }
                else
                {
                    AddDuplicateCall(newCall);
                }
                Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count);
            }
        }

        private void ProcessParCallCmd(ParCallCmd newParCall)
        {
            int maxCalleeLayerNum = newParCall.CallCmds.Select(c => civlTypeChecker.procToYieldingProc[c.Proc].upperLayer).Max();

            if (layerNum > maxCalleeLayerNum)
            {
                foreach (var call in newParCall.CallCmds)
                {
                    ProcessCallCmd(call);
                }
            }
            else
            {
                List<CallCmd> newCallCmds = new List<CallCmd>();
                foreach (var call in newParCall.CallCmds)
                {
                    YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[call.Proc];
                    if (yieldingProc is SkipProc && yieldingProc.upperLayer < layerNum)
                    {
                        continue;
                    }
                    else
                    {
                        call.Proc = procToDuplicate[call.Proc];
                        call.callee = call.Proc.Name;
                        newCallCmds.Add(call);
                    }
                }
                Debug.Assert(newCallCmds.Count > 0);
                newParCall.CallCmds = newCallCmds;
                newCmdSeq.Add(newParCall);
            }
        }

        private void AddActionCall(CallCmd newCall, ActionProc actionProc)
        {
            var refinedAction = actionProc.RefinedActionAtLayer(layerNum);

            newCall.IsAsync = false;
            newCall.Proc = refinedAction.proc;
            newCall.callee = newCall.Proc.Name;

            // We drop the hidden parameters of the procedure from the call to the action.
            Debug.Assert(newCall.Ins.Count == actionProc.proc.InParams.Count);
            Debug.Assert(newCall.Outs.Count == actionProc.proc.OutParams.Count);
            var newIns = new List<Expr>();
            var newOuts = new List<IdentifierExpr>();
            for (int i = 0; i < actionProc.proc.InParams.Count; i++)
            {
                if (civlTypeChecker.FormalRemainsInAction(actionProc, actionProc.proc.InParams[i]))
                {
                    newIns.Add(newCall.Ins[i]);
                }
            }
            for (int i = 0; i < actionProc.proc.OutParams.Count; i++)
            {
                if (civlTypeChecker.FormalRemainsInAction(actionProc, actionProc.proc.OutParams[i]))
                {
                    newOuts.Add(newCall.Outs[i]);
                }
            }
            newCall.Ins = newIns;
            newCall.Outs = newOuts;

            InjectGate(refinedAction, newCall, !IsRefinementLayer);
            newCmdSeq.Add(newCall);

            if (refinedAction.HasPendingAsyncs)
            {
                Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count - 1);
                CollectReturnedPendingAsyncs(newCall);
            }
        }

        private void InjectGate(Action action, CallCmd callCmd, bool assume = false)
        {
            if (action.gate.Count == 0) return;

            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            for (int i = 0; i < action.proc.InParams.Count; i++)
            {
                // Parameters come from the implementation that defines the action
                map[action.impl.InParams[i]] = callCmd.Ins[i];
            }
            Substitution subst = Substituter.SubstitutionFromHashtable(map);

            // Important: Do not remove CommentCmd!
            // It separates the injected gate from yield assertions.
            newCmdSeq.Add(new CommentCmd("<<< injected gate"));
            foreach (AssertCmd assertCmd in action.gate)
            {
                var expr = Substituter.Apply(subst, assertCmd.Expr);
                if (assume)
                    newCmdSeq.Add(new AssumeCmd(assertCmd.tok, expr));
                else
                    newCmdSeq.Add(new AssertCmd(assertCmd.tok, expr)
                        { ErrorData = $"This gate of {action.proc.Name} might not hold." });
            }
            newCmdSeq.Add(new CommentCmd("injected gate >>>"));
        }

        private void CollectReturnedPendingAsyncs(CallCmd newCall)
        {
            // Inject pending async collection
            newCall.Outs.Add(Expr.Ident(ReturnedPAs));
            if (!IsRefinementLayer) return;
            if (SummaryHasPendingAsyncParam)
            {
                var collectedUnionReturned = ExprHelper.FunctionCall(civlTypeChecker.pendingAsyncAdd,
                    Expr.Ident(CollectedPAs), Expr.Ident(ReturnedPAs));
                newCmdSeq.Add(CmdHelper.AssignCmd(CollectedPAs, collectedUnionReturned));
            }
            else
            {
                // TODO: As above, this was copied from InductiveSequentialization property NoPendingAsyncs.
                // Unify pending async stuff in something like PendingAsyncInstrumentation?
                var paBound = VarHelper.BoundVariable("pa", civlTypeChecker.pendingAsyncType);
                var pa = Expr.Ident(paBound);
                var expr = Expr.Eq(Expr.Select(Expr.Ident(ReturnedPAs), pa), Expr.Literal(0));
                var forallExpr = new ForallExpr(Token.NoToken, new List<Variable> { paBound }, expr);
                forallExpr.Typecheck(new TypecheckingContext(null));
                newCmdSeq.Add(new AssertCmd(newCall.tok, forallExpr)
                { ErrorData = "Pending asyncs created by this call are not summarized" });
            }
        }

        private void AddDuplicateCall(CallCmd newCall)
        {
            newCall.IsAsync = false;
            newCall.Proc = procToDuplicate[newCall.Proc];
            newCall.callee = newCall.Proc.Name;
            newCmdSeq.Add(newCall);
        }

        private void DesugarAsyncCall(CallCmd newCall)
        {
            if (!asyncCallPreconditionCheckers.ContainsKey(newCall.Proc.Name))
            {
                asyncCallPreconditionCheckers[newCall.Proc.Name] = new Procedure(Token.NoToken,
                    $"AsyncCallPreconditionChecker_{newCall.Proc.Name}",
                    newCall.Proc.TypeParameters, newCall.Proc.InParams, newCall.Proc.OutParams,
                    procToDuplicate[newCall.Proc].Requires, new List<IdentifierExpr>(), new List<Ensures>());
            }

            var asyncCallPreconditionChecker = asyncCallPreconditionCheckers[newCall.Proc.Name];
            newCall.Proc = asyncCallPreconditionChecker;
            newCall.callee = newCall.Proc.Name;
            newCmdSeq.Add(newCall);
        }

        private void AddPendingAsync(CallCmd newCall, ActionProc actionProc)
        {
            if (SummaryHasPendingAsyncParam)
            {
                AtomicAction paAction;
                if (actionProc.upperLayer == enclosingYieldingProc.upperLayer)
                    paAction = actionProc.refinedAction;
                else
                    paAction = actionProc.RefinedActionAtLayer(layerNum);

                Expr[] newIns = new Expr[paAction.proc.InParams.Count];
                for (int i = 0, j = 0; i < actionProc.proc.InParams.Count; i++)
                {
                    if (civlTypeChecker.FormalRemainsInAction(actionProc, actionProc.proc.InParams[i]))
                    {
                        newIns[j] = newCall.Ins[i];
                        j++;
                    }
                }

                var pa = ExprHelper.FunctionCall(paAction.pendingAsyncCtor, newIns);
                var inc = Expr.Add(Expr.Select(Expr.Ident(CollectedPAs), pa), Expr.Literal(1));
                var add = CmdHelper.AssignCmd(CollectedPAs, Expr.Store(Expr.Ident(CollectedPAs), pa, inc));
                newCmdSeq.Add(add);
            }
            else
            {
                newCmdSeq.Add(new AssertCmd(newCall.tok, Expr.False)
                    {ErrorData = "This pending async is not summarized"});
            }
        }
        #endregion

        public List<Declaration> Collect()
        {
            var decls = new List<Declaration>();
            decls.AddRange(procToDuplicate.Values);
            var newImpls = absyMap.Keys.OfType<Implementation>();
            decls.AddRange(newImpls);
            decls.AddRange(asyncCallPreconditionCheckers.Values);
            decls.AddRange(YieldingProcInstrumentation.TransformImplementations(
                civlTypeChecker,
                linearTypeChecker,
                layerNum,
                absyMap,
                yieldingProcs));
            return decls;
        }
    }
}
