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
        private Implementation enclosingImpl;
        private YieldingProc enclosingYieldingProc;

        private int layerNum;
        private Dictionary<Procedure, Procedure> procMap; /* Original -> Duplicate */
        private Dictionary<Absy, Absy> absyMap; /* Duplicate -> Original */
        private HashSet<Procedure> yieldingProcs;
        private Dictionary<string, Procedure> asyncCallPreconditionCheckers;
        
        public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, LinearTypeChecker linearTypeChecker, int layerNum)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.layerNum = layerNum;
            this.procMap = new Dictionary<Procedure, Procedure>();
            this.absyMap = new Dictionary<Absy, Absy>();
            this.yieldingProcs = new HashSet<Procedure>();
            this.asyncCallPreconditionCheckers = new Dictionary<string, Procedure>();
        }

        public override Procedure VisitProcedure(Procedure node)
        {
            if (!civlTypeChecker.procToYieldingProc.ContainsKey(node))
                return node;
            if (!procMap.ContainsKey(node))
            {
                YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[node];

                if (layerNum > yieldingProc.upperLayer)
                {
                    if (yieldingProc is ActionProc actionProc)
                    {
                        // yielding procedure already transformed to atomic action
                        var refinedAction = actionProc.RefinedActionAtLayer(layerNum);
                        if (refinedAction == null)
                            // TODO: This can only happen because YieldingProcChecker.AddCheckers calls
                            // VisitProcedure on every layer. Do this "call redirection" somewhere else?
                            return node;
                        return refinedAction.proc;
                    }
                    else if (yieldingProc is SkipProc)
                    {
                        // calls to skip procedures are erased
                        return node;
                    }
                    else if (yieldingProc is MoverProc)
                    {
                        // mover procedure does not exist on this layer any more
                        return node;
                    }
                }

                Procedure proc = (Procedure) node.Clone();
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

                procMap[node] = proc;
                absyMap[proc] = node;
            }

            return procMap[node];
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

        private bool IsRefinementLayer => layerNum == enclosingYieldingProc.upperLayer;

        public override Implementation VisitImplementation(Implementation impl)
        {
            if (!civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc))
                return impl;

            enclosingImpl = impl;
            enclosingYieldingProc = civlTypeChecker.procToYieldingProc[impl.Proc];
            if (layerNum > enclosingYieldingProc.upperLayer)
                return impl;

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
            newCall.Proc = VisitProcedure(newCall.Proc);
            newCall.callee = newCall.Proc.Name;
            absyMap[newCall] = call;
            return newCall;
        }

        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            ParCallCmd parCallCmd = (ParCallCmd) base.VisitParCallCmd(node);
            absyMap[parCallCmd] = node;
            return parCallCmd;
        }

        private List<Cmd> newCmdSeq;

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            newCmdSeq = new List<Cmd>();
            foreach(var cmd in cmdSeq)
            {
                Cmd newCmd = (Cmd)Visit(cmd);

                if (newCmd is CallCmd)
                {
                    ProcessCallCmd((CallCmd) cmd, (CallCmd)newCmd);
                }
                else if (newCmd is ParCallCmd)
                {
                    ProcessParCallCmd((ParCallCmd) cmd, (ParCallCmd) newCmd);
                }
                else if (!(newCmd is PredicateCmd predicateCmd && predicateCmd.Expr.Equals(Expr.True)))
                {
                    newCmdSeq.Add(newCmd);
                }
            }

            return newCmdSeq;
        }

        private bool SummaryHasPendingAsyncParam => ((ActionProc)enclosingYieldingProc).refinedAction.HasPendingAsyncs;

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

        private void DesugarAsyncCall(CallCmd newCall)
        {
            if (!asyncCallPreconditionCheckers.ContainsKey(newCall.Proc.Name))
            {
                asyncCallPreconditionCheckers[newCall.Proc.Name] = new Procedure(Token.NoToken,
                    $"AsyncCallPreconditionChecker_{newCall.Proc.Name}",
                    newCall.Proc.TypeParameters, newCall.Proc.InParams, newCall.Proc.OutParams,
                    newCall.Proc.Requires, new List<IdentifierExpr>(), new List<Ensures>());
            }

            var asyncCallPreconditionChecker = asyncCallPreconditionCheckers[newCall.Proc.Name];
            CallCmd checkerCallCmd = new CallCmd(newCall.tok, asyncCallPreconditionChecker.Name, newCall.Ins,
                newCall.Outs, newCall.Attributes);
            checkerCallCmd.Proc = asyncCallPreconditionChecker;
            newCmdSeq.Add(checkerCallCmd);
        }
        
        private void CollectPendingAsync(CallCmd call, CallCmd newCall, ActionProc actionProc)
        {
            if (SummaryHasPendingAsyncParam)
            {
                AtomicAction paAction;
                if (actionProc.upperLayer == enclosingYieldingProc.upperLayer)
                    paAction = actionProc.refinedAction;
                else
                    paAction = actionProc.RefinedActionAtLayer(layerNum);

                var pa = ExprHelper.FunctionCall(paAction.pendingAsyncCtor, newCall.Ins.ToArray());
                var inc = Expr.Add(Expr.Select(Expr.Ident(CollectedPAs), pa), Expr.Literal(1));
                var add = CmdHelper.AssignCmd(CollectedPAs, Expr.Store(Expr.Ident(CollectedPAs), pa, inc));
                newCmdSeq.Add(add);
            }
            else
            {
                newCmdSeq.Add(new AssertCmd(call.tok, Expr.False)
                    {ErrorData = "This pending async is not summarized"});
            }
        }

        private void CollectPendingAsyncs(CallCmd call, CallCmd newCall)
        {
            // Inject pending async collection
            if (newCall.Outs.Count != newCall.Proc.OutParams.Count)
            {
                Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count - 1);
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
                    var forallExpr = new ForallExpr(Token.NoToken, new List<Variable> {paBound}, expr);
                    forallExpr.Typecheck(new TypecheckingContext(null));
                    newCmdSeq.Add(new AssertCmd(call.tok, forallExpr)
                        {ErrorData = "Pending asyncs created by this call are not summarized"});
                }
            }
        }
        
        private void ProcessCallCmd(CallCmd call, CallCmd newCall)
        {
            if (civlTypeChecker.procToIntroductionAction.ContainsKey(call.Proc))
            {
                var introductionAction = civlTypeChecker.procToIntroductionAction[call.Proc];
                if (introductionAction.LayerNum == layerNum)
                {
                    InjectGate(introductionAction, newCall);
                    newCmdSeq.Add(newCall);
                }
                return;
            }

            if (civlTypeChecker.procToLemmaProc.ContainsKey(call.Proc))
            {
                if (civlTypeChecker.FindLayers(call.Attributes)[0] == layerNum)
                {
                    newCmdSeq.Add(newCall);
                }
                return;
            }
            
            // handle calls to yielding procedures in the rest of this method
            YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[call.Proc];
            
            if (newCall.IsAsync)
            {
                if (yieldingProc.upperLayer < layerNum)
                {
                    if (call.HasAttribute(CivlAttributes.SYNC))
                    {
                        // synchronize the called atomic action
                        newCall.IsAsync = false;
                        newCmdSeq.Add(newCall);
                    }
                }
                else
                {
                    if (yieldingProc is MoverProc && yieldingProc.upperLayer == layerNum)
                    {
                        // synchronize the called mover procedure
                        newCall.IsAsync = false;
                        newCmdSeq.Add(newCall);
                    }
                    else
                    {
                        DesugarAsyncCall(newCall);
                        if (IsRefinementLayer && yieldingProc is ActionProc actionProc)
                        {
                            CollectPendingAsync(call, newCall, actionProc);
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
                    newCmdSeq.Add(newCall);
                }
                return;
            }

            // handle synchronous calls to mover procedures
            if (yieldingProc is MoverProc)
            {
                newCmdSeq.Add(newCall);
                return;
            }
            
            // handle synchronous calls to action procedures
            {
                Debug.Assert(yieldingProc is ActionProc);
                ActionProc actionProc = (ActionProc)yieldingProc;
                if (actionProc.upperLayer < layerNum)
                {
                    InjectGate(actionProc.RefinedActionAtLayer(layerNum), newCall);
                }
                newCmdSeq.Add(newCall);
                CollectPendingAsyncs(call, newCall);
            }
        }

        private void ProcessParCallCmd(ParCallCmd parCall, ParCallCmd newParCall)
        {
            int maxCalleeLayerNum = parCall.CallCmds.Select(c => civlTypeChecker.procToYieldingProc[c.Proc].upperLayer).Max();

            if (layerNum > maxCalleeLayerNum)
            {
                foreach (var pair in parCall.CallCmds.Zip(newParCall.CallCmds))
                {
                    ProcessCallCmd(pair.Item1, pair.Item2);
                    absyMap[pair.Item2] = parCall;
                }
            }
            else
            {
                List<CallCmd> newCallCmds = new List<CallCmd>();
                foreach (var pair in parCall.CallCmds.Zip(newParCall.CallCmds))
                {
                    YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[pair.Item1.Proc];
                    if (yieldingProc is SkipProc && yieldingProc.upperLayer < layerNum)
                    {
                        continue;
                    }
                    else
                    {
                        newCallCmds.Add(pair.Item2);
                    }
                }
                Debug.Assert(newCallCmds.Count > 0);
                newParCall.CallCmds = newCallCmds;
                newCmdSeq.Add(newParCall);
            }
        }

        // We only have to check the gate of a called atomic action (via an assert) at the creation layer of the caller.
        // In all layers below we just establish invariants which do not require the gates to be checked and we can inject is as an assume.
        private void InjectGate(Action action, CallCmd callCmd)
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
                if (IsRefinementLayer || action is IntroductionAction)
                    newCmdSeq.Add(new AssertCmd(assertCmd.tok, expr)
                        { ErrorData = $"This gate of {action.proc.Name} might not hold." });
                else
                    newCmdSeq.Add(new AssumeCmd(assertCmd.tok, expr));
            }
            newCmdSeq.Add(new CommentCmd("injected gate >>>"));
        }

        public List<Declaration> Collect()
        {
            var decls = new List<Declaration>();
            decls.AddRange(procMap.Values);
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
