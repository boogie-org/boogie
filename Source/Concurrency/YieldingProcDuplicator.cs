using System.Collections.Generic;
using System.Linq;
using System;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public class YieldingProcDuplicator : Duplicator
    {
        private CivlTypeChecker civlTypeChecker;
        private LinearTypeChecker linearTypeChecker;
        private Implementation enclosingImpl;
        private YieldingProc enclosingYieldingProc;

        private int layerNum;
        private Dictionary<Procedure, Procedure> procMap; /* Original -> Duplicate */
        private Dictionary<Absy, Absy> absyMap; /* Duplicate -> Original */
        private Dictionary<Implementation, Implementation> implMap; /* Duplicate -> Original */
        private HashSet<Procedure> yieldingProcs;

        public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, LinearTypeChecker linearTypeChecker, int layerNum)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.layerNum = layerNum;
            this.procMap = new Dictionary<Procedure, Procedure>();
            this.absyMap = new Dictionary<Absy, Absy>();
            this.implMap = new Dictionary<Implementation, Implementation>();
            this.yieldingProcs = new HashSet<Procedure>();
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
                    proc.Modifies = civlTypeChecker.sharedVariableIdentifiers;
                    yieldingProcs.Add(proc);
                }

                procMap[node] = proc;
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

            implMap[newImpl] = impl;
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

        private void ProcessCallCmd(CallCmd call, CallCmd newCall)
        {
            if (civlTypeChecker.procToIntroductionProc.ContainsKey(call.Proc))
            {
                if (!civlTypeChecker.CallExists(call, enclosingYieldingProc.upperLayer, layerNum))
                    return;
            }
            else
            {
                YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[call.Proc];
                if (yieldingProc is SkipProc && yieldingProc.upperLayer < layerNum)
                {
                    return;
                }
                if (newCall.IsAsync)
                {
                    if ((call.HasAttribute(CivlAttributes.SYNC) && yieldingProc.upperLayer < layerNum) ||
                        (yieldingProc is MoverProc && yieldingProc.upperLayer == layerNum))
                    {
                        newCall.IsAsync = false;
                    }

                    if (yieldingProc is ActionProc actionProc && !call.HasAttribute(CivlAttributes.SYNC) && yieldingProc.upperLayer <= layerNum)
                    {
                        if (layerNum != enclosingYieldingProc.upperLayer) return;
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
                            newCmdSeq.Add(new AssertCmd(call.tok, Expr.False) { ErrorData = "This pending async is not summarized" });
                        }
                        return;
                    }
                }

                InjectGate(yieldingProc, newCall);
            }

            newCmdSeq.Add(newCall);

            // Inject pending async collection
            if (newCall.Outs.Count != newCall.Proc.OutParams.Count)
            {
                Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count - 1);
                newCall.Outs.Add(Expr.Ident(ReturnedPAs));
                if (!IsRefinementLayer) return;
                if (SummaryHasPendingAsyncParam)
                {
                    var collectedUnionReturned = ExprHelper.FunctionCall(civlTypeChecker.pendingAsyncAdd, Expr.Ident(CollectedPAs), Expr.Ident(ReturnedPAs));
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
                    newCmdSeq.Add(new AssertCmd(call.tok, forallExpr) { ErrorData = "Pending asyncs created by this call are not summarized" });
                }
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
        private void InjectGate(YieldingProc yieldingProc, CallCmd callCmd)
        {
            if (!(yieldingProc is ActionProc calledActionProc)) return;
            if (calledActionProc.upperLayer >= layerNum) return;
            AtomicAction atomicAction = calledActionProc.RefinedActionAtLayer(layerNum);
            if (atomicAction.gate.Count == 0) return;

            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            for (int i = 0; i < calledActionProc.proc.InParams.Count; i++)
            {
                // Parameters come from the implementation that defines the atomic action
                map[atomicAction.impl.InParams[i]] = callCmd.Ins[i];
            }

            Substitution subst = Substituter.SubstitutionFromHashtable(map);

            // Important: Do not remove CommentCmd!
            // It separates the injected gate from yield assertions in CollectAndDesugarYields.
            newCmdSeq.Add(new CommentCmd("<<< injected gate"));
            foreach (AssertCmd assertCmd in atomicAction.gate)
            {
                if (IsRefinementLayer)
                    newCmdSeq.Add((AssertCmd)Substituter.Apply(subst, assertCmd));
                else
                    newCmdSeq.Add(new AssumeCmd(assertCmd.tok, Substituter.Apply(subst, assertCmd.Expr)));
            }

            newCmdSeq.Add(new CommentCmd("injected gate >>>"));
        }

        public List<Declaration> Collect()
        {
            var decls = new List<Declaration>();
            decls.AddRange(procMap.Values);
            decls.AddRange(implMap.Keys);
            decls.AddRange(YieldingProcInstrumentation.TransformImplementations(
                civlTypeChecker,
                linearTypeChecker,
                layerNum,
                absyMap,
                implMap,
                yieldingProcs));
            return decls;
        }
    }
}
