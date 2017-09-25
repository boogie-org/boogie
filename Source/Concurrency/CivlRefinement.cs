using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
    public class YieldingProcDuplicator : Duplicator
    {
        CivlTypeChecker civlTypeChecker;
        public int layerNum;
        Implementation enclosingImpl;
        public Dictionary<Procedure, Procedure> procMap; /* Original -> Duplicate */
        public Dictionary<Absy, Absy> absyMap; /* Duplicate -> Original */
        public Dictionary<Implementation, Implementation> implMap; /* Duplicate -> Original */
        public HashSet<Procedure> yieldingProcs;

        public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, int layerNum)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.layerNum = layerNum;
            this.enclosingImpl = null;
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

                Procedure proc = (Procedure)node.Clone();
                proc.Name = string.Format("{0}_{1}", node.Name, layerNum);
                proc.InParams = this.VisitVariableSeq(node.InParams);
                proc.OutParams = this.VisitVariableSeq(node.OutParams);
                proc.Requires = this.VisitRequiresSeq(node.Requires);
                proc.Ensures = this.VisitEnsuresSeq(node.Ensures);
                if (yieldingProc is MoverProc && yieldingProc.upperLayer == layerNum)
                {
                    proc.Modifies = ((MoverProc)yieldingProc).modifiedGlobalVars.Select(g => Expr.Ident(g)).ToList();
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

        private Variable dummyLocalVar; // TODO: document purpose of dummy var
        public override Implementation VisitImplementation(Implementation impl)
        {
            enclosingImpl = impl;
            dummyLocalVar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_dummy", Type.Bool));
            Implementation newImpl = base.VisitImplementation(impl);
            newImpl.LocVars.Add(dummyLocalVar);
            newImpl.Name = newImpl.Proc.Name;
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
            AssertCmd assertCmd = (AssertCmd)base.VisitAssertCmd(node);
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                assertCmd.Expr = Expr.True;
            return assertCmd;
        }

        public override Cmd VisitCallCmd(CallCmd call)
        {
            CallCmd newCall = (CallCmd)base.VisitCallCmd(call);
            if (newCall.IsAsync && civlTypeChecker.procToYieldingProc.ContainsKey(call.Proc))
            {
                YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[call.Proc];
                Debug.Assert(yieldingProc.IsLeftMover);
                if (yieldingProc.upperLayer < layerNum || (yieldingProc is MoverProc && yieldingProc.upperLayer== layerNum))
                {
                    newCall.IsAsync = false;
                }
            }
            newCall.Proc = VisitProcedure(newCall.Proc);
            newCall.callee = newCall.Proc.Name;
            absyMap[newCall] = call;
            return newCall;
        }

        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            ParCallCmd parCallCmd = (ParCallCmd)base.VisitParCallCmd(node);
            absyMap[parCallCmd] = node;
            return parCallCmd;
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> cmds = base.VisitCmdSeq(cmdSeq);
            List<Cmd> newCmds = new List<Cmd>();
            for (int i = 0; i < cmds.Count; i++)
            {
                Cmd originalCmd = cmdSeq[i];
                Cmd cmd = cmds[i];

                if (originalCmd is CallCmd)
                {
                    ProcessCallCmd((CallCmd)originalCmd, (CallCmd)cmd, newCmds);
                }
                else if (originalCmd is ParCallCmd)
                {
                    ProcessParCallCmd((ParCallCmd)originalCmd, (ParCallCmd)cmd, newCmds);
                }
                else
                {
                    newCmds.Add(cmd);
                }
            }
            return newCmds;
        }

        private void ProcessCallCmd(CallCmd originalCallCmd, CallCmd callCmd, List<Cmd> newCmds)
        {
            int enclosingProcLayerNum = civlTypeChecker.procToActionInfo[enclosingImpl.Proc].createdAtLayerNum;
            Procedure originalProc = originalCallCmd.Proc;

            if (civlTypeChecker.procToAtomicProcedureInfo.ContainsKey(originalProc))
            {
                if (civlTypeChecker.CallExists(originalCallCmd, enclosingProcLayerNum, layerNum))
                {
                    newCmds.Add(callCmd);
                }
            }
            else if (civlTypeChecker.procToActionInfo.ContainsKey(originalProc))
            {
                AtomicActionInfo atomicActionInfo = civlTypeChecker.procToActionInfo[originalProc] as AtomicActionInfo;
                // We only have to check the gate of a called atomic action (via an assert) at the creation layer of the caller.
                // In all layers below we just establish invariants which do not require the gates to be checked.
                if (atomicActionInfo != null && atomicActionInfo.gate.Count > 0 && layerNum == enclosingProcLayerNum)
                {
                    newCmds.Add(new HavocCmd(Token.NoToken, new List<IdentifierExpr> { Expr.Ident(dummyLocalVar) }));
                    Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                    for (int i = 0; i < originalProc.InParams.Count; i++)
                    {
                        map[originalProc.InParams[i]] = callCmd.Ins[i];
                    }
                    Substitution subst = Substituter.SubstitutionFromHashtable(map);
                    foreach (AssertCmd assertCmd in atomicActionInfo.gate)
                    {
                        newCmds.Add(Substituter.Apply(subst, assertCmd));
                    }
                }
                newCmds.Add(callCmd);
            }
            else
            {
                Debug.Assert(false);
            }
        }

        private void ProcessParCallCmd(ParCallCmd originalParCallCmd, ParCallCmd parCallCmd, List<Cmd> newCmds)
        {
            int maxCalleeLayerNum = 0;
            foreach (CallCmd iter in originalParCallCmd.CallCmds)
            {
                int calleeLayerNum = civlTypeChecker.procToActionInfo[iter.Proc].createdAtLayerNum;
                if (calleeLayerNum > maxCalleeLayerNum)
                    maxCalleeLayerNum = calleeLayerNum;
            }
            if (layerNum > maxCalleeLayerNum)
            {
                for (int i = 0; i < parCallCmd.CallCmds.Count; i++)
                {
                    ProcessCallCmd(originalParCallCmd.CallCmds[i], parCallCmd.CallCmds[i], newCmds);
                    absyMap[parCallCmd.CallCmds[i]] = originalParCallCmd;
                }
            }
            else
            {
                newCmds.Add(parCallCmd);
            }
        }
    }

    public class CivlRefinement
    {
        LinearTypeChecker linearTypeChecker;
        CivlTypeChecker civlTypeChecker;
        Dictionary<Absy, Absy> absyMap;
        Dictionary<Implementation, Implementation> implMap;
        HashSet<Procedure> yieldingProcs;
        int layerNum;
        Dictionary<string, Procedure> asyncAndParallelCallDesugarings;
        List<Procedure> yieldCheckerProcs;
        List<Implementation> yieldCheckerImpls;
        Procedure yieldProc;

        Variable pc;
        Variable ok;
        Expr alpha;
        Expr beta;
        HashSet<Variable> frame;

        private CivlRefinement(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, YieldingProcDuplicator duplicator)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.civlTypeChecker = civlTypeChecker;
            this.absyMap = duplicator.absyMap;
            this.layerNum = duplicator.layerNum;
            this.implMap = duplicator.implMap;
            this.yieldingProcs = duplicator.yieldingProcs;

            asyncAndParallelCallDesugarings = new Dictionary<string, Procedure>();
            yieldCheckerProcs = new List<Procedure>();
            yieldCheckerImpls = new List<Implementation>();
            yieldProc = null;
        }

        private Formal OgOldGlobalFormal(Variable v)
        { return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", v.Name), v.TypedIdent.Type), true); }

        private LocalVariable OgOldGlobalLocal(Variable v)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", v.Name), v.TypedIdent.Type)); }

        private LocalVariable OgOldLocalLocal(Variable v)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_local_old_{0}", v.Name), v.TypedIdent.Type)); }

        private LocalVariable OgOldLocal(Variable v)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_old_{0}", v.Name), v.TypedIdent.Type)); }

        private LocalVariable OgPcLocal()
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_pc", Type.Bool)); }

        private LocalVariable OgPcLabelLocal(string label)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_pc_{0}", label), Type.Bool)); }

        private LocalVariable OgOkLocal()
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_ok", Type.Bool)); }

        private LocalVariable OgOkLabelLocal(string label)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_ok_{0}", label), Type.Bool)); }

        private Formal OgParCallDesugarFormal(Variable v, int count, bool incoming)
        { return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_{0}_{1}", count, v.Name), v.TypedIdent.Type), incoming); }

        private LocalVariable CopyLocal(Variable v)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type)); }

        private Formal CopyIn(Variable v)
        { return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type), true); }

        private IEnumerable<Variable> AvailableLinearVars(Absy absy)
        {
            HashSet<Variable> availableVars = new HashSet<Variable>(linearTypeChecker.AvailableLinearVars(absyMap[absy]));
            foreach (var g in civlTypeChecker.globalVarToLayerRange.Keys)
            {
                SharedVariableInfo info = civlTypeChecker.globalVarToLayerRange[g];
                if (!(info.introLayerNum <= layerNum && layerNum <= info.hideLayerNum))
                {
                    availableVars.Remove(g);
                }
            }
            foreach (var v in civlTypeChecker.localVarToIntroLayer.Keys)
            {
                LocalVariableInfo info = civlTypeChecker.localVarToIntroLayer[v];
                if (layerNum < info.layer)
                {
                    availableVars.Remove(v);
                }
            }
            return availableVars;
        }

        private Dictionary<string, Expr> ComputeAvailableExprs(IEnumerable<Variable> availableLinearVars)
        {
            Dictionary<string, Expr> domainNameToExpr = new Dictionary<string, Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                var domain = linearTypeChecker.linearDomains[domainName];
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new Expr[] { Expr.False });
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }
            foreach (Variable v in availableLinearVars)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                var domain = linearTypeChecker.linearDomains[domainName];
                if (!domain.collectors.ContainsKey(v.TypedIdent.Type)) continue;
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]), new List<Expr> { Expr.Ident(v) });
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new List<Expr> { ie, domainNameToExpr[domainName] });
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }
            return domainNameToExpr;
        }

        private void TransformImpl(Implementation impl)
        {
            HashSet<Block> yieldingHeaders;
            Graph<Block> graph = ComputeYieldingLoopHeaders(impl, out yieldingHeaders);

            List<Variable> newLocalVars;
            Dictionary<string, Variable> domainNameToLocalVar;
            Dictionary<Variable, Variable> ogOldGlobalMap;
            SetupRefinementCheck(impl, out newLocalVars, out domainNameToLocalVar, out ogOldGlobalMap);

            List<List<Cmd>> yields = CollectAndDesugarYields(impl, domainNameToLocalVar, ogOldGlobalMap);

            List<Variable> oldPcs, oldOks;
            ProcessLoopHeaders(impl, graph, yieldingHeaders, domainNameToLocalVar, ogOldGlobalMap, out oldPcs, out oldOks);

            AddInitialBlock(impl, oldPcs, oldOks, domainNameToLocalVar, ogOldGlobalMap);

            CreateYieldCheckerImpl(impl, yields);

            impl.LocVars.AddRange(newLocalVars);
            impl.LocVars.AddRange(oldPcs);
            impl.LocVars.AddRange(oldOks);

            UnifyCallsToYieldProc(impl, ogOldGlobalMap, domainNameToLocalVar);
        }

        private Graph<Block> ComputeYieldingLoopHeaders(Implementation impl, out HashSet<Block> yieldingHeaders)
        {
            Graph<Block> graph;
            impl.PruneUnreachableBlocks();
            impl.ComputePredecessorsForBlocks();
            graph = Program.GraphFromImpl(impl);
            graph.ComputeLoops();
            if (!graph.Reducible)
            {
                throw new Exception("Irreducible flow graphs are unsupported.");
            }
            yieldingHeaders = new HashSet<Block>();
            IEnumerable<Block> sortedHeaders = graph.SortHeadersByDominance();
            foreach (Block header in sortedHeaders)
            {
                if (yieldingHeaders.Any(x => graph.DominatorMap.DominatedBy(x, header)))
                {
                    yieldingHeaders.Add(header);
                }
                else if (IsYieldingHeader(graph, header))
                {
                    yieldingHeaders.Add(header);
                }
                else
                {
                    continue;
                }
            }
            return graph;
        }

        private bool IsYieldingHeader(Graph<Block> graph, Block header)
        {
            foreach (Block backEdgeNode in graph.BackEdgeNodes(header))
            {
                foreach (Block x in graph.NaturalLoops(header, backEdgeNode))
                {
                    foreach (Cmd cmd in x.Cmds)
                    {
                        if (cmd is YieldCmd)
                            return true;
                        if (cmd is ParCallCmd)
                            return true;
                        CallCmd callCmd = cmd as CallCmd;
                        if (callCmd == null) continue;
                        if (yieldingProcs.Contains(callCmd.Proc))
                            return true;
                    }
                }
            }
            return false;
        }

        private void SetupRefinementCheck(
            Implementation impl,
            out List<Variable> newLocalVars,
            out Dictionary<string, Variable> domainNameToLocalVar,
            out Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            pc = null;
            ok = null;
            alpha = null;
            beta = null;
            frame = null;

            newLocalVars = new List<Variable>();
            ogOldGlobalMap = new Dictionary<Variable, Variable>();
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                LocalVariable l = OgOldGlobalLocal(g);
                ogOldGlobalMap[g] = l;
                newLocalVars.Add(l);
            }

            Procedure originalProc = implMap[impl].Proc;
            ActionInfo actionInfo = civlTypeChecker.procToActionInfo[originalProc];
            if (actionInfo.createdAtLayerNum == this.layerNum)
            {
                pc = OgPcLocal();
                ok = OgOkLocal();
                newLocalVars.Add(pc);
                newLocalVars.Add(ok);
                Dictionary<Variable, Expr> alwaysMap = new Dictionary<Variable, Expr>();
                for (int i = 0; i < originalProc.InParams.Count; i++)
                {
                    alwaysMap[originalProc.InParams[i]] = Expr.Ident(impl.InParams[i]);
                }
                for (int i = 0; i < originalProc.OutParams.Count; i++)
                {
                    alwaysMap[originalProc.OutParams[i]] = Expr.Ident(impl.OutParams[i]);
                }
                Substitution always = Substituter.SubstitutionFromHashtable(alwaysMap);
                Dictionary<Variable, Expr> foroldMap = new Dictionary<Variable, Expr>();
                foreach (Variable g in civlTypeChecker.sharedVariables)
                {
                    foroldMap[g] = Expr.Ident(ogOldGlobalMap[g]);
                }
                Substitution forold = Substituter.SubstitutionFromHashtable(foroldMap);
                frame = new HashSet<Variable>(civlTypeChecker.sharedVariables);
                foreach (Variable v in civlTypeChecker.sharedVariables)
                {
                    if (civlTypeChecker.globalVarToLayerRange[v].hideLayerNum <= actionInfo.createdAtLayerNum ||
                        civlTypeChecker.globalVarToLayerRange[v].introLayerNum > actionInfo.createdAtLayerNum)
                    {
                        frame.Remove(v);
                    }
                }
                AtomicActionInfo atomicActionInfo = actionInfo as AtomicActionInfo;
                if (atomicActionInfo == null)
                {
                    beta = Expr.True;
                    foreach (var v in frame)
                    {
                        beta = Expr.And(beta, Expr.Eq(Expr.Ident(v), foroldMap[v]));
                    }
                    alpha = Expr.True;
                }
                else
                {
                    Expr betaExpr = (new TransitionRelationComputation(civlTypeChecker.program, atomicActionInfo, frame, new HashSet<Variable>())).TransitionRelationCompute(true);
                    beta = Substituter.ApplyReplacingOldExprs(always, forold, betaExpr);
                    Expr alphaExpr = Expr.And(atomicActionInfo.gate.Select(g => g.Expr));
                    alphaExpr.Type = Type.Bool;
                    alpha = Substituter.Apply(always, alphaExpr);
                }
                foreach (Variable f in impl.OutParams)
                {
                    LocalVariable copy = OgOldLocal(f);
                    newLocalVars.Add(copy);
                    ogOldGlobalMap[f] = copy;
                }
            }

            domainNameToLocalVar = new Dictionary<string, Variable>();
            {
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable l = linearTypeChecker.LinearDomainInLocal(domainName);
                    domainNameToLocalVar[domainName] = l;
                    newLocalVars.Add(l);
                }
            }
        }

        private List<List<Cmd>> CollectAndDesugarYields(Implementation impl,
            Dictionary<string, Variable> domainNameToLocalVar, Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            // Collect the yield predicates and desugar yields
            List<List<Cmd>> yields = new List<List<Cmd>>();
            List<Cmd> cmds = new List<Cmd>();
            foreach (Block b in impl.Blocks)
            {
                YieldCmd yieldCmd = null;
                List<Cmd> newCmds = new List<Cmd>();
                for (int i = 0; i < b.Cmds.Count; i++)
                {
                    Cmd cmd = b.Cmds[i];
                    if (cmd is YieldCmd)
                    {
                        yieldCmd = (YieldCmd)cmd;
                        continue;
                    }
                    if (yieldCmd != null)
                    {
                        PredicateCmd pcmd = cmd as PredicateCmd;
                        if (pcmd == null)
                        {
                            DesugarYield(yieldCmd, cmds, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                            if (cmds.Count > 0)
                            {
                                yields.Add(cmds);
                                cmds = new List<Cmd>();
                            }
                            yieldCmd = null;
                        }
                        else
                        {
                            cmds.Add(pcmd);
                        }
                    }

                    if (cmd is CallCmd)
                    {
                        CallCmd callCmd = cmd as CallCmd;
                        if (yieldingProcs.Contains(callCmd.Proc))
                        {
                            AddCallToYieldProc(callCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                        }
                        if (callCmd.IsAsync)
                        {
                            if (!asyncAndParallelCallDesugarings.ContainsKey(callCmd.Proc.Name))
                            {
                                asyncAndParallelCallDesugarings[callCmd.Proc.Name] = new Procedure(Token.NoToken, string.Format("DummyAsyncTarget_{0}", callCmd.Proc.Name), callCmd.Proc.TypeParameters, callCmd.Proc.InParams, callCmd.Proc.OutParams, callCmd.Proc.Requires, new List<IdentifierExpr>(), new List<Ensures>());
                            }
                            var dummyAsyncTargetProc = asyncAndParallelCallDesugarings[callCmd.Proc.Name];
                            CallCmd dummyCallCmd = new CallCmd(callCmd.tok, dummyAsyncTargetProc.Name, callCmd.Ins, callCmd.Outs, callCmd.Attributes);
                            dummyCallCmd.Proc = dummyAsyncTargetProc;
                            newCmds.Add(dummyCallCmd);
                        }
                        else
                        {
                            newCmds.Add(callCmd);
                        }
                        if (yieldingProcs.Contains(callCmd.Proc))
                        {
                            HashSet<Variable> availableLinearVars = new HashSet<Variable>(AvailableLinearVars(callCmd));

                            if (!callCmd.IsAsync && civlTypeChecker.sharedVariables.Count > 0 && pc != null)
                            {
                                // assume pc || alpha(i, g);
                                Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
                                assumeExpr.Type = Type.Bool;
                                newCmds.Add(new AssumeCmd(Token.NoToken, assumeExpr));
                            }

                            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(availableLinearVars);
                            AddUpdatesToOldGlobalVars(newCmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);
                        }
                    }
                    else if (cmd is ParCallCmd)
                    {
                        ParCallCmd parCallCmd = cmd as ParCallCmd;
                        AddCallToYieldProc(parCallCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                        DesugarParallelCallCmd(newCmds, parCallCmd);
                        HashSet<Variable> availableLinearVars = new HashSet<Variable>(AvailableLinearVars(parCallCmd));

                        if (civlTypeChecker.sharedVariables.Count > 0 && pc != null)
                        {
                            // assume pc || alpha(i, g);
                            Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
                            assumeExpr.Type = Type.Bool;
                            newCmds.Add(new AssumeCmd(Token.NoToken, assumeExpr));
                        }

                        Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(availableLinearVars);
                        AddUpdatesToOldGlobalVars(newCmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);
                    }
                    else
                    {
                        newCmds.Add(cmd);
                    }
                }
                if (yieldCmd != null)
                {
                    DesugarYield(yieldCmd, cmds, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                    if (cmds.Count > 0)
                    {
                        yields.Add(cmds);
                        cmds = new List<Cmd>();
                    }
                }
                if (b.TransferCmd is ReturnCmd)
                {
                    AddCallToYieldProc(b.TransferCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                    if (pc != null)
                    {
                        AssertCmd assertCmd = new AssertCmd(b.TransferCmd.tok, Expr.Ident(ok));
                        assertCmd.ErrorData = "Failed to execute atomic action before procedure return";
                        newCmds.Add(assertCmd);
                    }
                }
                b.Cmds = newCmds;
            }
            return yields;
        }

        private CallCmd CallToYieldProc(IToken tok, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar)
        {
            List<Expr> exprSeq = new List<Expr>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                exprSeq.Add(Expr.Ident(domainNameToLocalVar[domainName]));
            }
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                exprSeq.Add(Expr.Ident(ogOldGlobalMap[g]));
            }
            if (yieldProc == null)
            {
                List<Variable> inputs = new List<Variable>();
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    inputs.Add(linearTypeChecker.LinearDomainInFormal(domainName));
                }
                foreach (Variable g in civlTypeChecker.sharedVariables)
                {
                    inputs.Add(OgOldGlobalFormal(g));
                }
                yieldProc = new Procedure(Token.NoToken, string.Format("og_yield_{0}", layerNum), new List<TypeVariable>(), inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
                yieldProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            }
            CallCmd yieldCallCmd = new CallCmd(Token.NoToken, yieldProc.Name, exprSeq, new List<IdentifierExpr>());
            yieldCallCmd.Proc = yieldProc;
            return yieldCallCmd;
        }

        private void AddCallToYieldProc(IToken tok, List<Cmd> newCmds, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar)
        {
            if (!CommandLineOptions.Clo.TrustNonInterference)
            {
                CallCmd yieldCallCmd = CallToYieldProc(tok, ogOldGlobalMap, domainNameToLocalVar);
                newCmds.Add(yieldCallCmd);
            }

            if (pc != null)
            {
                Expr aa = OldEqualityExprForGlobals(ogOldGlobalMap);
                Expr bb = OldEqualityExpr(ogOldGlobalMap);

                // assert pc || g_old == g || beta(i, g_old, o, g);
                Expr assertExpr = Expr.Or(Expr.Ident(pc), Expr.Or(aa, beta));
                assertExpr.Typecheck(new TypecheckingContext(null));
                AssertCmd skipOrBetaAssertCmd = new AssertCmd(tok, assertExpr);
                skipOrBetaAssertCmd.ErrorData = "Transition invariant in initial state violated";
                newCmds.Add(skipOrBetaAssertCmd);

                // assert pc ==> o_old == o && g_old == g;
                assertExpr = Expr.Imp(Expr.Ident(pc), bb);
                assertExpr.Typecheck(new TypecheckingContext(null));
                AssertCmd skipAssertCmd = new AssertCmd(tok, assertExpr);
                skipAssertCmd.ErrorData = "Transition invariant in final state violated";
                newCmds.Add(skipAssertCmd);

                // pc, ok := g_old == g ==> pc, ok || beta(i, g_old, o, g);
                List<AssignLhs> pcUpdateLHS = new List<AssignLhs> {
                        new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)),
                        new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok))
                    };
                List<Expr> pcUpdateRHS = new List<Expr>(
                    new Expr[] {
                        Expr.Imp(aa, Expr.Ident(pc)),
                        Expr.Or(Expr.Ident(ok), beta)
                    });
                foreach (Expr e in pcUpdateRHS)
                {
                    e.Typecheck(new TypecheckingContext(null));
                }
                newCmds.Add(new AssignCmd(Token.NoToken, pcUpdateLHS, pcUpdateRHS));
            }
        }

        private Expr OldEqualityExpr(Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            Expr bb = Expr.True;
            foreach (Variable o in ogOldGlobalMap.Keys)
            {
                if (o is GlobalVariable && !frame.Contains(o)) continue;
                bb = Expr.And(bb, Expr.Eq(Expr.Ident(o), Expr.Ident(ogOldGlobalMap[o])));
                bb.Type = Type.Bool;
            }
            return bb;
        }

        private Expr OldEqualityExprForGlobals(Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            Expr bb = Expr.True;
            foreach (Variable o in ogOldGlobalMap.Keys)
            {
                if (o is GlobalVariable && frame.Contains(o))
                {
                    bb = Expr.And(bb, Expr.Eq(Expr.Ident(o), Expr.Ident(ogOldGlobalMap[o])));
                    bb.Type = Type.Bool;
                }
            }
            return bb;
        }

        private void DesugarYield(YieldCmd yieldCmd, List<Cmd> cmds, List<Cmd> newCmds, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar)
        {
            AddCallToYieldProc(yieldCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);

            if (civlTypeChecker.sharedVariableIdentifiers.Count > 0)
            {
                newCmds.Add(new HavocCmd(Token.NoToken, civlTypeChecker.sharedVariableIdentifiers));
                if (pc != null)
                {
                    // assume pc || alpha(i, g);
                    Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
                    assumeExpr.Type = Type.Bool;
                    newCmds.Add(new AssumeCmd(Token.NoToken, assumeExpr));
                }
            }

            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(AvailableLinearVars(yieldCmd));
            AddUpdatesToOldGlobalVars(newCmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);

            for (int j = 0; j < cmds.Count; j++)
            {
                PredicateCmd predCmd = (PredicateCmd)cmds[j];
                newCmds.Add(new AssumeCmd(Token.NoToken, predCmd.Expr));
            }
        }

        private void AddUpdatesToOldGlobalVars(List<Cmd> newCmds, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar, Dictionary<string, Expr> domainNameToExpr)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(domainNameToLocalVar[domainName])));
                rhss.Add(domainNameToExpr[domainName]);
            }
            foreach (Variable g in ogOldGlobalMap.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(ogOldGlobalMap[g])));
                rhss.Add(Expr.Ident(g));
            }
            if (lhss.Count > 0)
            {
                newCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }
        }

        public void DesugarParallelCallCmd(List<Cmd> newCmds, ParCallCmd parCallCmd)
        {
            List<string> parallelCalleeNames = new List<string>();
            List<Expr> ins = new List<Expr>();
            List<IdentifierExpr> outs = new List<IdentifierExpr>();
            string procName = "og";
            foreach (CallCmd callCmd in parCallCmd.CallCmds)
            {
                procName = procName + "_" + callCmd.Proc.Name;
                ins.AddRange(callCmd.Ins);
                outs.AddRange(callCmd.Outs);
            }
            Procedure proc;
            if (asyncAndParallelCallDesugarings.ContainsKey(procName))
            {
                proc = asyncAndParallelCallDesugarings[procName];
            }
            else
            {
                List<Variable> inParams = new List<Variable>();
                List<Variable> outParams = new List<Variable>();
                List<Requires> requiresSeq = new List<Requires>();
                List<Ensures> ensuresSeq = new List<Ensures>();
                int count = 0;
                foreach (CallCmd callCmd in parCallCmd.CallCmds)
                {
                    Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                    foreach (Variable x in callCmd.Proc.InParams)
                    {
                        Variable y = OgParCallDesugarFormal(x, count, true);
                        inParams.Add(y);
                        map[x] = Expr.Ident(y);
                    }
                    foreach (Variable x in callCmd.Proc.OutParams)
                    {
                        Variable y = OgParCallDesugarFormal(x, count, false);
                        outParams.Add(y);
                        map[x] = Expr.Ident(y);
                    }
                    Contract.Assume(callCmd.Proc.TypeParameters.Count == 0);
                    Substitution subst = Substituter.SubstitutionFromHashtable(map);
                    foreach (Requires req in callCmd.Proc.Requires)
                    {
                        requiresSeq.Add(new Requires(req.tok, req.Free, Substituter.Apply(subst, req.Condition), null, req.Attributes));
                    }
                    foreach (Ensures ens in callCmd.Proc.Ensures)
                    {
                        ensuresSeq.Add(new Ensures(ens.tok, ens.Free, Substituter.Apply(subst, ens.Condition), null, ens.Attributes));
                    }
                    count++;
                }
                proc = new Procedure(Token.NoToken, procName, new List<TypeVariable>(), inParams, outParams, requiresSeq, civlTypeChecker.sharedVariableIdentifiers, ensuresSeq);
                asyncAndParallelCallDesugarings[procName] = proc;
            }
            CallCmd dummyCallCmd = new CallCmd(parCallCmd.tok, proc.Name, ins, outs, parCallCmd.Attributes);
            dummyCallCmd.Proc = proc;
            newCmds.Add(dummyCallCmd);
        }

        private void ProcessLoopHeaders(Implementation impl, Graph<Block> graph, HashSet<Block> yieldingHeaders,
            Dictionary<string, Variable> domainNameToLocalVar, Dictionary<Variable, Variable> ogOldGlobalMap,
            out List<Variable> oldPcs, out List<Variable> oldOks)
        {
            oldPcs = new List<Variable>();
            oldOks = new List<Variable>();
            foreach (Block header in yieldingHeaders)
            {
                LocalVariable oldPc = null;
                LocalVariable oldOk = null;
                if (pc != null)
                {
                    oldPc = OgPcLabelLocal(header.Label);
                    oldOk = OgOkLabelLocal(header.Label);
                    oldPcs.Add(oldPc);
                    oldOks.Add(oldOk);
                }
                Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(AvailableLinearVars(header));
                foreach (Block pred in header.Predecessors)
                {
                    AddCallToYieldProc(header.tok, pred.Cmds, ogOldGlobalMap, domainNameToLocalVar);
                    if (pc != null && !graph.BackEdgeNodes(header).Contains(pred))
                    {
                        pred.Cmds.Add(new AssignCmd(Token.NoToken,
                            new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldPc)), new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldOk)) },
                            new List<Expr> { Expr.Ident(pc), Expr.Ident(ok) }));
                    }
                    AddUpdatesToOldGlobalVars(pred.Cmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);
                }
                List<Cmd> newCmds = new List<Cmd>();
                if (pc != null)
                {
                    AssertCmd assertCmd;
                    assertCmd = new AssertCmd(header.tok, Expr.Eq(Expr.Ident(oldPc), Expr.Ident(pc)));
                    assertCmd.ErrorData = "Specification state must not change for transitions ending in loop headers";
                    newCmds.Add(assertCmd);
                    assertCmd = new AssertCmd(header.tok, Expr.Imp(Expr.Ident(oldOk), Expr.Ident(ok)));
                    assertCmd.ErrorData = "Specification state must not change for transitions ending in loop headers";
                    newCmds.Add(assertCmd);
                }
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Eq(Expr.Ident(domainNameToLocalVar[domainName]), domainNameToExpr[domainName])));
                }
                foreach (Variable v in ogOldGlobalMap.Keys)
                {
                    newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Eq(Expr.Ident(v), Expr.Ident(ogOldGlobalMap[v]))));
                }
                newCmds.AddRange(header.Cmds);
                header.Cmds = newCmds;
            }
        }

        private void AddInitialBlock(Implementation impl, List<Variable> oldPcs, List<Variable> oldOks,
            Dictionary<string, Variable> domainNameToLocalVar, Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            // Add initial block
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            if (pc != null)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)));
                rhss.Add(Expr.False);
                foreach (Variable oldPc in oldPcs)
                {
                    lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldPc)));
                    rhss.Add(Expr.False);
                }
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok)));
                rhss.Add(Expr.False);
                foreach (Variable oldOk in oldOks)
                {
                    lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldOk)));
                    rhss.Add(Expr.False);
                }
            }
            Dictionary<string, Expr> domainNameToExpr = new Dictionary<string, Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                var domain = linearTypeChecker.linearDomains[domainName];
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new Expr[] { Expr.False });
                domainNameToExpr[domainName] = expr;
            }
            for (int i = 0; i < impl.InParams.Count - linearTypeChecker.linearDomains.Count; i++)
            {
                Variable v = impl.InParams[i];
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
                if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                var domain = linearTypeChecker.linearDomains[domainName];
                if (!domain.collectors.ContainsKey(v.TypedIdent.Type)) continue;
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]), new List<Expr> { Expr.Ident(v) });
                domainNameToExpr[domainName] = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new List<Expr> { ie, domainNameToExpr[domainName] });
            }
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(domainNameToLocalVar[domainName])));
                rhss.Add(domainNameToExpr[domainName]);
            }
            foreach (Variable g in ogOldGlobalMap.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(ogOldGlobalMap[g])));
                rhss.Add(Expr.Ident(g));
            }
            if (lhss.Count > 0)
            {
                Block initBlock = new Block(Token.NoToken, "og_init", new List<Cmd> { new AssignCmd(Token.NoToken, lhss, rhss) }, new GotoCmd(Token.NoToken, new List<String> { impl.Blocks[0].Label }, new List<Block> { impl.Blocks[0] }));
                impl.Blocks.Insert(0, initBlock);
            }
        }

        private void CreateYieldCheckerImpl(Implementation impl, List<List<Cmd>> yields)
        {
            if (yields.Count == 0) return;

            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            List<Variable> locals = new List<Variable>();
            List<Variable> inputs = new List<Variable>();

            foreach (Variable local in impl.LocVars)
            {
                var copy = CopyLocal(local);
                locals.Add(copy);
                map[local] = Expr.Ident(copy);
            }
            for (int i = 0; i < impl.InParams.Count; i++)
            {
                Variable inParam = impl.InParams[i];
                Variable copy;
                if (i < impl.InParams.Count - linearTypeChecker.linearDomains.Count)
                {
                    copy = CopyLocal(inParam);
                    locals.Add(copy);
                }
                else
                {
                    copy = CopyIn(inParam);
                    inputs.Add(copy);
                }
                map[impl.InParams[i]] = Expr.Ident(copy);
            }
            for (int i = 0; i < impl.OutParams.Count; i++)
            {
                Variable outParam = impl.OutParams[i];
                var copy = CopyLocal(outParam);
                locals.Add(copy);
                map[impl.OutParams[i]] = Expr.Ident(copy);
            }
            Dictionary<Variable, Expr> ogOldLocalMap = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> assumeMap = new Dictionary<Variable, Expr>(map);
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                var copy = OgOldLocalLocal(g);
                locals.Add(copy);
                ogOldLocalMap[g] = Expr.Ident(copy);
                Formal f = OgOldGlobalFormal(g);
                inputs.Add(f);
                assumeMap[g] = Expr.Ident(f);
            }

            Substitution assumeSubst = Substituter.SubstitutionFromHashtable(assumeMap);
            Substitution oldSubst = Substituter.SubstitutionFromHashtable(ogOldLocalMap);
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            List<Block> yieldCheckerBlocks = new List<Block>();
            List<String> labels = new List<String>();
            List<Block> labelTargets = new List<Block>();
            Block yieldCheckerBlock = new Block(Token.NoToken, "exit", new List<Cmd>(), new ReturnCmd(Token.NoToken));
            labels.Add(yieldCheckerBlock.Label);
            labelTargets.Add(yieldCheckerBlock);
            yieldCheckerBlocks.Add(yieldCheckerBlock);
            int yieldCount = 0;
            foreach (List<Cmd> cs in yields)
            {
                List<Cmd> newCmds = new List<Cmd>();
                foreach (Cmd cmd in cs)
                {
                    PredicateCmd predCmd = (PredicateCmd)cmd;
                    newCmds.Add(new AssumeCmd(Token.NoToken, Substituter.ApplyReplacingOldExprs(assumeSubst, oldSubst, predCmd.Expr)));
                }
                foreach (Cmd cmd in cs)
                {
                    PredicateCmd predCmd = (PredicateCmd)cmd;
                    var newExpr = Substituter.ApplyReplacingOldExprs(subst, oldSubst, predCmd.Expr);
                    if (predCmd is AssertCmd)
                    {
                        AssertCmd assertCmd = new AssertCmd(predCmd.tok, newExpr, predCmd.Attributes);
                        assertCmd.ErrorData = "Non-interference check failed";
                        newCmds.Add(assertCmd);
                    }
                    /*
                    Disjointness assumes injected by LinearTypeChecker are dropped now because the 
                    previous loop has already subsituted the old global state in these assumes.
                    It would be unsound to have these assumes on the current global state.
                    */
                }
                newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                yieldCheckerBlock = new Block(Token.NoToken, "L" + yieldCount++, newCmds, new ReturnCmd(Token.NoToken));
                labels.Add(yieldCheckerBlock.Label);
                labelTargets.Add(yieldCheckerBlock);
                yieldCheckerBlocks.Add(yieldCheckerBlock);
            }
            yieldCheckerBlocks.Insert(0, new Block(Token.NoToken, "enter", new List<Cmd>(), new GotoCmd(Token.NoToken, labels, labelTargets)));

            // Create the yield checker procedure
            var yieldCheckerName = string.Format("Impl_YieldChecker_{0}", impl.Name);
            var yieldCheckerProc = new Procedure(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            yieldCheckerProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            yieldCheckerProcs.Add(yieldCheckerProc);

            // Create the yield checker implementation
            var yieldCheckerImpl = new Implementation(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs, new List<Variable>(), locals, yieldCheckerBlocks);
            yieldCheckerImpl.Proc = yieldCheckerProc;
            yieldCheckerImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            yieldCheckerImpls.Add(yieldCheckerImpl);
        }

        private void UnifyCallsToYieldProc(Implementation impl, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar)
        {
            CallCmd yieldCallCmd = CallToYieldProc(Token.NoToken, ogOldGlobalMap, domainNameToLocalVar);
            Block yieldCheckBlock = new Block(Token.NoToken, "CallToYieldProc", new List<Cmd> { yieldCallCmd, new AssumeCmd(Token.NoToken, Expr.False) }, new ReturnCmd(Token.NoToken));
            List<Block> newBlocks = new List<Block>();
            foreach (Block b in impl.Blocks)
            {
                TransferCmd transferCmd = b.TransferCmd;
                List<Cmd> newCmds = new List<Cmd>();
                for (int i = b.Cmds.Count - 1; i >= 0; i--)
                {
                    CallCmd callCmd = b.Cmds[i] as CallCmd;
                    if (callCmd == null || callCmd.Proc != yieldProc)
                    {
                        newCmds.Insert(0, b.Cmds[i]);
                    }
                    else
                    {
                        Block newBlock = new Block(Token.NoToken, b.Label + i, newCmds, transferCmd);
                        newCmds = new List<Cmd>();
                        transferCmd = new GotoCmd(Token.NoToken, new List<string> { newBlock.Label, yieldCheckBlock.Label },
                                                                 new List<Block> { newBlock, yieldCheckBlock });
                        newBlocks.Add(newBlock);
                    }
                }
                b.Cmds = newCmds;
                b.TransferCmd = transferCmd;
            }
            impl.Blocks.AddRange(newBlocks);
            impl.Blocks.Add(yieldCheckBlock);
        }

        private void AddYieldProcAndImpl(List<Declaration> decls)
        {
            if (yieldProc == null) return;

            Program program = linearTypeChecker.program;
            List<Variable> inputs = new List<Variable>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                inputs.Add(linearTypeChecker.LinearDomainInFormal(domainName));
            }
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                inputs.Add(OgOldGlobalFormal(g));
            }
            List<Block> blocks = new List<Block>();
            TransferCmd transferCmd = new ReturnCmd(Token.NoToken);
            if (yieldCheckerProcs.Count > 0)
            {
                List<Block> blockTargets = new List<Block>();
                List<String> labelTargets = new List<String>();
                int labelCount = 0;
                foreach (Procedure proc in yieldCheckerProcs)
                {
                    List<Expr> exprSeq = new List<Expr>();
                    foreach (Variable v in inputs)
                    {
                        exprSeq.Add(Expr.Ident(v));
                    }
                    CallCmd callCmd = new CallCmd(Token.NoToken, proc.Name, exprSeq, new List<IdentifierExpr>());
                    callCmd.Proc = proc;
                    string label = string.Format("L_{0}", labelCount++);
                    Block block = new Block(Token.NoToken, label, new List<Cmd> { callCmd }, new ReturnCmd(Token.NoToken));
                    labelTargets.Add(label);
                    blockTargets.Add(block);
                    blocks.Add(block);
                }
                transferCmd = new GotoCmd(Token.NoToken, labelTargets, blockTargets);
            }
            blocks.Insert(0, new Block(Token.NoToken, "enter", new List<Cmd>(), transferCmd));

            var yieldImpl = new Implementation(Token.NoToken, yieldProc.Name, new List<TypeVariable>(), inputs, new List<Variable>(), new List<Variable>(), blocks);
            yieldImpl.Proc = yieldProc;
            yieldImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            decls.Add(yieldProc);
            decls.Add(yieldImpl);
        }

        private List<Declaration> Collect()
        {
            List<Declaration> decls = new List<Declaration>();
            foreach (Procedure proc in yieldCheckerProcs)
            {
                decls.Add(proc);
            }
            foreach (Implementation impl in yieldCheckerImpls)
            {
                decls.Add(impl);
            }
            foreach (Procedure proc in asyncAndParallelCallDesugarings.Values)
            {
                decls.Add(proc);
            }
            AddYieldProcAndImpl(decls);
            return decls;
        }  

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            Program program = linearTypeChecker.program;
            foreach (int layerNum in civlTypeChecker.allLayerNums)
            {
                if (CommandLineOptions.Clo.TrustLayersDownto <= layerNum || layerNum <= CommandLineOptions.Clo.TrustLayersUpto) continue;

                YieldingProcDuplicator duplicator = new YieldingProcDuplicator(civlTypeChecker, layerNum);
                foreach (var yieldingProc in civlTypeChecker.procToYieldingProc.Values)
                {
                    if (layerNum <= yieldingProc.upperLayer)
                    {
                        Procedure duplicateProc = duplicator.VisitProcedure(yieldingProc.proc);
                        decls.Add(duplicateProc);
                    }
                }

                CivlRefinement civlTransform = new CivlRefinement(linearTypeChecker, civlTypeChecker, duplicator);
                foreach (var impl in program.Implementations.Where(impl => civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc)))
                {
                    var yieldingProc = civlTypeChecker.procToYieldingProc[impl.Proc];
                    if (layerNum <= yieldingProc.upperLayer)
                    {
                        Implementation duplicateImpl = duplicator.VisitImplementation(impl);
                        if (!(yieldingProc is MoverProc && yieldingProc.upperLayer == layerNum))
                        {
                            civlTransform.TransformImpl(duplicateImpl);
                        }
                        decls.Add(duplicateImpl);
                    }
                }
                decls.AddRange(civlTransform.Collect());
            }
        }
    }
}
