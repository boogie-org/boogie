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
    // YieldingProcDuplicator is roughly divided into two phases (see regions below):
    // 1. The visitor pass generates the basic per-layer version (procedure and implementation)
    //    of every yielding procedure.
    // 2. VisitImplementation finally calls TransformImpl which modifies the generated implementation
    //    by injecting the refinement and noninterference checks.
    public class YieldingProcDuplicator : Duplicator
    {
        CivlTypeChecker civlTypeChecker;
        LinearTypeChecker linearTypeChecker;
        public int layerNum;
        private Dictionary<Procedure, Procedure> procToSkipProcDummy;

        public Dictionary<Procedure, Procedure> procMap;           /* Original -> Duplicate */
        public Dictionary<Absy, Absy> absyMap;                     /* Duplicate -> Original */
        public Dictionary<Implementation, Implementation> implMap; /* Duplicate -> Original */
        public HashSet<Procedure> yieldingProcs;

        private YieldingProc enclosingYieldingProc;

        Dictionary<string, Procedure> asyncAndParallelCallDesugarings;
        List<Procedure> yieldCheckerProcs;
        List<Implementation> yieldCheckerImpls;
        Procedure yieldProc;

        Variable pc;
        Variable ok;
        Expr alpha;
        Expr beta;
        HashSet<Variable> frame;

        public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, LinearTypeChecker linearTypeChecker, int layerNum, Dictionary<Procedure, Procedure> procToSkipProcDummy)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.layerNum = layerNum;
            this.procToSkipProcDummy = procToSkipProcDummy;

            this.procMap = new Dictionary<Procedure, Procedure>();
            this.absyMap = new Dictionary<Absy, Absy>();
            this.implMap = new Dictionary<Implementation, Implementation>();
            this.yieldingProcs = new HashSet<Procedure>();

            asyncAndParallelCallDesugarings = new Dictionary<string, Procedure>();
            yieldCheckerProcs = new List<Procedure>();
            yieldCheckerImpls = new List<Implementation>();
            yieldProc = null;
        }

        #region Visitor implementation
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
                        var action = actionProc.refinedAction;
                        if (action.layerRange.Contains(layerNum))
                            return action.layerToActionCopy[layerNum].proc;
                        else
                            return node;
                    }
                    else if (yieldingProc is SkipProc)
                    {
                        // (calls to) skip procedures do not completely disappear because of output variables
                        return procToSkipProcDummy[yieldingProc.proc];
                    }
                    else if (yieldingProc is MoverProc)
                    {
                        // mover procedure does not exist on this layer any more
                        return node;
                    }
                }

                Procedure proc = (Procedure)node.Clone();
                proc.Name = string.Format("{0}_{1}", node.Name, layerNum);
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

        public override Implementation VisitImplementation(Implementation impl)
        {
            if (!civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc))
                return impl;

            enclosingYieldingProc = civlTypeChecker.procToYieldingProc[impl.Proc];
            if (layerNum > enclosingYieldingProc.upperLayer)
                return impl;

            Implementation newImpl = base.VisitImplementation(impl);
            newImpl.Name = newImpl.Proc.Name;
            implMap[newImpl] = impl;

            if (!(enclosingYieldingProc is MoverProc && enclosingYieldingProc.upperLayer == layerNum))
            {
                TransformImpl(newImpl);
            }

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
            newCall.Proc = VisitProcedure(newCall.Proc);

            if (newCall.IsAsync)
            {
                Debug.Assert(civlTypeChecker.procToYieldingProc.ContainsKey(call.Proc));
                YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[call.Proc];
                Debug.Assert(yieldingProc.IsLeftMover);
                if (yieldingProc.upperLayer < layerNum || (yieldingProc is MoverProc && yieldingProc.upperLayer == layerNum))
                {
                    newCall.IsAsync = false;
                }
                if (enclosingYieldingProc.upperLayer == layerNum && yieldingProc.upperLayer > layerNum)
                {
                    ActionProc actionProc = (ActionProc)yieldingProc;
                    newCall.Proc = actionProc.addPendingAsyncProc;
                    newCall.IsAsync = false;
                }
            }

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
            List<Cmd> visitedCmdSeq = base.VisitCmdSeq(cmdSeq);
            List<Cmd> newCmdSeq = new List<Cmd>();
            for (int i = 0; i < visitedCmdSeq.Count; i++)
            {
                Cmd originalCmd = cmdSeq[i];
                Cmd visitedCmd = visitedCmdSeq[i];

                if (originalCmd is CallCmd)
                {
                    ProcessCallCmd((CallCmd)originalCmd, (CallCmd)visitedCmd, newCmdSeq);
                }
                else if (originalCmd is ParCallCmd)
                {
                    ProcessParCallCmd((ParCallCmd)originalCmd, (ParCallCmd)visitedCmd, newCmdSeq);
                }
                else
                {
                    newCmdSeq.Add(visitedCmd);
                }
            }
            newCmdSeq.RemoveAll(cmd => (cmd is AssertCmd assertCmd && assertCmd.Expr.Equals(Expr.True)) ||
                                       (cmd is AssumeCmd assumeCmd && assumeCmd.Expr.Equals(Expr.True)));
            return newCmdSeq;
        }

        // We only have to check the gate of a called atomic action (via an assert) at the creation layer of the caller.
        // In all layers below we just establish invariants which do not require the gates to be checked and we can inject is as an assume.
        private void InjectGate(ActionProc calledActionProc, CallCmd callCmd, List<Cmd> newCmds)
        {
            if (calledActionProc.upperLayer >= layerNum) return;
            AtomicActionCopy atomicActionCopy = calledActionProc.refinedAction.layerToActionCopy[layerNum];
            if (atomicActionCopy.gate.Count == 0) return;

            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            for (int i = 0; i < calledActionProc.proc.InParams.Count; i++)
            {
                // Parameters come from the implementation that defines the atomic action
                map[atomicActionCopy.impl.InParams[i]] = callCmd.Ins[i];
            }
            Substitution subst = Substituter.SubstitutionFromHashtable(map);

            // Important: Do not remove CommentCmd!
            // It separates the injected gate from yield assertions in CollectAndDesugarYields.
            newCmds.Add(new CommentCmd("<<< injected gate"));
            foreach (AssertCmd assertCmd in atomicActionCopy.gate)
            {
                if (layerNum == enclosingYieldingProc.upperLayer)
                    newCmds.Add((AssertCmd)Substituter.Apply(subst, assertCmd));
                else
                    newCmds.Add(new AssumeCmd(assertCmd.tok, Substituter.Apply(subst, assertCmd.Expr)));
            }
            newCmds.Add(new CommentCmd("injected gate >>>"));
        }

        private void ProcessCallCmd(CallCmd originalCallCmd, CallCmd callCmd, List<Cmd> newCmds)
        {
            Procedure originalProc = originalCallCmd.Proc;

            if (civlTypeChecker.procToIntroductionProc.ContainsKey(originalProc))
            {
                if (!civlTypeChecker.CallExists(originalCallCmd, enclosingYieldingProc.upperLayer, layerNum))
                    return;
            }
            else if (civlTypeChecker.procToYieldingProc[originalProc] is ActionProc actionProc)
            {
                Debug.Assert(layerNum <= enclosingYieldingProc.upperLayer);
                InjectGate(actionProc, callCmd, newCmds);
            }
            newCmds.Add(callCmd);
        }

        private void ProcessParCallCmd(ParCallCmd originalParCallCmd, ParCallCmd parCallCmd, List<Cmd> newCmds)
        {
            int maxCalleeLayerNum = 0;
            foreach (CallCmd iter in originalParCallCmd.CallCmds)
            {
                int calleeLayerNum = civlTypeChecker.procToYieldingProc[iter.Proc].upperLayer;
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
        #endregion

        #region Yielding proc transformation
        // Snapshot variables for global variables
        private LocalVariable OgOldGlobalLocal(Variable v)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", v.Name), v.TypedIdent.Type)); }

        // ... and parameters for passing them around
        private Formal OgOldGlobalFormal(Variable v)
        { return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", v.Name), v.TypedIdent.Type), true); }

        // Snapshot variables for return variables
        private LocalVariable OgOldLocal(Variable v)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_old_{0}", v.Name), v.TypedIdent.Type)); }

        // Used to desugar "old" expressions
        // TODO: Check if this is done correctly (or could be simplified).
        private LocalVariable OgOldLocalLocal(Variable v)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_local_old_{0}", v.Name), v.TypedIdent.Type)); }

        // PC and OK variables for checking refinement
        private LocalVariable OgPcLocal()
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_pc", Type.Bool)); }

        private LocalVariable OgOkLocal()
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_ok", Type.Bool)); }

        // Versions of PC and OK for desugaring loops
        private LocalVariable OgPcLabelLocal(string label)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_pc_{0}", label), Type.Bool)); }

        private LocalVariable OgOkLabelLocal(string label)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_ok_{0}", label), Type.Bool)); }

        // Disambiguated parameters of parallel call (when multiple arms are combined into a single procedure)
        private Formal OgParCallDesugarFormal(Variable v, int count, bool incoming)
        { return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_{0}_{1}", count, v.Name), v.TypedIdent.Type), incoming); }

        // Plain copy
        private LocalVariable CopyLocal(Variable v)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type)); }

        private Formal CopyIn(Variable v)
        { return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type), true); }

        private IEnumerable<Variable> AvailableLinearVars(Absy absy)
        {
            HashSet<Variable> availableVars = new HashSet<Variable>(linearTypeChecker.AvailableLinearVars(absyMap[absy]));

            // A bit hackish, since GlobalVariableLayerRange and LocalVariableIntroLayer return maximum layer range
            // respectively minimum layer if called on non-global respectively non-local variable.
            availableVars.RemoveWhere(v =>
                !civlTypeChecker.GlobalVariableLayerRange(v).Contains(layerNum) ||
                layerNum < civlTypeChecker.LocalVariableIntroLayer(v)
            );

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
                var domain = linearTypeChecker.linearDomains[domainName];
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]), new List<Expr> { Expr.Ident(v) });
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new List<Expr> { ie, domainNameToExpr[domainName] });
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }
            return domainNameToExpr;
        }

        public void TransformImpl(Implementation impl)
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
                        if (cmd is CallCmd callCmd && yieldingProcs.Contains(callCmd.Proc))
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
            YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[originalProc];
            if (yieldingProc.upperLayer == this.layerNum)
            {
                pc = OgPcLocal();
                ok = OgOkLocal();
                newLocalVars.Add(pc);
                newLocalVars.Add(ok);
                Dictionary<Variable, Expr> foroldMap = new Dictionary<Variable, Expr>();
                foreach (Variable g in civlTypeChecker.sharedVariables)
                {
                    foroldMap[g] = Expr.Ident(ogOldGlobalMap[g]);
                }
                Substitution forold = Substituter.SubstitutionFromHashtable(foroldMap);
                frame = new HashSet<Variable>(civlTypeChecker.sharedVariables);
                foreach (Variable v in civlTypeChecker.sharedVariables)
                {
                    var layerRange = civlTypeChecker.GlobalVariableLayerRange(v);
                    if (layerRange.upperLayerNum <= yieldingProc.upperLayer ||
                        layerRange.lowerLayerNum > yieldingProc.upperLayer)
                    {
                        frame.Remove(v);
                    }
                }
                if (yieldingProc is ActionProc actionProc)
                {
                    // The parameters of an atomic action come from the implementation that denotes the atomic action specification.
                    // To use the transition relation computed below in the context of the yielding procedure of the refinement check,
                    // we need to substitute the parameters.
                    AtomicActionCopy atomicActionCopy = actionProc.refinedAction.layerToActionCopy[layerNum + 1];
                    Implementation atomicActionImpl = atomicActionCopy.impl;
                    Dictionary<Variable, Expr> alwaysMap = new Dictionary<Variable, Expr>();
                    for (int i = 0; i < atomicActionImpl.InParams.Count; i++)
                    {
                        alwaysMap[atomicActionImpl.InParams[i]] = Expr.Ident(impl.InParams[i]);
                    }
                    for (int i = 0; i < atomicActionImpl.OutParams.Count; i++)
                    {
                        alwaysMap[atomicActionImpl.OutParams[i]] = Expr.Ident(impl.OutParams[i]);
                    }
                    Substitution always = Substituter.SubstitutionFromHashtable(alwaysMap);

                    Expr betaExpr = (new TransitionRelationComputation(atomicActionCopy, frame, new HashSet<Variable>())).TransitionRelationCompute(true);
                    beta = Substituter.ApplyReplacingOldExprs(always, forold, betaExpr);
                    Expr alphaExpr = Expr.And(atomicActionCopy.gate.Select(g => g.Expr));
                    alphaExpr.Type = Type.Bool;
                    alpha = Substituter.Apply(always, alphaExpr);
                }
                else
                {
                    beta = Expr.And(frame.Select(v => Expr.Eq(Expr.Ident(v), foroldMap[v])));
                    alpha = Expr.True;
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
                    Variable l = linearTypeChecker.LinearDomainAvailableLocal(domainName);
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
                foreach (Cmd cmd in b.Cmds)
                {
                    if (cmd is YieldCmd ycmd)
                    {
                        yieldCmd = ycmd;
                        continue;
                    }
                    if (yieldCmd != null)
                    {
                        if (cmd is PredicateCmd)
                        {
                            cmds.Add(cmd);
                        }
                        else
                        {
                            DesugarYield(yieldCmd, cmds, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                            if (cmds.Count > 0)
                            {
                                yields.Add(cmds);
                                cmds = new List<Cmd>();
                            }
                            yieldCmd = null;
                        }
                    }

                    if (cmd is CallCmd callCmd)
                    {
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
                    else if (cmd is ParCallCmd parCallCmd)
                    {
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
                CivlUtil.AddInlineAttribute(yieldProc);
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
            List<Expr> ins = new List<Expr>();
            List<IdentifierExpr> outs = new List<IdentifierExpr>();
            string procName = "og";
            foreach (CallCmd callCmd in parCallCmd.CallCmds)
            {
                procName = procName + "_" + callCmd.Proc.Name;
                ins.AddRange(callCmd.Ins);
                outs.AddRange(callCmd.Outs);
            }
            if (!asyncAndParallelCallDesugarings.ContainsKey(procName))
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
                asyncAndParallelCallDesugarings[procName] = new Procedure(Token.NoToken, procName, new List<TypeVariable>(), inParams, outParams, requiresSeq, civlTypeChecker.sharedVariableIdentifiers, ensuresSeq);
            }
            Procedure proc = asyncAndParallelCallDesugarings[procName];
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
            foreach (var inParam in impl.InParams)
            {
                var domainName = linearTypeChecker.FindDomainName(inParam);
                if (domainName == null) continue;
                var domain = linearTypeChecker.linearDomains[domainName];
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[inParam.TypedIdent.Type]), new List<Expr> { Expr.Ident(inParam) });
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

            foreach (Variable local in impl.LocVars.Union(impl.InParams).Union(impl.OutParams))
            {
                var copy = CopyLocal(local);
                locals.Add(copy);
                map[local] = Expr.Ident(copy);
            }
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                var inParam = linearTypeChecker.LinearDomainInFormal(domainName);
                inputs.Add(inParam);
                map[linearTypeChecker.domainNameToHoleVar[domainName]] = Expr.Ident(inParam);
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
                    var newExpr = Substituter.ApplyReplacingOldExprs(assumeSubst, oldSubst, predCmd.Expr);
                    newCmds.Add(new AssumeCmd(Token.NoToken, newExpr));
                }
                foreach (Cmd cmd in cs)
                {
                    PredicateCmd predCmd = (PredicateCmd)cmd;
                    if (predCmd is AssertCmd)
                    {
                        var newExpr = Substituter.ApplyReplacingOldExprs(subst, oldSubst, predCmd.Expr);
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
            CivlUtil.AddInlineAttribute(yieldCheckerProc);
            yieldCheckerProcs.Add(yieldCheckerProc);

            // Create the yield checker implementation
            var yieldCheckerImpl = new Implementation(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs, new List<Variable>(), locals, yieldCheckerBlocks);
            yieldCheckerImpl.Proc = yieldCheckerProc;
            CivlUtil.AddInlineAttribute(yieldCheckerImpl);
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
                    if (b.Cmds[i] is CallCmd callCmd && callCmd.Proc == yieldProc)
                    {
                        Block newBlock = new Block(Token.NoToken, b.Label + i, newCmds, transferCmd);
                        newCmds = new List<Cmd>();
                        transferCmd = new GotoCmd(Token.NoToken, new List<string> { newBlock.Label, yieldCheckBlock.Label },
                                                                 new List<Block> { newBlock, yieldCheckBlock });
                        newBlocks.Add(newBlock);
                    }
                    else
                    {
                        newCmds.Insert(0, b.Cmds[i]);
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
            CivlUtil.AddInlineAttribute(yieldImpl);
            decls.Add(yieldProc);
            decls.Add(yieldImpl);
        }

        public List<Declaration> Collect()
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
        #endregion
    }

    public class CivlRefinement
    {
        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            Program program = linearTypeChecker.program;

            // Skip procedures do not completely disapper (because of ouput paramters).
            // We create dummy implementations with empty body.
            Dictionary<Procedure, Procedure> procToSkipProcDummy = new Dictionary<Procedure, Procedure>();
            foreach(SkipProc skipProc in civlTypeChecker.procToYieldingProc.Values.OfType<SkipProc>())
            {
                Procedure proc = (Procedure)skipProc.proc.Clone();
                proc.Name = string.Format("skip_dummy_{0}", proc.Name);
                proc.Requires = new List<Requires>();
                proc.Ensures = new List<Ensures>();
                proc.Modifies = new List<IdentifierExpr>();
                Block newInitBlock = new Block(Token.NoToken, "_init", new List<Cmd>(), new ReturnCmd(Token.NoToken));
                List<Block> newBlocks = new List<Block> { newInitBlock };
                Implementation impl = new Implementation(Token.NoToken, proc.Name, proc.TypeParameters, proc.InParams, proc.OutParams, new List<Variable>(), newBlocks);
                impl.Proc = proc;
                CivlUtil.AddInlineAttribute(proc);
                CivlUtil.AddInlineAttribute(impl);
                decls.Add(proc);
                decls.Add(impl);
                procToSkipProcDummy.Add(skipProc.proc, proc);
            }

            // Generate the refinement checks for every layer
            foreach (int layerNum in civlTypeChecker.allRefinementLayers)
            {
                if (CommandLineOptions.Clo.TrustLayersDownto <= layerNum || layerNum <= CommandLineOptions.Clo.TrustLayersUpto) continue;

                YieldingProcDuplicator duplicator = new YieldingProcDuplicator(civlTypeChecker, linearTypeChecker, layerNum, procToSkipProcDummy);

                // We can not simply call VisitProgram, because it does some resolving of calls
                // that is not necessary here (and actually fails).
                foreach (Procedure proc in program.Procedures)
                {
                    duplicator.VisitProcedure(proc);
                }
                foreach (Implementation impl in program.Implementations)
                {
                    duplicator.VisitImplementation(impl);
                }

                decls.AddRange(duplicator.procMap.Values);
                decls.AddRange(duplicator.implMap.Keys);
                decls.AddRange(duplicator.Collect());
            }
        }
    }
}
