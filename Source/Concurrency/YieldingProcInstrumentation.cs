using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
    class YieldingProcInstrumentation
    {
        public static List<Declaration> TransformImplementations(
            CivlTypeChecker civlTypeChecker,
            LinearTypeChecker linearTypeChecker,
            int layerNum,
            Dictionary<Absy, Absy> absyMap,
            Dictionary<Implementation, Implementation> implMap,
            HashSet<Procedure> yieldingProcs)
        {
            var yieldingProcInstrumentation = new YieldingProcInstrumentation(civlTypeChecker, linearTypeChecker, layerNum,
                absyMap, implMap, yieldingProcs);
            foreach (var kv in implMap)
            {
                var impl = kv.Value;
                var newImpl = kv.Key;
                var proc = civlTypeChecker.procToYieldingProc[impl.Proc];
                if (!(proc is MoverProc && proc.upperLayer == layerNum))
                {
                    yieldingProcInstrumentation.TransformImpl(newImpl);
                }
            }
            List<Declaration> decls = new List<Declaration>();
            foreach (Procedure proc in yieldingProcInstrumentation.yieldCheckerProcs)
            {
                decls.Add(proc);
            }
            foreach (Implementation impl in yieldingProcInstrumentation.yieldCheckerImpls)
            {
                decls.Add(impl);
            }
            foreach (Procedure proc in yieldingProcInstrumentation.asyncAndParallelCallDesugarings.Values)
            {
                decls.Add(proc);
            }
            decls.Add(yieldingProcInstrumentation.yieldProc);
            decls.Add(yieldingProcInstrumentation.YieldImpl());
            return decls;
        }

        private YieldingProcInstrumentation(
            CivlTypeChecker civlTypeChecker,
            LinearTypeChecker linearTypeChecker,
            int layerNum,
            Dictionary<Absy, Absy> absyMap,
            Dictionary<Implementation, Implementation> implMap,
            HashSet<Procedure> yieldingProcs)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.layerNum = layerNum;
            this.absyMap = absyMap;
            this.implMap = implMap;
            this.yieldingProcs = yieldingProcs;
            asyncAndParallelCallDesugarings = new Dictionary<string, Procedure>();
            yieldCheckerProcs = new List<Procedure>();
            yieldCheckerImpls = new List<Implementation>();
            
            List<Variable> inputs = new List<Variable>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                inputs.Add(linearTypeChecker.LinearDomainInFormal(domainName));
            }

            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                inputs.Add(OgOldGlobalFormal(g));
            }

            yieldProc = new Procedure(Token.NoToken, string.Format("og_yield_{0}", layerNum), new List<TypeVariable>(),
                inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            CivlUtil.AddInlineAttribute(yieldProc);
        }

        private CivlTypeChecker civlTypeChecker;
        private LinearTypeChecker linearTypeChecker;
        private int layerNum;
        private Dictionary<Absy, Absy> absyMap;
        private Dictionary<Implementation, Implementation> implMap;
        private HashSet<Procedure> yieldingProcs;
        
        private Dictionary<string, Procedure> asyncAndParallelCallDesugarings;
        private List<Procedure> yieldCheckerProcs;
        private List<Implementation> yieldCheckerImpls;
        private Procedure yieldProc;

        private NoninterferenceInstrumentation noninterferenceInstrumentation;
        private RefinementInstrumentation refinementInstrumentation;

        private Implementation YieldImpl()
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
                    Block block = new Block(Token.NoToken, label, new List<Cmd> {callCmd},
                        new ReturnCmd(Token.NoToken));
                    labelTargets.Add(label);
                    blockTargets.Add(block);
                    blocks.Add(block);
                }

                transferCmd = new GotoCmd(Token.NoToken, labelTargets, blockTargets);
            }

            blocks.Insert(0, new Block(Token.NoToken, "enter", new List<Cmd>(), transferCmd));

            var yieldImpl = new Implementation(Token.NoToken, yieldProc.Name, new List<TypeVariable>(), inputs,
                new List<Variable>(), new List<Variable>(), blocks);
            yieldImpl.Proc = yieldProc;
            CivlUtil.AddInlineAttribute(yieldImpl);
            return yieldImpl;
        }
        
        private Formal OgOldGlobalFormal(Variable v)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", v.Name), v.TypedIdent.Type), true);
        }
        
        private void TransformImpl(Implementation impl)
        {
            HashSet<Block> yieldingHeaders;
            Graph<Block> graph = ComputeYieldingLoopHeaders(impl, out yieldingHeaders);

            List<Variable> newLocalVars = new List<Variable>();
            var ogOldGlobalMap = SetupOgOldGlobalMap(newLocalVars);
            refinementInstrumentation = SetupRefinementInstrumentation(impl, ogOldGlobalMap, newLocalVars);
            noninterferenceInstrumentation = SetupNoninterferenceInstrumentation(ogOldGlobalMap, newLocalVars);

            List<List<PredicateCmd>> yields = CollectAndDesugarYields(impl);
            if (yields.Count > 0)
            {
                Procedure yieldCheckerProc;
                Implementation yieldCheckerImpl;
                noninterferenceInstrumentation.CreateYieldCheckerImpl(impl, yields, out yieldCheckerProc, out yieldCheckerImpl);
                yieldCheckerProcs.Add(yieldCheckerProc);
                yieldCheckerImpls.Add(yieldCheckerImpl);
            }

            ProcessLoopHeaders(yieldingHeaders);

            var initCmds = new List<Cmd>();
            if (refinementInstrumentation != null)
            {
                initCmds.Add(refinementInstrumentation.CreateInitCmd());
                newLocalVars.AddRange(refinementInstrumentation.ProcessLoopHeaders(graph, yieldingHeaders));
            }

            impl.LocVars.AddRange(newLocalVars);
            initCmds.AddRange(noninterferenceInstrumentation.CreateInitCmds(impl));
            AddInitialBlock(impl, initCmds);

            noninterferenceInstrumentation.UnifyCallsToYieldProc(impl);
        }

        // Snapshot variables for global variables
        private LocalVariable OgOldGlobalLocal(Variable v)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", v.Name), v.TypedIdent.Type));
        }

        // Snapshot variables for return variables
        private LocalVariable OgOldLocal(Variable v)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format("og_old_{0}", v.Name), v.TypedIdent.Type));
        }

        // PC and OK variables for checking refinement
        private LocalVariable OgPcLocal()
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_pc", Type.Bool));
        }

        private LocalVariable OgOkLocal()
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_ok", Type.Bool));
        }

        // Disambiguated parameters of parallel call (when multiple arms are combined into a single procedure)
        private Formal OgParCallDesugarFormal(Variable v, int count, bool incoming)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format("og_{0}_{1}", count, v.Name), v.TypedIdent.Type), incoming);
        }

        private Formal CopyIn(Variable v)
        {
            return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type), true);
        }

        private IEnumerable<Variable> AvailableLinearVars(Absy absy)
        {
            HashSet<Variable> availableVars =
                new HashSet<Variable>(linearTypeChecker.AvailableLinearVars(absyMap[absy]));

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
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new Expr[] {Expr.False});
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }

            foreach (Variable v in availableLinearVars)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                var domain = linearTypeChecker.linearDomains[domainName];
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]),
                    new List<Expr> {Expr.Ident(v)});
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool),
                    new List<Expr> {ie, domainNameToExpr[domainName]});
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }

            return domainNameToExpr;
        }

        private void AddInitialBlock(Implementation impl, List<Cmd> initCmds)
        {
            var gotoCmd = new GotoCmd(Token.NoToken, new List<String> {impl.Blocks[0].Label},
                new List<Block> {impl.Blocks[0]});
            Block initBlock = new Block(Token.NoToken, "og_init", initCmds, gotoCmd);
            impl.Blocks.Insert(0, initBlock);
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

        private Dictionary<Variable, Variable> SetupOgOldGlobalMap(List<Variable> newLocalVars)
        {
            var ogOldGlobalMap = new Dictionary<Variable, Variable>();
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                LocalVariable l = OgOldGlobalLocal(g);
                ogOldGlobalMap[g] = l;
                newLocalVars.Add(l);
            }
            return ogOldGlobalMap;
        }

        private RefinementInstrumentation SetupRefinementInstrumentation(Implementation impl, Dictionary<Variable, Variable> ogOldGlobalMap,
            List<Variable> newLocalVars)
        {
            Procedure originalProc = implMap[impl].Proc;
            YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[originalProc];
            if (yieldingProc.upperLayer != this.layerNum)
            {
                return null;
            }

            var pc = OgPcLocal();
            var ok = OgOkLocal();
            newLocalVars.Add(pc);
            newLocalVars.Add(ok);
            Dictionary<Variable, Expr> foroldMap = new Dictionary<Variable, Expr>();
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                foroldMap[g] = Expr.Ident(ogOldGlobalMap[g]);
            }

            Substitution forold = Substituter.SubstitutionFromHashtable(foroldMap);
            var frame = new HashSet<Variable>(civlTypeChecker.sharedVariables);
            foreach (Variable v in civlTypeChecker.sharedVariables)
            {
                var layerRange = civlTypeChecker.GlobalVariableLayerRange(v);
                if (layerRange.upperLayerNum <= yieldingProc.upperLayer ||
                    layerRange.lowerLayerNum > yieldingProc.upperLayer)
                {
                    frame.Remove(v);
                }
            }

            Expr alpha, beta;
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

                Expr betaExpr =
                    (new TransitionRelationComputation(atomicActionCopy, frame, new HashSet<Variable>()))
                    .TransitionRelationCompute(true);
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

            return new RefinementInstrumentation(ogOldGlobalMap, pc, ok, alpha, beta, frame);
        }

        private NoninterferenceInstrumentation SetupNoninterferenceInstrumentation(Dictionary<Variable, Variable> ogOldGlobalMap,
            List<Variable> newLocalVars)
        {
            var domainNameToLocalVar = new Dictionary<string, Variable>();
            {
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable l = linearTypeChecker.LinearDomainAvailableLocal(domainName);
                    domainNameToLocalVar[domainName] = l;
                    newLocalVars.Add(l);
                }
            }
            return new NoninterferenceInstrumentation(civlTypeChecker, linearTypeChecker, layerNum, ogOldGlobalMap,
                domainNameToLocalVar, yieldProc);
        }

        private List<List<PredicateCmd>> CollectAndDesugarYields(Implementation impl)
        {
            List<List<PredicateCmd>> yields = new List<List<PredicateCmd>>();
            List<PredicateCmd> cmds = new List<PredicateCmd>();
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
                            cmds.Add(cmd as PredicateCmd);
                        }
                        else
                        {
                            DesugarYield(yieldCmd, cmds, newCmds);
                            if (cmds.Count > 0)
                            {
                                yields.Add(cmds);
                                cmds = new List<PredicateCmd>();
                            }

                            yieldCmd = null;
                        }
                    }

                    if (cmd is CallCmd callCmd)
                    {
                        if (yieldingProcs.Contains(callCmd.Proc))
                        {
                            AddCallToYieldProc(callCmd.tok, newCmds);
                        }

                        if (callCmd.IsAsync)
                        {
                            if (!asyncAndParallelCallDesugarings.ContainsKey(callCmd.Proc.Name))
                            {
                                asyncAndParallelCallDesugarings[callCmd.Proc.Name] = new Procedure(Token.NoToken,
                                    string.Format("DummyAsyncTarget_{0}", callCmd.Proc.Name),
                                    callCmd.Proc.TypeParameters, callCmd.Proc.InParams, callCmd.Proc.OutParams,
                                    callCmd.Proc.Requires, new List<IdentifierExpr>(), new List<Ensures>());
                            }

                            var dummyAsyncTargetProc = asyncAndParallelCallDesugarings[callCmd.Proc.Name];
                            CallCmd dummyCallCmd = new CallCmd(callCmd.tok, dummyAsyncTargetProc.Name, callCmd.Ins,
                                callCmd.Outs, callCmd.Attributes);
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

                            if (!callCmd.IsAsync && civlTypeChecker.sharedVariables.Count > 0 && refinementInstrumentation != null)
                            {
                                newCmds.Add(refinementInstrumentation.CreateAssumeCmd());
                            }

                            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(availableLinearVars);
                            newCmds.AddRange(noninterferenceInstrumentation.AddUpdatesToOldGlobalVars(domainNameToExpr));
                        }
                    }
                    else if (cmd is ParCallCmd parCallCmd)
                    {
                        AddCallToYieldProc(parCallCmd.tok, newCmds);
                        DesugarParallelCallCmd(newCmds, parCallCmd);
                        HashSet<Variable> availableLinearVars = new HashSet<Variable>(AvailableLinearVars(parCallCmd));

                        if (civlTypeChecker.sharedVariables.Count > 0 && refinementInstrumentation != null)
                        {
                            newCmds.Add(refinementInstrumentation.CreateAssumeCmd());
                        }

                        Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(availableLinearVars);
                        newCmds.AddRange(noninterferenceInstrumentation.AddUpdatesToOldGlobalVars(domainNameToExpr));
                    }
                    else
                    {
                        newCmds.Add(cmd);
                    }
                }

                if (yieldCmd != null)
                {
                    DesugarYield(yieldCmd, cmds, newCmds);
                    if (cmds.Count > 0)
                    {
                        yields.Add(cmds);
                        cmds = new List<PredicateCmd>();
                    }
                }

                if (b.TransferCmd is ReturnCmd)
                {
                    AddCallToYieldProc(b.TransferCmd.tok, newCmds);
                    if (refinementInstrumentation != null)
                    {
                        newCmds.Add(refinementInstrumentation.CreateFinalAssertCmd(b.TransferCmd.tok));
                    }
                }

                b.Cmds = newCmds;
            }

            return yields;
        }

        private void AddCallToYieldProc(
            IToken tok,
            List<Cmd> newCmds)
        {
            if (!CommandLineOptions.Clo.TrustNonInterference)
            {
                CallCmd yieldCallCmd = noninterferenceInstrumentation.CallToYieldProc(tok);
                newCmds.Add(yieldCallCmd);
            }

            if (refinementInstrumentation != null)
            {
                newCmds.Add(refinementInstrumentation.CreateSkipOrBetaAssertCmd(tok));
                newCmds.Add(refinementInstrumentation.CreateSkipAssertCmd(tok));
                newCmds.Add(refinementInstrumentation.CreatePcOkUpdateCmd());
            }
        }

        private void DesugarYield(
            YieldCmd yieldCmd,
            List<PredicateCmd> cmds,
            List<Cmd> newCmds)
        {
            AddCallToYieldProc(yieldCmd.tok, newCmds);

            if (civlTypeChecker.sharedVariableIdentifiers.Count > 0)
            {
                newCmds.Add(new HavocCmd(Token.NoToken, civlTypeChecker.sharedVariableIdentifiers));
                if (refinementInstrumentation != null)
                {
                    newCmds.Add(refinementInstrumentation.CreateAssumeCmd());
                }
            }

            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(AvailableLinearVars(yieldCmd));
            newCmds.AddRange(noninterferenceInstrumentation.AddUpdatesToOldGlobalVars(domainNameToExpr));

            for (int j = 0; j < cmds.Count; j++)
            {
                newCmds.Add(new AssumeCmd(Token.NoToken, cmds[j].Expr));
            }
        }

        private void DesugarParallelCallCmd(List<Cmd> newCmds, ParCallCmd parCallCmd)
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
                        requiresSeq.Add(new Requires(req.tok, req.Free, Substituter.Apply(subst, req.Condition), null,
                            req.Attributes));
                    }

                    foreach (Ensures ens in callCmd.Proc.Ensures)
                    {
                        ensuresSeq.Add(new Ensures(ens.tok, ens.Free, Substituter.Apply(subst, ens.Condition), null,
                            ens.Attributes));
                    }

                    count++;
                }

                asyncAndParallelCallDesugarings[procName] = new Procedure(Token.NoToken, procName,
                    new List<TypeVariable>(), inParams, outParams, requiresSeq,
                    civlTypeChecker.sharedVariableIdentifiers, ensuresSeq);
            }

            Procedure proc = asyncAndParallelCallDesugarings[procName];
            CallCmd dummyCallCmd = new CallCmd(parCallCmd.tok, proc.Name, ins, outs, parCallCmd.Attributes);
            dummyCallCmd.Proc = proc;
            newCmds.Add(dummyCallCmd);
        }

        private void ProcessLoopHeaders(HashSet<Block> yieldingHeaders)
        {
            foreach (Block header in yieldingHeaders)
            {
                Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(AvailableLinearVars(header));
                foreach (Block pred in header.Predecessors)
                {
                    AddCallToYieldProc(header.tok, pred.Cmds);
                    pred.cmds.AddRange(noninterferenceInstrumentation.AddUpdatesToOldGlobalVars(domainNameToExpr));
                }

                var newCmds = noninterferenceInstrumentation.CreateAssumeCmds(domainNameToExpr);
                newCmds.AddRange(header.Cmds);
                header.Cmds = newCmds;
            }
        }
    }
}