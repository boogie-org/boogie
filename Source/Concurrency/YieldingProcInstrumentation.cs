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

            List<Declaration> decls = new List<Declaration>(yieldingProcInstrumentation.yieldCheckerDecls);
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
            yieldCheckerDecls = new List<Declaration>();

            List<Variable> inputs = new List<Variable>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                inputs.Add(linearTypeChecker.LinearDomainInFormal(domainName));
            }

            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                inputs.Add(OldGlobalFormal(g));
            }

            yieldProc = new Procedure(Token.NoToken, $"og_yield_{layerNum}", new List<TypeVariable>(),
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
        private List<Declaration> yieldCheckerDecls;
        private Procedure yieldProc;

        private GlobalSnapshotInstrumentation globalSnapshotInstrumentation;
        private RefinementInstrumentation refinementInstrumentation;
        private NoninterferenceInstrumentation noninterferenceInstrumentation;

        private Implementation YieldImpl()
        {
            List<Variable> inputs = new List<Variable>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                inputs.Add(linearTypeChecker.LinearDomainInFormal(domainName));
            }

            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                inputs.Add(OldGlobalFormal(g));
            }

            List<Block> blocks = new List<Block>();
            TransferCmd transferCmd = new ReturnCmd(Token.NoToken);
            if (yieldCheckerDecls.Count > 0)
            {
                List<Block> blockTargets = new List<Block>();
                List<String> labelTargets = new List<String>();
                int labelCount = 0;
                foreach (Procedure proc in yieldCheckerDecls.OfType<Procedure>())
                {
                    List<Expr> exprSeq = new List<Expr>();
                    foreach (Variable v in inputs)
                    {
                        exprSeq.Add(Expr.Ident(v));
                    }

                    CallCmd callCmd = new CallCmd(Token.NoToken, proc.Name, exprSeq, new List<IdentifierExpr>());
                    callCmd.Proc = proc;
                    string label = $"L_{labelCount++}";
                    Block block = new Block(Token.NoToken, label, new List<Cmd> { callCmd },
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

        private Formal OldGlobalFormal(Variable v)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, $"og_global_old_{v.Name}", v.TypedIdent.Type), true);
        }

        private void TransformImpl(Implementation impl)
        {
            HashSet<Block> yieldingLoopHeaders;
            Graph<Block> graph = ComputeYieldingLoopHeaders(impl, out yieldingLoopHeaders);

            // initialize globalSnapshotInstrumentation
            globalSnapshotInstrumentation = new GlobalSnapshotInstrumentation(civlTypeChecker);

            // initialize refinementInstrumentation
            Implementation originalImpl = implMap[impl];
            YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[originalImpl.Proc];
            if (yieldingProc.upperLayer == this.layerNum)
            {
                refinementInstrumentation = new SomeRefinementInstrumentation(
                    civlTypeChecker,
                    impl,
                    originalImpl,
                    globalSnapshotInstrumentation.OldGlobalMap,
                    yieldingLoopHeaders);
            }
            else
            {
                refinementInstrumentation = new NoneRefinementInstrumentation();
            }

            // initialize noninterferenceInstrumentation
            if (CommandLineOptions.Clo.TrustNonInterference)
            {
                noninterferenceInstrumentation = new NoneNoninterferenceInstrumentation();
            }
            else
            {
                noninterferenceInstrumentation = new SomeNoninterferenceInstrumentation(civlTypeChecker,
                    linearTypeChecker,
                    layerNum, absyMap, globalSnapshotInstrumentation.OldGlobalMap, yieldProc);
            }

            DesugarConcurrency(impl, graph, yieldingLoopHeaders);

            impl.LocVars.AddRange(globalSnapshotInstrumentation.NewLocalVars);
            impl.LocVars.AddRange(refinementInstrumentation.NewLocalVars);
            impl.LocVars.AddRange(noninterferenceInstrumentation.NewLocalVars);
        }

        private Block AddInitialBlock(Implementation impl)
        {
            var initCmds = new List<Cmd>();
            initCmds.AddRange(globalSnapshotInstrumentation.CreateInitCmds());
            initCmds.AddRange(refinementInstrumentation.CreateInitCmds());
            initCmds.AddRange(noninterferenceInstrumentation.CreateInitCmds(impl));
            var gotoCmd = new GotoCmd(Token.NoToken, new List<String> { impl.Blocks[0].Label },
                new List<Block> { impl.Blocks[0] });
            return new Block(Token.NoToken, "og_init", initCmds, gotoCmd);
        }

        private Graph<Block> ComputeYieldingLoopHeaders(Implementation impl, out HashSet<Block> yieldingLoopHeaders)
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

            yieldingLoopHeaders = new HashSet<Block>();
            IEnumerable<Block> sortedHeaders = graph.SortHeadersByDominance();
            foreach (Block header in sortedHeaders)
            {
                if (yieldingLoopHeaders.Any(x => graph.DominatorMap.DominatedBy(x, header)))
                {
                    yieldingLoopHeaders.Add(header);
                }
                else if (IsYieldingHeader(graph, header))
                {
                    yieldingLoopHeaders.Add(header);
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

        private void DesugarConcurrency(Implementation impl, Graph<Block> graph, HashSet<Block> yieldingLoopHeaders)
        {
            var allYieldPredicates = CollectYields(impl);
            var allNonemptyYieldPredicates = allYieldPredicates.Values.Where(x => x.Count > 0);
            if (allNonemptyYieldPredicates.Count() > 0)
            {
                yieldCheckerDecls.AddRange(noninterferenceInstrumentation.CreateYieldCheckerProcImpl(impl, allNonemptyYieldPredicates));
            }

            var yieldCheckerBlock = CreateYieldCheckerBlock();
            var returnBlock = CreateReturnBlock();
            SplitBlocks(impl);

            // add jumps to yieldCheckerBlock and returnBlock
            foreach (var b in impl.Blocks)
            {
                if (b.TransferCmd is GotoCmd gotoCmd)
                {
                    var addEdge = false;
                    foreach (var nextBlock in gotoCmd.labelTargets)
                    {
                        if (nextBlock.cmds.Count > 0)
                        {
                            var cmd = nextBlock.cmds[0];
                            if (cmd is YieldCmd)
                            {
                                addEdge = true;
                            }
                            else if (cmd is CallCmd callCmd && yieldingProcs.Contains(callCmd.Proc))
                            {
                                addEdge = true;
                            }
                            else if (cmd is ParCallCmd)
                            {
                                addEdge = true;
                            }
                        }
                    }
                    if (addEdge)
                    {
                        gotoCmd.labelNames.Add(yieldCheckerBlock.Label);
                        gotoCmd.labelTargets.Add(yieldCheckerBlock);
                    }
                }
                else
                {
                    b.TransferCmd = new GotoCmd(b.TransferCmd.tok, new List<string> { returnBlock.Label }, new List<Block> { returnBlock });
                }
            }
            foreach (Block header in yieldingLoopHeaders)
            {
                foreach (Block pred in header.Predecessors)
                {
                    var gotoCmd = pred.TransferCmd as GotoCmd;
                    gotoCmd.labelNames.Add(yieldCheckerBlock.Label);
                    gotoCmd.labelTargets.Add(yieldCheckerBlock);
                }
            }

            // desugar YieldCmd, CallCmd, and ParCallCmd 
            foreach (Block b in impl.Blocks)
            {
                if (b.cmds.Count > 0)
                {
                    var cmd = b.cmds[0];
                    if (cmd is YieldCmd yieldCmd)
                    {
                        var newCmds = new List<Cmd>();
                        newCmds.AddRange(refinementInstrumentation.CreateUpdateCmds());
                        var yieldPredicates = allYieldPredicates[yieldCmd];
                        newCmds.AddRange(yieldPredicates);
                        newCmds.AddRange(DesugarYieldCmd(yieldCmd, yieldPredicates));
                        newCmds.AddRange(b.cmds.GetRange(1 + yieldPredicates.Count, b.cmds.Count - (1 + yieldPredicates.Count)));
                        b.cmds = newCmds;
                    }
                    else if (cmd is CallCmd callCmd && yieldingProcs.Contains(callCmd.Proc))
                    {
                        List<Cmd> newCmds = new List<Cmd>();
                        newCmds.AddRange(refinementInstrumentation.CreateUpdateCmds());
                        if (callCmd.IsAsync)
                        {
                            if (!asyncAndParallelCallDesugarings.ContainsKey(callCmd.Proc.Name))
                            {
                                asyncAndParallelCallDesugarings[callCmd.Proc.Name] = new Procedure(Token.NoToken,
                                    $"DummyAsyncTarget_{callCmd.Proc.Name}",
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
                            if (civlTypeChecker.sharedVariables.Count > 0)
                            {
                                newCmds.AddRange(refinementInstrumentation.CreateAssumeCmds());
                            }
                        }
                        newCmds.AddRange(globalSnapshotInstrumentation.CreateUpdatesToOldGlobalVars());
                        newCmds.AddRange(refinementInstrumentation.CreateUpdatesToOldOutputVars());
                        newCmds.AddRange(noninterferenceInstrumentation.CreateUpdatesToPermissionCollector(callCmd));
                        newCmds.AddRange(b.cmds.GetRange(1, b.cmds.Count - 1));
                        b.cmds = newCmds;
                    }
                    else if (cmd is ParCallCmd parCallCmd)
                    {
                        List<Cmd> newCmds = new List<Cmd>();
                        newCmds.AddRange(refinementInstrumentation.CreateUpdateCmds());
                        newCmds.AddRange(DesugarParCallCmd(parCallCmd));
                        if (civlTypeChecker.sharedVariables.Count > 0)
                        {
                            newCmds.AddRange(refinementInstrumentation.CreateAssumeCmds());
                        }
                        newCmds.AddRange(globalSnapshotInstrumentation.CreateUpdatesToOldGlobalVars());
                        newCmds.AddRange(refinementInstrumentation.CreateUpdatesToOldOutputVars());
                        newCmds.AddRange(noninterferenceInstrumentation.CreateUpdatesToPermissionCollector(parCallCmd));
                        newCmds.AddRange(b.cmds.GetRange(1, b.cmds.Count - 1));
                        b.cmds = newCmds;
                    }
                }
            }

            impl.Blocks.AddRange(InstrumentYieldingLoopHeaders(graph, yieldingLoopHeaders));
            impl.Blocks.Add(yieldCheckerBlock);
            impl.Blocks.Add(returnBlock);
            impl.Blocks.Insert(0, AddInitialBlock(impl));
        }

        private Dictionary<YieldCmd, List<PredicateCmd>> CollectYields(Implementation impl)
        {
            Dictionary<YieldCmd, List<PredicateCmd>> allYieldPredicates = new Dictionary<YieldCmd, List<PredicateCmd>>();
            List<PredicateCmd> yieldPredicates = new List<PredicateCmd>();
            foreach (Block b in impl.Blocks)
            {
                YieldCmd yieldCmd = null;
                foreach (Cmd cmd in b.Cmds)
                {
                    if (yieldCmd != null)
                    {
                        if (cmd is PredicateCmd)
                        {
                            yieldPredicates.Add(cmd as PredicateCmd);
                        }
                        else
                        {
                            allYieldPredicates[yieldCmd] = yieldPredicates;
                            yieldPredicates = new List<PredicateCmd>();
                            yieldCmd = null;
                        }
                    }
                    if (cmd is YieldCmd ycmd)
                    {
                        yieldCmd = ycmd;
                    }
                }
                if (yieldCmd != null)
                {
                    allYieldPredicates[yieldCmd] = yieldPredicates;
                    yieldPredicates = new List<PredicateCmd>();
                }
            }
            return allYieldPredicates;
        }

        private void SplitBlocks(Implementation impl)
        {
            List<Block> newBlocks = new List<Block>();
            foreach (Block b in impl.Blocks)
            {
                var currTransferCmd = b.TransferCmd;
                int labelCount = 0;
                int lastSplitIndex = b.cmds.Count;
                for (int i = b.cmds.Count - 1; i >= 0; i--)
                {
                    var split = false;
                    var cmd = b.cmds[i];
                    if (cmd is YieldCmd)
                    {
                        split = true;
                    }
                    else if (cmd is CallCmd callCmd)
                    {
                        if (yieldingProcs.Contains(callCmd.Proc))
                        {
                            split = true;
                        }
                    }
                    else if (cmd is ParCallCmd)
                    {
                        split = true;
                    }
                    if (split)
                    {
                        var newBlock = new Block(b.tok, $"{b.Label}_{labelCount++}", b.cmds.GetRange(i, lastSplitIndex - i),
                            currTransferCmd);
                        newBlocks.Add(newBlock);
                        currTransferCmd = new GotoCmd(b.tok, new List<string> { newBlock.Label },
                            new List<Block> { newBlock });
                        lastSplitIndex = i;
                    }
                }
                b.cmds = b.cmds.GetRange(0, lastSplitIndex);
                b.TransferCmd = currTransferCmd;
            }
            impl.Blocks.AddRange(newBlocks);
        }

        private Block CreateYieldCheckerBlock()
        {
            var newCmds = new List<Cmd>();
            newCmds.AddRange(refinementInstrumentation.CreateAssertCmds());
            newCmds.AddRange(noninterferenceInstrumentation.CreateCallToYieldProc());
            newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
            return new Block(Token.NoToken, "YieldChecker", newCmds, new ReturnCmd(Token.NoToken));
        }

        private Block CreateReturnBlock()
        {
            var returnBlockCmds = new List<Cmd>();
            returnBlockCmds.AddRange(refinementInstrumentation.CreateUpdateCmds());
            returnBlockCmds.AddRange(refinementInstrumentation.CreateFinalAssertCmds());
            return new Block(Token.NoToken, "ReturnChecker", returnBlockCmds, new ReturnCmd(Token.NoToken));
        }

        private List<Cmd> DesugarYieldCmd(
            YieldCmd yieldCmd,
            List<PredicateCmd> cmds)
        {
            var newCmds = new List<Cmd>();
            if (civlTypeChecker.sharedVariableIdentifiers.Count > 0)
            {
                newCmds.Add(new HavocCmd(Token.NoToken, civlTypeChecker.sharedVariableIdentifiers));
                newCmds.AddRange(refinementInstrumentation.CreateAssumeCmds());
            }
            newCmds.AddRange(globalSnapshotInstrumentation.CreateUpdatesToOldGlobalVars());
            newCmds.AddRange(refinementInstrumentation.CreateUpdatesToOldOutputVars());
            newCmds.AddRange(noninterferenceInstrumentation.CreateUpdatesToPermissionCollector(yieldCmd));

            for (int j = 0; j < cmds.Count; j++)
            {
                newCmds.Add(new AssumeCmd(Token.NoToken, cmds[j].Expr));
            }
            return newCmds;
        }

        private List<Cmd> DesugarParCallCmd(ParCallCmd parCallCmd)
        {
            var newCmds = new List<Cmd>();
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
                        Variable y = ParCallDesugarFormal(x, count, true);
                        inParams.Add(y);
                        map[x] = Expr.Ident(y);
                    }
                    foreach (Variable x in callCmd.Proc.OutParams)
                    {
                        Variable y = ParCallDesugarFormal(x, count, false);
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
            return newCmds;
        }

        private Formal ParCallDesugarFormal(Variable v, int count, bool incoming)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, $"og_{count}_{v.Name}", v.TypedIdent.Type), incoming);
        }

        private List<Block> InstrumentYieldingLoopHeaders(Graph<Block> graph, HashSet<Block> yieldingLoopHeaders)
        {
            var newBlocks = new List<Block>();
            var headerToInstrumentationBlocks = new Dictionary<Block, List<Block>>();
            var headerToNonBackEdgeInstrumentationBlocks = new Dictionary<Block, List<Block>>();
            foreach (Block header in yieldingLoopHeaders)
            {
                headerToInstrumentationBlocks[header] = new List<Block>();
                headerToNonBackEdgeInstrumentationBlocks[header] = new List<Block>();
                foreach (Block pred in header.Predecessors)
                {
                    var gotoCmd = pred.TransferCmd as GotoCmd;
                    if (gotoCmd.labelTargets.Count == 1)
                    {
                        headerToInstrumentationBlocks[header].Add(pred);
                        if (!graph.BackEdgeNodes(header).Contains(pred))
                        {
                            headerToNonBackEdgeInstrumentationBlocks[header].Add(pred);
                        }
                    }
                    else
                    {
                        var newBlock = new Block(Token.NoToken, $"{pred.Label}_to_{header.Label}", new List<Cmd>(), pred.TransferCmd);
                        pred.TransferCmd = new GotoCmd(Token.NoToken, new List<string> { newBlock.Label }, new List<Block> { newBlock });
                        headerToInstrumentationBlocks[header].Add(newBlock);
                        if (!graph.BackEdgeNodes(header).Contains(pred))
                        {
                            headerToNonBackEdgeInstrumentationBlocks[header].Add(newBlock);
                        }
                        newBlocks.Add(newBlock);
                    }
                }
            }

            foreach (Block header in yieldingLoopHeaders)
            {
                foreach (Block pred in headerToInstrumentationBlocks[header])
                {
                    pred.cmds.AddRange(refinementInstrumentation.CreateUpdateCmds());
                }

                foreach (Block pred in headerToNonBackEdgeInstrumentationBlocks[header])
                {
                    pred.cmds.AddRange(refinementInstrumentation.CreateYieldingLoopHeaderInitCmds(header));
                }

                List<Cmd> firstCmds;
                List<Cmd> secondCmds;
                SplitCmds(header.Cmds, out firstCmds, out secondCmds);
                List<Cmd> newCmds = new List<Cmd>();
                newCmds.AddRange(firstCmds);
                newCmds.AddRange(refinementInstrumentation.CreateYieldingLoopHeaderAssertCmds(header));
                newCmds.AddRange(globalSnapshotInstrumentation.CreateUpdatesToOldGlobalVars());
                newCmds.AddRange(refinementInstrumentation.CreateUpdatesToOldOutputVars());
                newCmds.AddRange(noninterferenceInstrumentation.CreateUpdatesToPermissionCollector(header));
                newCmds.AddRange(secondCmds);
                header.Cmds = newCmds;
            }

            return newBlocks;
        }

        private void SplitCmds(List<Cmd> cmds, out List<Cmd> firstCmds, out List<Cmd> secondCmds)
        {
            firstCmds = new List<Cmd>();
            secondCmds = new List<Cmd>();
            var count = 0;
            bool splitDone = false;
            while (count < cmds.Count)
            {
                var cmd = cmds[count];
                if (splitDone)
                {
                    secondCmds.Add(cmd);
                    count++;
                }
                else if (cmd is PredicateCmd)
                {
                    firstCmds.Add(cmd);
                    count++;
                }
                else
                {
                    splitDone = true;
                }
            }
        }
    }
}
