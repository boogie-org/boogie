using System;
using System.Collections.Generic;
using System.Diagnostics;
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
            HashSet<Procedure> yieldingProcs)
        {
            var linearHelper = new LinearPermissionInstrumentation(civlTypeChecker, linearTypeChecker, layerNum, absyMap);
            var yieldingProcInstrumentation = new YieldingProcInstrumentation(
                civlTypeChecker, 
                linearTypeChecker, 
                linearHelper,
                layerNum,
                absyMap,
                yieldingProcs);
            foreach (var impl in absyMap.Keys.OfType<Implementation>())
            {
                // Add disjointness assumptions at beginning, loop headers, and after each call or parallel call.
                // These are added for each duplicate implementation of yielding procedures.
                // Disjointness assumptions after yields are added inside TransformImpl which is called for 
                // all implementations except for a mover procedure at its disappearing layer.
                // But this is fine because a mover procedure at its disappearing layer does not have a yield in it.
                linearHelper.AddDisjointnessAssumptions(impl, yieldingProcs);
                var originalImpl = absyMap[impl] as Implementation;
                var proc = civlTypeChecker.procToYieldingProc[originalImpl.Proc];
                if (!(proc is MoverProc && proc.upperLayer == layerNum))
                {
                    yieldingProcInstrumentation.TransformImpl(originalImpl, impl);
                }
            }

            List<Declaration> decls = new List<Declaration>(yieldingProcInstrumentation.noninterferenceCheckerDecls);
            foreach (Procedure proc in yieldingProcInstrumentation.parallelCallPreconditionCheckers.Values)
            {
                decls.Add(proc);
            }
            decls.Add(yieldingProcInstrumentation.wrapperNoninterferenceCheckerProc);
            decls.Add(yieldingProcInstrumentation.WrapperNoninterferenceCheckerImpl());
            return decls;
        }
        
        private CivlTypeChecker civlTypeChecker;
        private LinearTypeChecker linearTypeChecker;
        private int layerNum;
        private Dictionary<Absy, Absy> absyMap;
        private HashSet<Procedure> yieldingProcs;

        private Dictionary<string, Procedure> parallelCallPreconditionCheckers;
        private List<Declaration> noninterferenceCheckerDecls;
        private Procedure wrapperNoninterferenceCheckerProc;

        private GlobalSnapshotInstrumentation globalSnapshotInstrumentation;
        private RefinementInstrumentation refinementInstrumentation;
        private LinearPermissionInstrumentation linearPermissionInstrumentation;
        private NoninterferenceInstrumentation noninterferenceInstrumentation;
        
        private YieldingProcInstrumentation(
            CivlTypeChecker civlTypeChecker,
            LinearTypeChecker linearTypeChecker,
            LinearPermissionInstrumentation linearPermissionInstrumentation,
            int layerNum,
            Dictionary<Absy, Absy> absyMap,
            HashSet<Procedure> yieldingProcs)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.layerNum = layerNum;
            this.absyMap = absyMap;
            this.yieldingProcs = yieldingProcs;
            this.linearPermissionInstrumentation = linearPermissionInstrumentation;
            parallelCallPreconditionCheckers = new Dictionary<string, Procedure>();
            noninterferenceCheckerDecls = new List<Declaration>();

            List<Variable> inputs = new List<Variable>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                inputs.Add(linearTypeChecker.LinearDomainInFormal(domainName));
            }
            foreach (Variable g in civlTypeChecker.GlobalVariables)
            {
                inputs.Add(OldGlobalFormal(g));
            }
            wrapperNoninterferenceCheckerProc = new Procedure(Token.NoToken, $"Wrapper_NoninterferenceChecker_{layerNum}", new List<TypeVariable>(),
                inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            CivlUtil.AddInlineAttribute(wrapperNoninterferenceCheckerProc);
        }

        private Implementation WrapperNoninterferenceCheckerImpl()
        {
            List<Variable> inputs = new List<Variable>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                inputs.Add(linearTypeChecker.LinearDomainInFormal(domainName));
            }

            foreach (Variable g in civlTypeChecker.GlobalVariables)
            {
                inputs.Add(OldGlobalFormal(g));
            }

            List<Block> blocks = new List<Block>();
            TransferCmd transferCmd = new ReturnCmd(Token.NoToken);
            if (noninterferenceCheckerDecls.Count > 0)
            {
                List<Block> blockTargets = new List<Block>();
                List<String> labelTargets = new List<String>();
                int labelCount = 0;
                foreach (Procedure proc in noninterferenceCheckerDecls.OfType<Procedure>())
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

            var yieldImpl = new Implementation(Token.NoToken, wrapperNoninterferenceCheckerProc.Name, new List<TypeVariable>(), inputs,
                new List<Variable>(), new List<Variable>(), blocks);
            yieldImpl.Proc = wrapperNoninterferenceCheckerProc;
            CivlUtil.AddInlineAttribute(yieldImpl);
            return yieldImpl;
        }

        private Formal OldGlobalFormal(Variable v)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, $"civl_global_old_{v.Name}", v.TypedIdent.Type), true);
        }

        private void TransformImpl(Implementation originalImpl, Implementation impl)
        {
            // initialize globalSnapshotInstrumentation
            globalSnapshotInstrumentation = new GlobalSnapshotInstrumentation(civlTypeChecker);

            // initialize refinementInstrumentation
            YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[originalImpl.Proc];
            if (yieldingProc.upperLayer == this.layerNum)
            {
                if (yieldingProc is ActionProc)
                {
                    refinementInstrumentation = new ActionRefinementInstrumentation(
                        civlTypeChecker,
                        impl,
                        originalImpl,
                        globalSnapshotInstrumentation.OldGlobalMap);
                }
                else
                {
                    refinementInstrumentation = new SkipRefinementInstrumentation(
                        civlTypeChecker,
                        yieldingProc,
                        globalSnapshotInstrumentation.OldGlobalMap);
                }
            }
            else
            {
                refinementInstrumentation = new RefinementInstrumentation();
            }

            var allYieldPredicates = CollectYields(impl);
            
            // initialize noninterferenceInstrumentation
            if (CommandLineOptions.Clo.TrustNonInterference)
            {
                noninterferenceInstrumentation = new NoneNoninterferenceInstrumentation();
            }
            else
            {
                noninterferenceCheckerDecls.AddRange(
                    NoninterferenceChecker.CreateNoninterferenceCheckers(civlTypeChecker, linearTypeChecker, layerNum, absyMap, impl, allYieldPredicates));
                noninterferenceInstrumentation = new SomeNoninterferenceInstrumentation(
                    civlTypeChecker,
                    linearTypeChecker,
                    linearPermissionInstrumentation,
                    globalSnapshotInstrumentation.OldGlobalMap, 
                    wrapperNoninterferenceCheckerProc);
            }

            DesugarConcurrency(impl, allYieldPredicates);

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
            return new Block(Token.NoToken, "civl_init", initCmds, gotoCmd);
        }

        private void ComputeYieldingLoops(
            Implementation impl,
            out HashSet<Block> yieldingLoopHeaders, 
            out HashSet<Block> blocksInYieldingLoops)
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
            blocksInYieldingLoops = GetBlocksInAllNaturalLoops(yieldingLoopHeaders, graph);
        }

        private HashSet<Block> GetBlocksInAllNaturalLoops(HashSet<Block> headers, Graph<Block> g)
        {
            var allBlocksInNaturalLoops = new HashSet<Block>();
            foreach (Block header in headers)
            {
                foreach (Block source in g.BackEdgeNodes(header))
                {
                    g.NaturalLoops(header, source).Iter(b => allBlocksInNaturalLoops.Add(b));
                }
            }
            return allBlocksInNaturalLoops;
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

        private void AddEdge(GotoCmd gotoCmd, Block b)
        {
            gotoCmd.labelNames.Add(b.Label);
            gotoCmd.labelTargets.Add(b);
        }

        private void DesugarConcurrency(Implementation impl, Dictionary<YieldCmd, List<PredicateCmd>> allYieldPredicates)
        {
            var noninterferenceCheckerBlock = CreateNoninterferenceCheckerBlock();
            var refinementCheckerBlock = CreateRefinementCheckerBlock();
            var refinementCheckerForYieldingLoopsBlock = CreateRefinementCheckerBlockForYieldingLoops();
            var returnBlock = CreateReturnBlock();
            SplitBlocks(impl);
            
            HashSet<Block> yieldingLoopHeaders;
            HashSet<Block> blocksInYieldingLoops;
            ComputeYieldingLoops(impl, out yieldingLoopHeaders, out blocksInYieldingLoops);
            foreach (Block header in yieldingLoopHeaders)
            {
                foreach (Block pred in header.Predecessors)
                {
                    var gotoCmd = pred.TransferCmd as GotoCmd;
                    AddEdge(gotoCmd, noninterferenceCheckerBlock);
                    if (blocksInYieldingLoops.Contains(pred))
                    {
                        AddEdge(gotoCmd, refinementCheckerForYieldingLoopsBlock);
                    }
                    else
                    {
                        AddEdge(gotoCmd, refinementCheckerBlock);
                    }
                }
                List<Cmd> firstCmds;
                List<Cmd> secondCmds;
                SplitCmds(header.Cmds, out firstCmds, out secondCmds);
                List<Cmd> newCmds = new List<Cmd>();
                newCmds.AddRange(firstCmds);
                newCmds.AddRange(globalSnapshotInstrumentation.CreateUpdatesToOldGlobalVars());
                newCmds.AddRange(refinementInstrumentation.CreateUpdatesToOldOutputVars());
                newCmds.AddRange(noninterferenceInstrumentation.CreateUpdatesToPermissionCollector(header));
                newCmds.AddRange(secondCmds);
                header.Cmds = newCmds;
            }

            // add jumps to noninterferenceCheckerBlock and returnBlock
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
                        AddEdge(gotoCmd, noninterferenceCheckerBlock);
                        if (blocksInYieldingLoops.Contains(b))
                        {
                            AddEdge(gotoCmd, refinementCheckerForYieldingLoopsBlock);
                        }
                        else
                        {
                            AddEdge(gotoCmd, refinementCheckerBlock);
                        }
                    }
                }
                else
                {
                    b.TransferCmd = new GotoCmd(b.TransferCmd.tok, new List<string> { returnBlock.Label }, new List<Block> { returnBlock });
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
                        if (!blocksInYieldingLoops.Contains(b))
                        {
                            newCmds.AddRange(refinementInstrumentation.CreateUpdatesToRefinementVars());
                        }
                        var yieldPredicates = allYieldPredicates[yieldCmd];
                        newCmds.AddRange(yieldPredicates);
                        newCmds.AddRange(DesugarYieldCmd(yieldCmd, yieldPredicates));
                        newCmds.AddRange(b.cmds.GetRange(1 + yieldPredicates.Count, b.cmds.Count - (1 + yieldPredicates.Count)));
                        b.cmds = newCmds;
                    }
                    else if (cmd is CallCmd callCmd && yieldingProcs.Contains(callCmd.Proc))
                    {
                        List<Cmd> newCmds = new List<Cmd>();
                        if (!blocksInYieldingLoops.Contains(b))
                        {
                            newCmds.AddRange(refinementInstrumentation.CreateUpdatesToRefinementVars());
                        }
                        newCmds.Add(callCmd);
                        if (civlTypeChecker.GlobalVariables.Count() > 0)
                        {
                            newCmds.AddRange(refinementInstrumentation.CreateAssumeCmds());
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
                        if (!blocksInYieldingLoops.Contains(b))
                        {
                            newCmds.AddRange(refinementInstrumentation.CreateUpdatesToRefinementVars());
                        }
                        newCmds.AddRange(DesugarParCallCmd(parCallCmd));
                        if (civlTypeChecker.GlobalVariables.Count() > 0)
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

            impl.Blocks.Add(noninterferenceCheckerBlock);
            impl.Blocks.Add(refinementCheckerBlock);
            impl.Blocks.Add(refinementCheckerForYieldingLoopsBlock);
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

        private Block CreateNoninterferenceCheckerBlock()
        {
            var newCmds = new List<Cmd>();
            newCmds.AddRange(noninterferenceInstrumentation.CreateCallToYieldProc());
            newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
            return new Block(Token.NoToken, "NoninterferenceChecker", newCmds, new ReturnCmd(Token.NoToken));
        }

        private Block CreateRefinementCheckerBlock()
        {
            var newCmds = new List<Cmd>();
            newCmds.AddRange(refinementInstrumentation.CreateAssertCmds());
            newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
            return new Block(Token.NoToken, "RefinementChecker", newCmds, new ReturnCmd(Token.NoToken));
        }

        private Block CreateRefinementCheckerBlockForYieldingLoops()
        {
            var newCmds = new List<Cmd>();
            newCmds.AddRange(refinementInstrumentation.CreateUnchangedGlobalsAssertCmds());
            newCmds.AddRange(refinementInstrumentation.CreateUnchangedOutputsAssertCmds());
            newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
            return new Block(Token.NoToken, "RefinementCheckerForYieldingLoops", newCmds, new ReturnCmd(Token.NoToken));
        }

        private Block CreateReturnBlock()
        {
            var returnBlockCmds = new List<Cmd>();
            returnBlockCmds.AddRange(refinementInstrumentation.CreateUpdatesToRefinementVars());
            returnBlockCmds.AddRange(refinementInstrumentation.CreateReturnAssertCmds());
            return new Block(Token.NoToken, "ReturnChecker", returnBlockCmds, new ReturnCmd(Token.NoToken));
        }

        private List<Cmd> DesugarYieldCmd(
            YieldCmd yieldCmd,
            List<PredicateCmd> cmds)
        {
            var newCmds = new List<Cmd>();
            if (civlTypeChecker.GlobalVariables.Count() > 0)
            {
                newCmds.Add(new HavocCmd(Token.NoToken, civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList()));
                newCmds.AddRange(refinementInstrumentation.CreateAssumeCmds());
            }
            newCmds.AddRange(linearPermissionInstrumentation.DisjointnessAssumeCmds(yieldCmd, true));
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
            string procName = "ParallelCallPreconditionChecker";
            foreach (CallCmd callCmd in parCallCmd.CallCmds)
            {
                procName = procName + "_" + callCmd.Proc.Name;
                ins.AddRange(callCmd.Ins);
                outs.AddRange(callCmd.Outs);
            }

            if (!parallelCallPreconditionCheckers.ContainsKey(procName))
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
                parallelCallPreconditionCheckers[procName] = new Procedure(Token.NoToken, procName,
                    new List<TypeVariable>(), inParams, outParams, requiresSeq,
                    civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList(), ensuresSeq);
            }

            Procedure proc = parallelCallPreconditionCheckers[procName];
            CallCmd checkerCallCmd = new CallCmd(parCallCmd.tok, proc.Name, ins, outs, parCallCmd.Attributes);
            checkerCallCmd.Proc = proc;
            newCmds.Add(checkerCallCmd);
            return newCmds;
        }

        private Formal ParCallDesugarFormal(Variable v, int count, bool incoming)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, $"civl_{count}_{v.Name}", v.TypedIdent.Type), incoming);
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
