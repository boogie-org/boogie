using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public class MoverCheck
    {
        LinearTypeChecker linearTypeChecker;
        CivlTypeChecker civlTypeChecker;
        List<Declaration> decls;

        HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>> commutativityCheckerCache;
        HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>> gatePreservationCheckerCache;
        HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>> failurePreservationCheckerCache;

        private MoverCheck(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.civlTypeChecker = civlTypeChecker;
            this.decls = decls;
            this.commutativityCheckerCache = new HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>>();
            this.gatePreservationCheckerCache = new HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>>();
            this.failurePreservationCheckerCache = new HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>>();
        }

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            if (civlTypeChecker.procToAtomicAction.Count == 0)
                return;

            MoverCheck moverChecking = new MoverCheck(linearTypeChecker, civlTypeChecker, decls);

            foreach (int layer in civlTypeChecker.allAtomicActionLayers)
            {
                var pool = civlTypeChecker.procToAtomicAction.Values.Where(a => a.layerRange.Contains(layer));

                var moverChecks =
                    from first in pool
                    from second in pool
                    where first.moverType != MoverType.Atomic
                    select new { First = first, Second = second };

                foreach (var moverCheck in moverChecks)
                {
                    var first = moverCheck.First.layerToActionCopy[layer];
                    var second = moverCheck.Second.layerToActionCopy[layer];

                    if (moverCheck.First.IsRightMover)
                    {
                        moverChecking.CreateCommutativityChecker(first, second);
                        moverChecking.CreateGatePreservationChecker(second, first);
                    }
                    if (moverCheck.First.IsLeftMover)
                    {
                        moverChecking.CreateCommutativityChecker(second, first);
                        moverChecking.CreateGatePreservationChecker(first, second);
                        moverChecking.CreateFailurePreservationChecker(second, first);
                    }
                }
                foreach (AtomicAction atomicAction in pool.Where(a => a.IsLeftMover))
                {
                    moverChecking.CreateNonBlockingChecker(atomicAction.layerToActionCopy[layer]);
                }
            }
        }

        private static List<Block> CloneBlocks(List<Block> blocks)
        {
            Dictionary<Block, Block> blockMap = new Dictionary<Block, Block>();
            List<Block> otherBlocks = new List<Block>();
            foreach (Block block in blocks)
            {
                List<Cmd> otherCmds = new List<Cmd>();
                foreach (Cmd cmd in block.Cmds)
                {
                    otherCmds.Add(cmd);
                }
                Block otherBlock = new Block();
                otherBlock.tok = block.tok;
                otherBlock.Cmds = otherCmds;
                otherBlock.Label = block.Label;
                otherBlocks.Add(otherBlock);
                blockMap[block] = otherBlock;
            }
            foreach (Block block in blocks)
            {
                if (block.TransferCmd is ReturnCmd)
                {
                    blockMap[block].TransferCmd = new ReturnCmd(block.TransferCmd.tok);
                    continue;
                }
                List<Block> otherGotoCmdLabelTargets = new List<Block>();
                List<string> otherGotoCmdLabelNames = new List<string>();
                GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    otherGotoCmdLabelTargets.Add(blockMap[target]);
                    otherGotoCmdLabelNames.Add(blockMap[target].Label);
                }
                blockMap[block].TransferCmd = new GotoCmd(block.TransferCmd.tok, otherGotoCmdLabelNames, otherGotoCmdLabelTargets);
            }
            return otherBlocks;
        }

        private static List<Block> ComposeBlocks(AtomicActionCopy first, AtomicActionCopy second)
        {
            List<Block> firstBlocks = CloneBlocks(first.firstAction.Blocks);
            List<Block> secondBlocks = CloneBlocks(second.secondAction.Blocks);
            foreach (Block b in firstBlocks.Where(b => b.TransferCmd is ReturnCmd))
            {
                List<Block>  bs = new List<Block>  { secondBlocks[0] };
                List<string> ls = new List<string> { secondBlocks[0].Label };
                b.TransferCmd = new GotoCmd(b.tok, ls, bs);
            }
            return Enumerable.Union(firstBlocks, secondBlocks).ToList();
        }

        private IEnumerable<Expr> DisjointnessExpr(IEnumerable<Variable> paramVars, HashSet<Variable> frame)
        {
            Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                domainNameToScope[domainName] = new HashSet<Variable>();
            }
            foreach (Variable v in paramVars.Union(frame))
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
                domainNameToScope[domainName].Add(v);
            }
            foreach (string domainName in domainNameToScope.Keys)
            {
                yield return linearTypeChecker.DisjointnessExpr(domainName, domainNameToScope[domainName]);
            }
        }

        private Requires DisjointnessRequires(IEnumerable<Variable> paramVars, HashSet<Variable> frame)
        {
            return new Requires(false, Expr.And(DisjointnessExpr(paramVars, frame)));
        }

        private void AddChecker(string checkerName, List<Variable> inputs, List<Variable> outputs, List<Variable> locals, List<Requires> requires, List<Ensures> ensures, List<Block> blocks)
        {
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, civlTypeChecker.sharedVariableIdentifiers, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateCommutativityChecker(AtomicActionCopy first, AtomicActionCopy second)
        {
            if (first == second && first.firstInParams.Count == 0 && first.firstOutParams.Count == 0)
                return;
            if (first.TriviallyCommutesWith(second))
                return;
            if (!commutativityCheckerCache.Add(Tuple.Create(first, second)))
                return;

            List<Variable> inputs  = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();
            List<Variable> locals  = Enumerable.Union(first.firstAction.LocVars, second.secondAction.LocVars).ToList();
            List<Block> blocks = ComposeBlocks(first, second);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(first.actionUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);
            
            List<Requires> requires = new List<Requires>();
            requires.Add(DisjointnessRequires(first.firstInParams.Union(second.secondInParams).Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame));
            foreach (AssertCmd assertCmd in Enumerable.Union(first.firstGate, second.secondGate))
                requires.Add(new Requires(false, assertCmd.Expr));
            
            var transitionRelationComputation = new TransitionRelationComputation(first, second, frame, new HashSet<Variable>());
            Expr transitionRelation = transitionRelationComputation.TransitionRelationCompute();
            {
                List<Block> bs = new List<Block> { blocks[0] };
                List<string> ls = new List<string> { blocks[0].Label };
                var initBlock = new Block(Token.NoToken, string.Format("{0}_{1}_init", first.proc.Name, second.proc.Name), transitionRelationComputation.TriggerAssumes(), new GotoCmd(Token.NoToken, ls, bs));
                blocks.Insert(0, initBlock);
            }

            var secondInParamsFiltered = second.secondInParams.Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_IN);
            IEnumerable<Expr> linearityAssumes = Enumerable.Union(
                DisjointnessExpr(first.firstOutParams.Union(secondInParamsFiltered), frame),
                DisjointnessExpr(first.firstOutParams.Union(second.secondOutParams), frame));
            // TODO: add further disjointness expressions?
            Ensures ensureCheck = new Ensures(first.proc.tok, false, Expr.Imp(Expr.And(linearityAssumes), transitionRelation), null);
            ensureCheck.ErrorData = string.Format("Commutativity check between {0} and {1} failed", first.proc.Name, second.proc.Name);
            List<Ensures> ensures = new List<Ensures> { ensureCheck };
            
            string checkerName = string.Format("CommutativityChecker_{0}_{1}", first.proc.Name, second.proc.Name);

            AddChecker(checkerName, inputs, outputs, locals, requires, ensures, blocks);
        }

        private void CreateGatePreservationChecker(AtomicActionCopy first, AtomicActionCopy second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;
            if (!gatePreservationCheckerCache.Add(Tuple.Create(first, second)))
                return;

            List<Variable> inputs = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();
            List<Variable> locals = new List<Variable>(second.secondAction.LocVars);
            List<Block> blocks = CloneBlocks(second.secondAction.Blocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>();
            List<Ensures> ensures = new List<Ensures>();
            requires.Add(DisjointnessRequires(first.firstInParams.Union(second.secondInParams).Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame));
            foreach (AssertCmd assertCmd in second.secondGate)
                requires.Add(new Requires(false, assertCmd.Expr));
            
            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(first.firstInParams.Union(second.secondOutParams), frame);
            foreach (AssertCmd assertCmd in first.firstGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
                Ensures ensureCheck = new Ensures(assertCmd.tok, false, Expr.Imp(Expr.And(linearityAssumes), assertCmd.Expr), null);
                ensureCheck.ErrorData = string.Format("Gate of {0} not preserved by {1}", first.proc.Name, second.proc.Name);
                ensures.Add(ensureCheck);
            }
            string checkerName = string.Format("GatePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            
            AddChecker(checkerName, inputs, outputs, locals, requires, ensures, blocks);
        }

        private void CreateFailurePreservationChecker(AtomicActionCopy first, AtomicActionCopy second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;
            if (!failurePreservationCheckerCache.Add(Tuple.Create(first, second)))
                return;

            List<Variable> inputs = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();
            List<Variable> locals = new List<Variable>(second.secondAction.LocVars);
            List<Block> blocks = CloneBlocks(second.secondAction.Blocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>();
            requires.Add(DisjointnessRequires(first.firstInParams.Union(second.secondInParams).Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame));
            Expr firstNegatedGate = Expr.Not(Expr.And(first.firstGate.Select(a => a.Expr)));
            firstNegatedGate.Type = Type.Bool; // necessary?
            requires.Add(new Requires(false, firstNegatedGate));
            foreach (AssertCmd assertCmd in second.secondGate)
                requires.Add(new Requires(false, assertCmd.Expr));

            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(first.firstInParams.Union(second.secondOutParams), frame);
            Ensures ensureCheck = new Ensures(first.proc.tok, false, Expr.Imp(Expr.And(linearityAssumes), firstNegatedGate), null);
            ensureCheck.ErrorData = string.Format("Gate failure of {0} not preserved by {1}", first.proc.Name, second.proc.Name);
            List<Ensures> ensures = new List<Ensures> { ensureCheck };
            
            string checkerName = string.Format("FailurePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);

            AddChecker(checkerName, inputs, outputs, locals, requires, ensures, blocks);
        }

        private void CreateNonBlockingChecker(AtomicActionCopy second)
        {
            if (!second.HasAssumeCmd) return;

            List<Variable> inputs = new List<Variable>(second.secondInParams);
            List<Variable> outputs = new List<Variable>();
            List<Variable> locals = new List<Variable>();
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);
            
            List<Requires> requires = new List<Requires>();
            requires.Add(DisjointnessRequires(second.secondInParams.Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame));
            foreach (AssertCmd assertCmd in second.secondGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }
            List<Ensures> ensures = new List<Ensures>();

            HashSet<Variable> postExistVars = new HashSet<Variable>();
            postExistVars.UnionWith(frame);
            postExistVars.UnionWith(second.secondOutParams);
            Expr nonBlockingExpr = (new TransitionRelationComputation(second, frame, postExistVars)).TransitionRelationCompute();
            AssertCmd nonBlockingAssert = new AssertCmd(second.proc.tok, nonBlockingExpr);
            nonBlockingAssert.ErrorData = string.Format("Non-blocking check for {0} failed", second.proc.Name);
            List<Block> blocks = new List<Block>{ new Block(second.proc.tok, "L", new List<Cmd>() { nonBlockingAssert }, new ReturnCmd(Token.NoToken)) };

            string checkerName = string.Format("NonBlockingChecker_{0}", second.proc.Name);
            
            AddChecker(checkerName, inputs, outputs, locals, requires, ensures, blocks);
        }
    }
}