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
        HashSet<Tuple<AtomicAction, AtomicAction>> commutativityCheckerCache;
        HashSet<Tuple<AtomicAction, AtomicAction>> gatePreservationCheckerCache;
        HashSet<Tuple<AtomicAction, AtomicAction>> failurePreservationCheckerCache;

        private MoverCheck(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.civlTypeChecker = civlTypeChecker;
            this.decls = decls;
            this.commutativityCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
            this.gatePreservationCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
            this.failurePreservationCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
        }

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            if (civlTypeChecker.procToAtomicAction.Count == 0)
                return;

            List<AtomicAction> sortedByCreatedLayerNum = civlTypeChecker.procToAtomicAction.Values
                .OrderBy(a => a.layerRange.lowerLayerNum).ToList();
            List<AtomicAction> sortedByAvailableUptoLayerNum = civlTypeChecker.procToAtomicAction.Values
                .OrderBy(a => a.layerRange.upperLayerNum).ToList();

            Dictionary<int, HashSet<AtomicAction>> pools = new Dictionary<int, HashSet<AtomicAction>>();
            int indexIntoSortedByCreatedLayerNum = 0;
            int indexIntoSortedByAvailableUptoLayerNum = 0;
            HashSet<AtomicAction> currPool = new HashSet<AtomicAction>();
            while (indexIntoSortedByCreatedLayerNum < sortedByCreatedLayerNum.Count)
            {
                var currLayerNum = sortedByCreatedLayerNum[indexIntoSortedByCreatedLayerNum].layerRange.lowerLayerNum;
                pools[currLayerNum] = new HashSet<AtomicAction>(currPool);
                while (indexIntoSortedByCreatedLayerNum < sortedByCreatedLayerNum.Count)
                {
                    var action = sortedByCreatedLayerNum[indexIntoSortedByCreatedLayerNum];
                    if (action.layerRange.lowerLayerNum > currLayerNum) break;
                    pools[currLayerNum].Add(action);
                    indexIntoSortedByCreatedLayerNum++;
                }
                while (indexIntoSortedByAvailableUptoLayerNum < sortedByAvailableUptoLayerNum.Count)
                {
                    var action = sortedByAvailableUptoLayerNum[indexIntoSortedByAvailableUptoLayerNum];
                    if (action.layerRange.upperLayerNum >= currLayerNum) break;
                    pools[currLayerNum].Remove(action);
                    indexIntoSortedByAvailableUptoLayerNum++;
                }
                currPool = pools[currLayerNum];
            }

            Program program = civlTypeChecker.program;
            MoverCheck moverChecking = new MoverCheck(linearTypeChecker, civlTypeChecker, decls);

            var moverChecks =
            from layer in pools.Keys
            from first in pools[layer]
            from second in pools[layer]
            where first.moverType != MoverType.Atomic
            select new { First = first, Second = second };

            foreach (var moverCheck in moverChecks)
            {
                var first = moverCheck.First;
                var second = moverCheck.Second;

                if (first.IsRightMover)
                {
                    moverChecking.CreateCommutativityChecker(program, first, second);
                    moverChecking.CreateGatePreservationChecker(program, second, first);
                }
                if (first.IsLeftMover)
                {
                    moverChecking.CreateCommutativityChecker(program, second, first);
                    moverChecking.CreateGatePreservationChecker(program, first, second);
                    moverChecking.CreateFailurePreservationChecker(program, second, first);
                }
            }
            foreach (AtomicAction atomicAction in sortedByCreatedLayerNum)
            {
                if (atomicAction.IsLeftMover && atomicAction.HasAssumeCmd)
                {
                    moverChecking.CreateNonBlockingChecker(program, atomicAction);
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
                otherBlock.Cmds = otherCmds;
                otherBlock.Label = block.Label;
                otherBlocks.Add(otherBlock);
                blockMap[block] = otherBlock;
            }
            foreach (Block block in blocks)
            {
                if (block.TransferCmd is ReturnCmd) continue;
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

        private IEnumerable<Expr> DisjointnessExpr(Program program, IEnumerable<Variable> paramVars, HashSet<Variable> frame)
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
                if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                domainNameToScope[domainName].Add(v);
            }
            foreach (string domainName in domainNameToScope.Keys)
            {
                yield return linearTypeChecker.DisjointnessExpr(domainName, domainNameToScope[domainName]);
            }
        }

        private Requires DisjointnessRequires(Program program, IEnumerable<Variable> paramVars, HashSet<Variable> frame)
        {
            return new Requires(false, Expr.And(DisjointnessExpr(program, paramVars, frame)));
        }

        private void CreateCommutativityChecker(Program program, AtomicAction first, AtomicAction second)
        {
            if (first == second && first.firstInParams.Count == 0 && first.firstOutParams.Count == 0)
                return;
            if (first.TriviallyCommutesWith(second))
                return;
            if (!commutativityCheckerCache.Add(new Tuple<AtomicAction, AtomicAction>(first, second)))
                return;

            List<Variable> inputs  = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();
            List<Variable> locals  = Enumerable.Union(first.firstAction.LocVars, second.secondAction.LocVars).ToList();
            List<Block> firstBlocks = CloneBlocks(first.firstAction.Blocks);
            List<Block> secondBlocks = CloneBlocks(second.secondAction.Blocks);
            foreach (Block b in firstBlocks.Where(b => b.TransferCmd is ReturnCmd))
            {
                List<Block>  bs = new List<Block>  { secondBlocks[0] };
                List<string> ls = new List<string> { secondBlocks[0].Label };
                b.TransferCmd = new GotoCmd(Token.NoToken, ls, bs);
            }
            List<Block> blocks = Enumerable.Union(firstBlocks, secondBlocks).ToList();
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(first.actionUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);
            
            List<Requires> requires = new List<Requires>();
            requires.Add(DisjointnessRequires(program, first.firstInParams.Union(second.secondInParams), frame));
            foreach (AssertCmd assertCmd in Enumerable.Union(first.firstGate, second.secondGate))
                requires.Add(new Requires(false, assertCmd.Expr));
            
            var transitionRelationComputation = new TransitionRelationComputation(program, first, second, frame, new HashSet<Variable>());
            Expr transitionRelation = transitionRelationComputation.TransitionRelationCompute();
            {
                List<Block> bs = new List<Block> { blocks[0] };
                List<string> ls = new List<string> { blocks[0].Label };
                var initBlock = new Block(Token.NoToken, string.Format("{0}_{1}_init", first.proc.Name, second.proc.Name), transitionRelationComputation.TriggerAssumes(), new GotoCmd(Token.NoToken, ls, bs));
                blocks.Insert(0, initBlock);
            }

            var secondInParamsFiltered = second.secondInParams.Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_IN);
            IEnumerable<Expr> linearityAssumes = Enumerable.Union(
                DisjointnessExpr(program, first.firstOutParams.Union(secondInParamsFiltered), frame),
                DisjointnessExpr(program, first.firstOutParams.Union(second.secondOutParams), frame));
            // TODO: add further disjointness expressions?
            Ensures ensureCheck = new Ensures(false, Expr.Imp(Expr.And(linearityAssumes), transitionRelation));
            ensureCheck.ErrorData = string.Format("Commutativity check between {0} and {1} failed", first.proc.Name, second.proc.Name);
            List<Ensures> ensures = new List<Ensures> { ensureCheck };
            
            string checkerName = string.Format("CommutativityChecker_{0}_{1}", first.proc.Name, second.proc.Name);

            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, civlTypeChecker.sharedVariableIdentifiers, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateGatePreservationChecker(Program program, AtomicAction first, AtomicAction second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;
            if (!gatePreservationCheckerCache.Add(new Tuple<AtomicAction, AtomicAction>(first, second)))
                return;

            List<Variable> inputs = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();
            List<Variable> locals = new List<Variable>(second.secondAction.LocVars);
            List<Block> secondBlocks = CloneBlocks(second.secondAction.Blocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>();
            List<Ensures> ensures = new List<Ensures>();
            requires.Add(DisjointnessRequires(program, first.firstInParams.Union(second.secondInParams), frame));
            foreach (AssertCmd assertCmd in second.secondGate)
                requires.Add(new Requires(false, assertCmd.Expr));
            
            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(program, first.firstInParams.Union(second.secondOutParams), frame);
            foreach (AssertCmd assertCmd in first.firstGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
                Ensures ensureCheck = new Ensures(assertCmd.tok, false, Expr.Imp(Expr.And(linearityAssumes), assertCmd.Expr), null);
                ensureCheck.ErrorData = string.Format("Gate not preserved by {0}", second.proc.Name);
                ensures.Add(ensureCheck);
            }
            string checkerName = string.Format("GatePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, civlTypeChecker.sharedVariableIdentifiers, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, secondBlocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateFailurePreservationChecker(Program program, AtomicAction first, AtomicAction second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;
            if (!failurePreservationCheckerCache.Add(new Tuple<AtomicAction, AtomicAction>(first, second)))
                return;

            List<Variable> inputs = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();
            List<Variable> locals = new List<Variable>(second.secondAction.LocVars);
            List<Block> secondBlocks = CloneBlocks(second.secondAction.Blocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>();
            requires.Add(DisjointnessRequires(program, first.firstInParams.Union(second.secondInParams), frame));
            Expr gateExpr = Expr.Not(Expr.And(first.firstGate.Select(a => a.Expr)));
            gateExpr.Type = Type.Bool; // necessary?
            requires.Add(new Requires(false, gateExpr));
            foreach (AssertCmd assertCmd in second.secondGate)
                requires.Add(new Requires(false, assertCmd.Expr));

            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(program, first.firstInParams.Union(second.secondOutParams), frame);
            Ensures ensureCheck = new Ensures(false, Expr.Imp(Expr.And(linearityAssumes), gateExpr));
            ensureCheck.ErrorData = string.Format("Gate failure of {0} not preserved by {1}", first.proc.Name, second.proc.Name);
            List<Ensures> ensures = new List<Ensures> { ensureCheck };
            
            string checkerName = string.Format("FailurePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);

            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, civlTypeChecker.sharedVariableIdentifiers, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, secondBlocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateNonBlockingChecker(Program program, AtomicAction second)
        {
            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(second.secondInParams);

            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);
            
            List<Requires> requires = new List<Requires>();
            requires.Add(DisjointnessRequires(program, second.secondInParams, frame));
            foreach (AssertCmd assertCmd in second.secondGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }

            HashSet<Variable> postExistVars = new HashSet<Variable>();
            postExistVars.UnionWith(frame);
            postExistVars.UnionWith(second.secondOutParams);
            Expr ensuresExpr = (new TransitionRelationComputation(program, second, frame, postExistVars)).TransitionRelationCompute();
            Ensures ensureCheck = new Ensures(false, ensuresExpr);
            ensureCheck.ErrorData = string.Format("{0} is blocking", second.proc.Name);
            List<Ensures> ensures = new List<Ensures> { ensureCheck };

            List<Block> blocks = new List<Block> { new Block(Token.NoToken, "L", new List<Cmd>(), new ReturnCmd(Token.NoToken)) };
            string checkerName = string.Format("NonBlockingChecker_{0}", second.proc.Name);
            
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), requires, civlTypeChecker.sharedVariableIdentifiers, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), new List<Variable>(), blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }
    }
}