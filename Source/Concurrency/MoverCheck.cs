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
        HashSet<Tuple<AtomicActionInfo, AtomicActionInfo>> commutativityCheckerCache;
        HashSet<Tuple<AtomicActionInfo, AtomicActionInfo>> gatePreservationCheckerCache;
        HashSet<Tuple<AtomicActionInfo, AtomicActionInfo>> failurePreservationCheckerCache;

        private MoverCheck(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.civlTypeChecker = civlTypeChecker;
            this.decls = decls;
            this.commutativityCheckerCache = new HashSet<Tuple<AtomicActionInfo, AtomicActionInfo>>();
            this.gatePreservationCheckerCache = new HashSet<Tuple<AtomicActionInfo, AtomicActionInfo>>();
            this.failurePreservationCheckerCache = new HashSet<Tuple<AtomicActionInfo, AtomicActionInfo>>();
        }

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            if (civlTypeChecker.procToActionInfo.Count == 0)
                return;

            List<ActionInfo> sortedByCreatedLayerNum = new List<ActionInfo>(civlTypeChecker.procToActionInfo.Values.Where(x => x is AtomicActionInfo && !x.isExtern));
            sortedByCreatedLayerNum.Sort((x, y) => { return (x.createdAtLayerNum == y.createdAtLayerNum) ? 0 : (x.createdAtLayerNum < y.createdAtLayerNum) ? -1 : 1; });
            List<ActionInfo> sortedByAvailableUptoLayerNum = new List<ActionInfo>(civlTypeChecker.procToActionInfo.Values.Where(x => x is AtomicActionInfo && !x.isExtern));
            sortedByAvailableUptoLayerNum.Sort((x, y) => { return (x.availableUptoLayerNum == y.availableUptoLayerNum) ? 0 : (x.availableUptoLayerNum < y.availableUptoLayerNum) ? -1 : 1; });

            Dictionary<int, HashSet<AtomicActionInfo>> pools = new Dictionary<int, HashSet<AtomicActionInfo>>();
            int indexIntoSortedByCreatedLayerNum = 0;
            int indexIntoSortedByAvailableUptoLayerNum = 0;
            HashSet<AtomicActionInfo> currPool = new HashSet<AtomicActionInfo>();
            while (indexIntoSortedByCreatedLayerNum < sortedByCreatedLayerNum.Count)
            {
                var currLayerNum = sortedByCreatedLayerNum[indexIntoSortedByCreatedLayerNum].createdAtLayerNum;
                pools[currLayerNum] = new HashSet<AtomicActionInfo>(currPool);
                while (indexIntoSortedByCreatedLayerNum < sortedByCreatedLayerNum.Count)
                {
                    var actionInfo = sortedByCreatedLayerNum[indexIntoSortedByCreatedLayerNum] as AtomicActionInfo;
                    if (actionInfo.createdAtLayerNum > currLayerNum) break;
                    pools[currLayerNum].Add(actionInfo);
                    indexIntoSortedByCreatedLayerNum++;
                }
                while (indexIntoSortedByAvailableUptoLayerNum < sortedByAvailableUptoLayerNum.Count)
                {
                    var actionInfo = sortedByAvailableUptoLayerNum[indexIntoSortedByAvailableUptoLayerNum] as AtomicActionInfo;
                    if (actionInfo.availableUptoLayerNum > currLayerNum) break;
                    pools[currLayerNum].Remove(actionInfo);
                    indexIntoSortedByAvailableUptoLayerNum++;
                }
                currPool = pools[currLayerNum];
            }

            // No atomic action has mover type Top
            Debug.Assert(pools.All(l => l.Value.All(a => a.moverType != MoverType.Top)));

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
            foreach (AtomicActionInfo atomicActionInfo in sortedByCreatedLayerNum)
            {
                if (atomicActionInfo.IsLeftMover && atomicActionInfo.hasAssumeCmd)
                {
                    moverChecking.CreateNonBlockingChecker(program, atomicActionInfo);
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

        private void CreateCommutativityChecker(Program program, AtomicActionInfo first, AtomicActionInfo second)
        {
            if (first == second && first.thatInParams.Count == 0 && first.thatOutParams.Count == 0)
                return;
            if (first.CommutesWith(second))
                return;
            if (!commutativityCheckerCache.Add(new Tuple<AtomicActionInfo, AtomicActionInfo>(first, second)))
                return;

            List<Variable> inputs  = Enumerable.Union(first.thatInParams, second.thisInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.thatOutParams, second.thisOutParams).ToList();
            List<Variable> locals  = Enumerable.Union(first.thatAction.LocVars, second.thisAction.LocVars).ToList();
            List<Block> firstBlocks = CloneBlocks(first.thatAction.Blocks);
            List<Block> secondBlocks = CloneBlocks(second.thisAction.Blocks);
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
            requires.Add(DisjointnessRequires(program, first.thatInParams.Union(second.thisInParams), frame));
            foreach (AssertCmd assertCmd in Enumerable.Union(first.thatGate, second.thisGate))
                requires.Add(new Requires(false, assertCmd.Expr));

            var transitionRelationComputation = new TransitionRelationComputation(program, first, second, frame, new HashSet<Variable>());
            Expr transitionRelation = transitionRelationComputation.TransitionRelationCompute();
            {
                List<Block> bs = new List<Block> { blocks[0] };
                List<string> ls = new List<string> { blocks[0].Label };
                var initBlock = new Block(Token.NoToken, string.Format("{0}_{1}_init", first.proc.Name, second.proc.Name), transitionRelationComputation.TriggerAssumes(), new GotoCmd(Token.NoToken, ls, bs));
                blocks.Insert(0, initBlock);
            }
            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(program, first.thatOutParams.Union(second.thisInParams), frame).Union(DisjointnessExpr(program, first.thatOutParams.Union(second.thisOutParams), frame));
            Ensures ensureCheck = new Ensures(false, Expr.Imp(Expr.And(linearityAssumes), transitionRelation));
            ensureCheck.ErrorData = string.Format("Commutativity check between {0} and {1} failed", first.proc.Name, second.proc.Name);
            List<Ensures> ensures = new List<Ensures> { ensureCheck };
            
            string checkerName = string.Format("CommutativityChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = civlTypeChecker.SharedVariables.Select(x => Expr.Ident(x)).ToList();

            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateGatePreservationChecker(Program program, AtomicActionInfo first, AtomicActionInfo second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;
            if (!gatePreservationCheckerCache.Add(new Tuple<AtomicActionInfo, AtomicActionInfo>(first, second)))
                return;

            List<Variable> inputs = Enumerable.Union(first.thatInParams, second.thisInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.thatOutParams, second.thisOutParams).ToList();
            List<Variable> locals = new List<Variable>(second.thisAction.LocVars);
            List<Block> secondBlocks = CloneBlocks(second.thisAction.Blocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>();
            List<Ensures> ensures = new List<Ensures>();
            requires.Add(DisjointnessRequires(program, first.thatInParams.Union(second.thisInParams), frame));
            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(program, first.thatInParams.Union(second.thisOutParams), frame);
            foreach (AssertCmd assertCmd in second.thisGate)
                requires.Add(new Requires(false, assertCmd.Expr));
            
            foreach (AssertCmd assertCmd in first.thatGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
                Ensures ensureCheck = new Ensures(assertCmd.tok, false, Expr.Imp(Expr.And(linearityAssumes), assertCmd.Expr), null);
                ensureCheck.ErrorData = string.Format("Gate not preserved by {0}", second.proc.Name);
                ensures.Add(ensureCheck);
            }
            string checkerName = string.Format("GatePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = civlTypeChecker.SharedVariables.Select(x => Expr.Ident(x)).ToList();

            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, secondBlocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateFailurePreservationChecker(Program program, AtomicActionInfo first, AtomicActionInfo second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;
            if (!failurePreservationCheckerCache.Add(new Tuple<AtomicActionInfo, AtomicActionInfo>(first, second)))
                return;

            List<Variable> inputs = Enumerable.Union(first.thatInParams, second.thisInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.thatOutParams, second.thisOutParams).ToList();
            List<Variable> locals = new List<Variable>(second.thisAction.LocVars);
            List<Block> secondBlocks = CloneBlocks(second.thisAction.Blocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>();
            requires.Add(DisjointnessRequires(program, first.thatInParams.Union(second.thisInParams), frame));
            Expr gateExpr = Expr.Not(Expr.And(first.thatGate.Select(a => a.Expr)));
            gateExpr.Type = Type.Bool; // necessary?
            requires.Add(new Requires(false, gateExpr));
            foreach (AssertCmd assertCmd in second.thisGate)
                requires.Add(new Requires(false, assertCmd.Expr));

            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(program, first.thatInParams.Union(second.thisOutParams), frame);
            Ensures ensureCheck = new Ensures(false, Expr.Imp(Expr.And(linearityAssumes), gateExpr));
            ensureCheck.ErrorData = string.Format("Gate failure of {0} not preserved by {1}", first.proc.Name, second.proc.Name);
            List<Ensures> ensures = new List<Ensures> { ensureCheck };
            
            string checkerName = string.Format("FailurePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = civlTypeChecker.SharedVariables.Select(x => Expr.Ident(x)).ToList();

            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, secondBlocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateNonBlockingChecker(Program program, AtomicActionInfo second)
        {
            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(second.thisInParams);

            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);
            
            List<Requires> requires = new List<Requires>();
            requires.Add(DisjointnessRequires(program, second.thisInParams, frame));
            foreach (AssertCmd assertCmd in second.thisGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }

            HashSet<Variable> postExistVars = new HashSet<Variable>();
            postExistVars.UnionWith(frame);
            postExistVars.UnionWith(second.thisOutParams);
            Expr ensuresExpr = (new TransitionRelationComputation(program, second, frame, postExistVars)).TransitionRelationCompute();
            Ensures ensureCheck = new Ensures(false, ensuresExpr);
            ensureCheck.ErrorData = string.Format("{0} is blocking", second.proc.Name);
            List<Ensures> ensures = new List<Ensures> { ensureCheck };

            List<Block> blocks = new List<Block> { new Block(Token.NoToken, "L", new List<Cmd>(), new ReturnCmd(Token.NoToken)) };
            string checkerName = string.Format("NonBlockingChecker_{0}", second.proc.Name);
            List<IdentifierExpr> globalVars = civlTypeChecker.SharedVariables.Select(x => Expr.Ident(x)).ToList();
            
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), new List<Variable>(), blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }
    }
}