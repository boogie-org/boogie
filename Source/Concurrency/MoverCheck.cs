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

            Program program = civlTypeChecker.program;
            MoverCheck moverChecking = new MoverCheck(linearTypeChecker, civlTypeChecker, decls);
            foreach (int layerNum in pools.Keys)
            {
                foreach (AtomicActionInfo first in pools[layerNum])
                {
                    Debug.Assert(first.moverType != MoverType.Top);
                    if (first.moverType == MoverType.Atomic)
                        continue;
                    foreach (AtomicActionInfo second in pools[layerNum])
                    {
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

        public sealed class MyDuplicator : Duplicator
        {
            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                IdentifierExpr ret = (IdentifierExpr) base.VisitIdentifierExpr(node);
                if (ret.Decl is GlobalVariable)
                {
                    return new OldExpr(Token.NoToken, ret);
                }
                else
                {
                    return ret;
                }
            }
        }

        public class TransitionRelationComputation
        {
            private Program program;
            private AtomicActionInfo first;  // corresponds to that*
            private AtomicActionInfo second; // corresponds to this*
            private Stack<Cmd> cmdStack;
            private List<PathInfo> paths;
            private HashSet<Variable> frame;
            private HashSet<Variable> postExistVars;

            public TransitionRelationComputation(Program program, AtomicActionInfo second, HashSet<Variable> frame, HashSet<Variable> postExistVars)
            {
                this.postExistVars = postExistVars;
                this.frame = frame;
                TransitionRelationComputationHelper(program, null, second);
            }

            public TransitionRelationComputation(Program program, AtomicActionInfo first, AtomicActionInfo second, HashSet<Variable> frame, HashSet<Variable> postExistVars)
            {
                this.postExistVars = postExistVars;
                this.frame = frame;
                TransitionRelationComputationHelper(program, first, second);
            }

            private void TransitionRelationComputationHelper(Program program, AtomicActionInfo first, AtomicActionInfo second)
            {
                this.program = program;
                this.first = first;
                this.second = second;
                this.cmdStack = new Stack<Cmd>();
                this.paths = new List<PathInfo>();
                List<IdentifierExpr> havocVars = new List<IdentifierExpr>();
                this.second.thisOutParams.ForEach(v => havocVars.Add(Expr.Ident(v)));
                this.second.thisAction.LocVars.ForEach(v => havocVars.Add(Expr.Ident(v)));
                if (havocVars.Count > 0)
                {
                    HavocCmd havocCmd = new HavocCmd(Token.NoToken, havocVars);
                    cmdStack.Push(havocCmd);
                }
                Search(this.second.thisAction.Blocks[0], false);
            }

            private void Substitute(Dictionary<Variable, Expr> map, ref List<Expr> pathExprs, ref Dictionary<Variable, Expr> varToExpr)
            {
                Substitution subst = Substituter.SubstitutionFromHashtable(map);
                List<Expr> oldPathExprs = pathExprs;
                pathExprs = new List<Expr>();
                foreach (Expr pathExpr in oldPathExprs)
                {
                    pathExprs.Add(Substituter.Apply(subst, pathExpr));
                }
                Dictionary<Variable, Expr> oldVarToExpr = varToExpr;
                varToExpr = new Dictionary<Variable, Expr>();
                foreach (Variable v in oldVarToExpr.Keys)
                {
                    varToExpr[v] = Substituter.Apply(subst, oldVarToExpr[v]);
                }
            }

            struct PathInfo
            {
                public HashSet<Variable> existsVars;
                public Dictionary<Variable, Expr> varToExpr;
                public List<Expr> pathExprs;

                public PathInfo(HashSet<Variable> existsVars, Dictionary<Variable, Expr> varToExpr, List<Expr> pathExprs)
                {
                    this.existsVars = existsVars;
                    this.varToExpr = varToExpr;
                    this.pathExprs = pathExprs;
                }
            }
            
            private void FlattenAnd(Expr x, List<Expr> xs)
            {
                NAryExpr naryExpr = x as NAryExpr;
                if (naryExpr != null && naryExpr.Fun.FunctionName == "&&")
                {
                    FlattenAnd(naryExpr.Args[0], xs);
                    FlattenAnd(naryExpr.Args[1], xs);
                }
                else
                {
                    xs.Add(x);
                }
            }

            private void AddPath()
            {
                HashSet<Variable> existsVars = new HashSet<Variable>();
                Dictionary<Variable, Expr> varToExpr = new Dictionary<Variable, Expr>();
                foreach (Variable v in frame)
                {
                    varToExpr[v] = Expr.Ident(v);
                }
                if (first != null)
                {
                    foreach (Variable v in first.thatOutParams)
                    {
                        varToExpr[v] = Expr.Ident(v);
                    }
                }
                foreach (Variable v in second.thisOutParams)
                {
                    varToExpr[v] = Expr.Ident(v);
                }
                List<Expr> pathExprs = new List<Expr>();
                int boundVariableCount = 0;
                foreach (Cmd cmd in cmdStack)
                {
                    if (cmd is AssumeCmd)
                    {
                        AssumeCmd assumeCmd = cmd as AssumeCmd;
                        FlattenAnd(assumeCmd.Expr, pathExprs);
                    }
                    else if (cmd is AssignCmd)
                    {
                        AssignCmd assignCmd = (cmd as AssignCmd).AsSimpleAssignCmd;
                        Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                        for (int k = 0; k < assignCmd.Lhss.Count; k++)
                        {
                            map[assignCmd.Lhss[k].DeepAssignedVariable] = assignCmd.Rhss[k];
                        }
                        Substitute(map, ref pathExprs, ref varToExpr);
                    }
                    else if (cmd is HavocCmd)
                    {
                        HavocCmd havocCmd = cmd as HavocCmd;
                        Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                        foreach (IdentifierExpr ie in havocCmd.Vars)
                        {
                            BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "#tmp_" + boundVariableCount++, ie.Decl.TypedIdent.Type));
                            map[ie.Decl] = Expr.Ident(bv);
                            existsVars.Add(bv);
                        }
                        Substitute(map, ref pathExprs, ref varToExpr);
                    }
                    else
                    {
                        Debug.Assert(false);
                    }
                }
                paths.Add(new PathInfo(existsVars, varToExpr, pathExprs));
            }

            private Expr CalculatePathCondition(PathInfo path)
            {
                Expr returnExpr = Expr.True;

                HashSet<Variable> existsVars = path.existsVars;
                Dictionary<Variable, Expr> existsMap = new Dictionary<Variable, Expr>();

                Dictionary<Variable, Expr> varToExpr = path.varToExpr;
                foreach (Variable v in varToExpr.Keys)
                {
                    if (postExistVars.Contains(v)) continue;
                    IdentifierExpr ie = varToExpr[v] as IdentifierExpr;
                    if (ie != null && !existsMap.ContainsKey(ie.Decl) && existsVars.Contains(ie.Decl))
                    {
                        existsMap[ie.Decl] = Expr.Ident(v);
                        existsVars.Remove(ie.Decl);
                    }
                    else
                    {
                        returnExpr = Expr.And(returnExpr, Expr.Eq(Expr.Ident(v), (new MyDuplicator()).VisitExpr(varToExpr[v])));
                        returnExpr.Type = Type.Bool;
                    }
                }

                List<Expr> pathExprs = new List<Expr>();
                path.pathExprs.ForEach(x => pathExprs.Add((new MyDuplicator()).VisitExpr(x)));
                foreach (Expr x in pathExprs)
                {
                    Variable boundVar;
                    Expr boundVarExpr;
                    if (InferSubstitution(x, out boundVar, out boundVarExpr) && existsVars.Contains(boundVar))
                    {
                        existsMap[boundVar] = boundVarExpr;
                        existsVars.Remove(boundVar);
                    }
                    else
                    {
                        returnExpr = Expr.And(returnExpr, x);
                        returnExpr.Type = Type.Bool;
                    }
                }
                
                returnExpr = Substituter.Apply(Substituter.SubstitutionFromHashtable(existsMap), returnExpr);
                if (existsVars.Count > 0)
                {
                    returnExpr = new ExistsExpr(Token.NoToken, new List<Variable>(existsVars), returnExpr);
                }
                return returnExpr;
            }

            bool InferSubstitution(Expr x, out Variable var, out Expr expr)
            {
                var = null;
                expr = null;
                NAryExpr naryExpr = x as NAryExpr;
                if (naryExpr == null || naryExpr.Fun.FunctionName != "==")
                {
                    return false;
                }
                IdentifierExpr arg0 = naryExpr.Args[0] as IdentifierExpr;
                if (arg0 != null && arg0.Decl is BoundVariable)
                {
                    var = arg0.Decl;
                    expr = naryExpr.Args[1];
                    return true;
                }
                IdentifierExpr arg1 = naryExpr.Args[1] as IdentifierExpr;
                if (arg1 != null && arg1.Decl is BoundVariable)
                {
                    var = arg1.Decl;
                    expr = naryExpr.Args[0];
                    return true;
                }
                return false;
            }

            public Expr TransitionRelationCompute(bool withOriginalInOutVariables = false)
            {
                Expr transitionRelation = Expr.False;
                foreach (PathInfo path in paths)
                {
                    transitionRelation = Expr.Or(transitionRelation, CalculatePathCondition(path));
                }
                ResolutionContext rc = new ResolutionContext(null);
                rc.StateMode = ResolutionContext.State.Two;
                transitionRelation.Resolve(rc);
                transitionRelation.Typecheck(new TypecheckingContext(null));

                if (withOriginalInOutVariables)
                {
                    Dictionary<Variable, Expr> invertedMap = new Dictionary<Variable, Expr>();
                    if (first != null)
                    {
                        foreach (var x in first.thatMap)
                        {
                            invertedMap[((IdentifierExpr)x.Value).Decl] = Expr.Ident(x.Key);
                        }
                    }
                    if (second != null)
                    {
                        foreach (var x in second.thisMap)
                        {
                            invertedMap[((IdentifierExpr)x.Value).Decl] = Expr.Ident(x.Key);
                        }
                    }
                    Substitution subst = Substituter.SubstitutionFromHashtable(invertedMap);
                    return Substituter.Apply(subst, transitionRelation);
                }
                else
                {
                    return transitionRelation;
                }

            }

            private void Search(Block b, bool inFirst)
            {
                int pathSizeAtEntry = cmdStack.Count;
                foreach (Cmd cmd in b.Cmds)
                {
                    cmdStack.Push(cmd);
                }
                if (b.TransferCmd is ReturnCmd)
                {
                    if (first == null || inFirst)
                    {
                        AddPath();
                    }
                    else
                    {
                        List<IdentifierExpr> havocVars = new List<IdentifierExpr>();
                        first.thatOutParams.ForEach(v => havocVars.Add(Expr.Ident(v)));
                        first.thatAction.LocVars.ForEach(v => havocVars.Add(Expr.Ident(v)));
                        if (havocVars.Count > 0)
                        {
                            HavocCmd havocCmd = new HavocCmd(Token.NoToken, havocVars);
                            cmdStack.Push(havocCmd);
                        }
                        Search(first.thatAction.Blocks[0], true);
                    }
                }
                else
                {
                    GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
                    foreach (Block target in gotoCmd.labelTargets)
                    {
                        Search(target, inFirst);
                    }
                }
                Debug.Assert(cmdStack.Count >= pathSizeAtEntry);
                while (cmdStack.Count > pathSizeAtEntry)
                {
                    cmdStack.Pop();
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

        private List<Requires> DisjointnessRequires(Program program, AtomicActionInfo first, AtomicActionInfo second, HashSet<Variable> frame)
        {
            List<Requires> requires = new List<Requires>();
            Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                domainNameToScope[domainName] = new HashSet<Variable>();
            }
            foreach (Variable v in frame)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
                if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                domainNameToScope[domainName].Add(v);
            }
            if (first != null)
            {
                foreach (Variable v in first.thatInParams)
                {
                    var domainName = linearTypeChecker.FindDomainName(v);
                    if (domainName == null) continue;
                    if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                    domainNameToScope[domainName].Add(v);
                }
            }
            foreach (Variable v in second.thisInParams)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
                if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                domainNameToScope[domainName].Add(v);
            }
            foreach (string domainName in domainNameToScope.Keys)
            {
                requires.Add(new Requires(false, linearTypeChecker.DisjointnessExpr(domainName, domainNameToScope[domainName])));
            }
            return requires;
        }

        private void CreateCommutativityChecker(Program program, AtomicActionInfo first, AtomicActionInfo second)
        {
            if (first == second && first.thatInParams.Count == 0 && first.thatOutParams.Count == 0)
                return;
            if (first.CommutesWith(second))
                return;
            Tuple<AtomicActionInfo, AtomicActionInfo> actionPair = new Tuple<AtomicActionInfo, AtomicActionInfo>(first, second);
            if (commutativityCheckerCache.Contains(actionPair))
                return;
            commutativityCheckerCache.Add(actionPair);

            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(first.thatInParams);
            inputs.AddRange(second.thisInParams);
            List<Variable> outputs = new List<Variable>();
            outputs.AddRange(first.thatOutParams);
            outputs.AddRange(second.thisOutParams);
            List<Variable> locals = new List<Variable>();
            locals.AddRange(first.thatAction.LocVars);
            locals.AddRange(second.thisAction.LocVars);
            List<Block> firstBlocks = CloneBlocks(first.thatAction.Blocks);
            List<Block> secondBlocks = CloneBlocks(second.thisAction.Blocks);
            foreach (Block b in firstBlocks)
            {
                if (b.TransferCmd is ReturnCmd)
                {
                    List<Block> bs = new List<Block>();
                    bs.Add(secondBlocks[0]);
                    List<string> ls = new List<string>();
                    ls.Add(secondBlocks[0].Label);
                    b.TransferCmd = new GotoCmd(Token.NoToken, ls, bs);
                }
            }
            List<Block> blocks = new List<Block>();
            blocks.AddRange(firstBlocks);
            blocks.AddRange(secondBlocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(first.actionUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);
            List<Requires> requires = DisjointnessRequires(program, first, second, frame);
            foreach (AssertCmd assertCmd in first.thatGate)
                requires.Add(new Requires(false, assertCmd.Expr));
            foreach (AssertCmd assertCmd in second.thisGate)
                requires.Add(new Requires(false, assertCmd.Expr));
            List<Ensures> ensures = new List<Ensures>();
            Expr transitionRelation = (new TransitionRelationComputation(program, first, second, frame, new HashSet<Variable>())).TransitionRelationCompute();
            Ensures ensureCheck = new Ensures(false, transitionRelation);
            ensureCheck.ErrorData = string.Format("Commutativity check between {0} and {1} failed", first.proc.Name, second.proc.Name);
            ensures.Add(ensureCheck);
            string checkerName = string.Format("CommutativityChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            civlTypeChecker.SharedVariables.Iter(x => globalVars.Add(Expr.Ident(x)));
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
            Tuple<AtomicActionInfo, AtomicActionInfo> actionPair = new Tuple<AtomicActionInfo, AtomicActionInfo>(first, second);
            if (gatePreservationCheckerCache.Contains(actionPair))
                return;
            gatePreservationCheckerCache.Add(actionPair);

            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(first.thatInParams);
            inputs.AddRange(second.thisInParams);
            List<Variable> outputs = new List<Variable>();
            outputs.AddRange(first.thatOutParams);
            outputs.AddRange(second.thisOutParams);
            List<Variable> locals = new List<Variable>();
            locals.AddRange(second.thisAction.LocVars);
            List<Block> secondBlocks = CloneBlocks(second.thisAction.Blocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);
            List<Requires> requires = DisjointnessRequires(program, first, second, frame);
            List<Ensures> ensures = new List<Ensures>();
            foreach (AssertCmd assertCmd in first.thatGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
                Ensures ensureCheck = new Ensures(assertCmd.tok, false, assertCmd.Expr, null);
                ensureCheck.ErrorData = string.Format("Gate not preserved by {0}", second.proc.Name);
                ensures.Add(ensureCheck);
            }
            foreach (AssertCmd assertCmd in second.thisGate)
                requires.Add(new Requires(false, assertCmd.Expr));
            string checkerName = string.Format("GatePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            civlTypeChecker.SharedVariables.Iter(x => globalVars.Add(Expr.Ident(x)));
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
            Tuple<AtomicActionInfo, AtomicActionInfo> actionPair = new Tuple<AtomicActionInfo, AtomicActionInfo>(first, second);
            if (failurePreservationCheckerCache.Contains(actionPair))
                return;
            failurePreservationCheckerCache.Add(actionPair);

            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(first.thatInParams);
            inputs.AddRange(second.thisInParams);
            List<Variable> outputs = new List<Variable>();
            outputs.AddRange(first.thatOutParams);
            outputs.AddRange(second.thisOutParams);
            List<Variable> locals = new List<Variable>();
            locals.AddRange(second.thisAction.LocVars);
            List<Block> secondBlocks = CloneBlocks(second.thisAction.Blocks);
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);
            List<Requires> requires = DisjointnessRequires(program, first, second, frame);
            Expr gateExpr = Expr.True;
            foreach (AssertCmd assertCmd in first.thatGate)
            {
                gateExpr = Expr.And(gateExpr, assertCmd.Expr);
                gateExpr.Type = Type.Bool;
            }
            gateExpr = Expr.Not(gateExpr);
            gateExpr.Type = Type.Bool;
            requires.Add(new Requires(false, gateExpr));
            List<Ensures> ensures = new List<Ensures>();
            Ensures ensureCheck = new Ensures(false, gateExpr);
            ensureCheck.ErrorData = string.Format("Gate failure of {0} not preserved by {1}", first.proc.Name, second.proc.Name);
            ensures.Add(ensureCheck);
            foreach (AssertCmd assertCmd in second.thisGate)
                requires.Add(new Requires(false, assertCmd.Expr));
            string checkerName = string.Format("FailurePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            civlTypeChecker.SharedVariables.Iter(x => globalVars.Add(Expr.Ident(x)));
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
            List<Requires> requires = DisjointnessRequires(program, null, second, frame);
            foreach (AssertCmd assertCmd in second.thisGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }
            HashSet<Variable> postExistVars = new HashSet<Variable>();
            postExistVars.UnionWith(frame);
            postExistVars.UnionWith(second.thisOutParams);
            Expr ensuresExpr = (new TransitionRelationComputation(program, second, frame, postExistVars)).TransitionRelationCompute();
            List<Ensures> ensures = new List<Ensures>();
            Ensures ensureCheck = new Ensures(false, ensuresExpr);
            ensureCheck.ErrorData = string.Format("{0} is blocking", second.proc.Name);
            ensures.Add(ensureCheck);

            List<Block> blocks = new List<Block>();
            blocks.Add(new Block(Token.NoToken, "L", new List<Cmd>(), new ReturnCmd(Token.NoToken)));
            string checkerName = string.Format("NonBlockingChecker_{0}", second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            civlTypeChecker.SharedVariables.Iter(x => globalVars.Add(Expr.Ident(x)));
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), new List<Variable>(), blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }
    }
}