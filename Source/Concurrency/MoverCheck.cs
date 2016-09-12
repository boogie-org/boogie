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

            private Dictionary<Variable, Variable> existsVars;
            private HashSet<Variable> firstExistsVars;
            private HashSet<Variable> secondExistsVars;

            private bool IsExistsVar(Variable v)
            {
                if (firstExistsVars.Contains(v))
                {
                    return true;
                }
                else if (secondExistsVars.Contains(v))
                {
                    return true;
                }
                else
                {
                    return false;
                }
            }

            private void PopulateExistsVars(Variable v)
            {
                if (existsVars.ContainsKey(v)) return;
                existsVars[v] = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "#tmp_" + existsVars.Count, v.TypedIdent.Type));
            }

            private Function TriggerFunction(Variable v)
            {
                PopulateExistsVars(v);
                if (firstExistsVars.Contains(v))
                {
                    return first.TriggerFunction(v);
                }
                else if (secondExistsVars.Contains(v))
                {
                    return second.TriggerFunction(v);
                }
                else
                {
                    Debug.Assert(false);
                    return null;
                }
            }

            public List<Cmd> TriggerAssumes()
            {
                List<Cmd> list = new List<Cmd>();
                foreach (var v in existsVars.Keys)
                {
                    var triggerFun = TriggerFunction(v);
                    Expr expr = new NAryExpr(Token.NoToken, new FunctionCall(triggerFun), new Expr[] { Expr.Ident(v) });
                    list.Add(new AssumeCmd(Token.NoToken, expr));
                }
                return list;
            }

            public TransitionRelationComputation(Program program, AtomicActionInfo second, HashSet<Variable> frame, HashSet<Variable> postExistVars)
            {
                this.postExistVars = postExistVars;
                this.frame = frame;
                this.existsVars = new Dictionary<Variable, Variable>();
                this.firstExistsVars = new HashSet<Variable>();
                this.secondExistsVars = new HashSet<Variable>();
                TransitionRelationComputationHelper(program, null, second);
            }

            public TransitionRelationComputation(Program program, AtomicActionInfo first, AtomicActionInfo second, HashSet<Variable> frame, HashSet<Variable> postExistVars)
            {
                this.postExistVars = postExistVars;
                this.frame = frame;
                this.existsVars = new Dictionary<Variable, Variable>();
                this.firstExistsVars = new HashSet<Variable>();
                this.secondExistsVars = new HashSet<Variable>();
                TransitionRelationComputationHelper(program, first, second);
            }

            private void TransitionRelationComputationHelper(Program program, AtomicActionInfo first, AtomicActionInfo second)
            {
                this.program = program;
                this.first = first;
                this.second = second;
                this.cmdStack = new Stack<Cmd>();
                this.paths = new List<PathInfo>();
                foreach (Variable v in second.thisOutParams.Union(second.thisAction.LocVars))
                {
                    secondExistsVars.Add(v);
                }
                if (first != null)
                {
                    foreach (Variable v in first.thatOutParams.Union(first.thatAction.LocVars))
                    {
                        firstExistsVars.Add(v);
                    }
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
                public Dictionary<Variable, Expr> varToExpr;
                public List<Expr> pathExprs;

                public PathInfo(Dictionary<Variable, Expr> varToExpr, List<Expr> pathExprs)
                {
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
                Dictionary<Variable, Variable> existsVars = new Dictionary<Variable, Variable>();
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
                    else
                    {
                        Debug.Assert(false);
                    }
                }
                paths.Add(new PathInfo(varToExpr, pathExprs));
            }

            private Expr CalculatePathCondition(PathInfo path)
            {
                HashSet<Variable> allExistsVars = new HashSet<Variable>(firstExistsVars.Union(secondExistsVars));
                HashSet<Variable> usedExistsVars = new HashSet<Variable>();
                Dictionary<Variable, Expr> existsSubstitutionMap = new Dictionary<Variable, Expr>();
                foreach (Variable v in path.varToExpr.Keys)
                {
                    if (postExistVars.Contains(v)) continue;
                    VariableCollector collector = new VariableCollector();
                    collector.Visit(path.varToExpr[v]);
                    usedExistsVars.UnionWith(collector.usedVars.Intersect(allExistsVars));
                    IdentifierExpr ie = path.varToExpr[v] as IdentifierExpr;
                    if (ie != null && IsExistsVar(ie.Decl) && !existsSubstitutionMap.ContainsKey(ie.Decl))
                    {
                        existsSubstitutionMap[ie.Decl] = Expr.Ident(v);
                    }
                }
                foreach (Expr x in path.pathExprs)
                {
                    VariableCollector collector = new VariableCollector();
                    collector.Visit(x);
                    usedExistsVars.UnionWith(collector.usedVars.Intersect(allExistsVars));
                    InferSubstitution(x, existsSubstitutionMap);
                }
                List<Expr> triggerExprs = new List<Expr>();
                List<Variable> quantifiedVars = new List<Variable>();
                foreach (var v in usedExistsVars)
                {
                    if (!existsSubstitutionMap.ContainsKey(v))
                    {
                        var triggerFun = TriggerFunction(v); // this call populates existsVars[v]
                        var quantifiedVar = existsVars[v];
                        triggerExprs.Add(new NAryExpr(Token.NoToken, new FunctionCall(triggerFun), new Expr[] { Expr.Ident(quantifiedVar) }));
                        quantifiedVars.Add(quantifiedVar);
                        existsSubstitutionMap[v] = Expr.Ident(quantifiedVar);
                    }
                }

                Substitution subst = Substituter.SubstitutionFromHashtable(existsSubstitutionMap);
                List<Expr> returnExprs = new List<Expr>();

                foreach (Variable v in path.varToExpr.Keys)
                {
                    if (postExistVars.Contains(v)) continue;
                    Expr withOldExpr = new MyDuplicator().VisitExpr(path.varToExpr[v]);
                    var substExpr = Expr.Eq(Expr.Ident(v), Substituter.Apply(subst, withOldExpr));
                    substExpr.Type = Type.Bool;
                    returnExprs.Add(substExpr);
                }

                foreach (Expr x in path.pathExprs)
                {
                    var withOldExpr = new MyDuplicator().VisitExpr(x);
                    returnExprs.Add(Substituter.Apply(subst, withOldExpr));
                }

                var returnExpr = Expr.And(returnExprs);
                if (quantifiedVars.Count > 0)
                {
                    if (first == null)
                    {
                        returnExpr = new ExistsExpr(Token.NoToken, quantifiedVars, returnExpr);
                    }
                    else
                    {
                        returnExpr = new ExistsExpr(Token.NoToken, quantifiedVars, new Trigger(Token.NoToken, true, triggerExprs), returnExpr);
                    }
                    
                }
                return returnExpr;
            }

            void InferSubstitution(Expr x, Dictionary<Variable, Expr> existsSubstitutionMap)
            {
                NAryExpr naryExpr = x as NAryExpr;
                if (naryExpr == null || naryExpr.Fun.FunctionName != "==")
                {
                    return;
                }
                IdentifierExpr arg0 = naryExpr.Args[0] as IdentifierExpr;
                if (arg0 != null && IsExistsVar(arg0.Decl) && !existsSubstitutionMap.ContainsKey(arg0.Decl))
                {
                    existsSubstitutionMap[arg0.Decl] = naryExpr.Args[1];
                    return;
                }
                IdentifierExpr arg1 = naryExpr.Args[1] as IdentifierExpr;
                if (arg1 != null && IsExistsVar(arg1.Decl) && !existsSubstitutionMap.ContainsKey(arg1.Decl))
                {
                    existsSubstitutionMap[arg1.Decl] = naryExpr.Args[0];
                }
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