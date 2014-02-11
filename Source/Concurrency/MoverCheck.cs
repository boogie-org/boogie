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
        public static MoverType GetMoverType(Ensures e, out int phaseNum)
        {
            phaseNum = QKeyValue.FindIntAttribute(e.Attributes, "atomic", int.MaxValue);
            if (phaseNum != int.MaxValue)
                return MoverType.Atomic;
            phaseNum = QKeyValue.FindIntAttribute(e.Attributes, "right", int.MaxValue);
            if (phaseNum != int.MaxValue)
                return MoverType.Right;
            phaseNum = QKeyValue.FindIntAttribute(e.Attributes, "left", int.MaxValue);
            if (phaseNum != int.MaxValue)
                return MoverType.Left;
            phaseNum = QKeyValue.FindIntAttribute(e.Attributes, "both", int.MaxValue);
            if (phaseNum != int.MaxValue)
                return MoverType.Both;
            return MoverType.Top;
        }

        LinearTypeChecker linearTypeChecker;
        MoverTypeChecker moverTypeChecker;
        List<Declaration> decls;
        HashSet<Tuple<ActionInfo, ActionInfo>> commutativityCheckerCache;
        HashSet<Tuple<ActionInfo, ActionInfo>> gatePreservationCheckerCache;
        HashSet<Tuple<ActionInfo, ActionInfo>> failurePreservationCheckerCache;
        private MoverCheck(LinearTypeChecker linearTypeChecker, MoverTypeChecker moverTypeChecker, List<Declaration> decls)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.moverTypeChecker = moverTypeChecker;
            this.decls = decls;
            this.commutativityCheckerCache = new HashSet<Tuple<ActionInfo, ActionInfo>>();
            this.gatePreservationCheckerCache = new HashSet<Tuple<ActionInfo, ActionInfo>>();
            this.failurePreservationCheckerCache = new HashSet<Tuple<ActionInfo, ActionInfo>>();
        }

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, MoverTypeChecker moverTypeChecker, List<Declaration> decls)
        {
            if (moverTypeChecker.procToActionInfo.Count == 0)
                return;

            Dictionary<int, HashSet<ActionInfo>> pools = new Dictionary<int, HashSet<ActionInfo>>();
            foreach (ActionInfo action in moverTypeChecker.procToActionInfo.Values)
            {
                foreach (int phaseNum in action.callerPhaseNums)
                {
                    if (!pools.ContainsKey(phaseNum))
                    {
                        pools[phaseNum] = new HashSet<ActionInfo>();
                    }
                    pools[phaseNum].Add(action);
                }
            }

            Program program = moverTypeChecker.program;
            MoverCheck moverChecking = new MoverCheck(linearTypeChecker, moverTypeChecker, decls);
            foreach (int phaseNum1 in pools.Keys)
            {
                foreach (ActionInfo first in pools[phaseNum1])
                {
                    Debug.Assert(first.moverType != MoverType.Top);
                    if (first.moverType == MoverType.Atomic)
                        continue;
                    foreach (int phaseNum2 in pools.Keys)
                    {
                        if (phaseNum2 < phaseNum1) continue;
                        foreach (ActionInfo second in pools[phaseNum2])
                        {
                            if (second.phaseNum < phaseNum1)
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
                }
            }
            foreach (ActionInfo action in moverTypeChecker.procToActionInfo.Values)
            {
                if (action.IsLeftMover && action.hasAssumeCmd)
                {
                    moverChecking.CreateNonBlockingChecker(program, action);
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
                    return ret;
            }
        }

        public class TransitionRelationComputation
        {
            private Program program;
            private ActionInfo first;  // corresponds to that*
            private ActionInfo second; // corresponds to this*
            private Stack<Cmd> cmdStack;
            private List<PathInfo> paths;

            public TransitionRelationComputation(Program program, ActionInfo second) : this(program, null, second)
            {
            }

            public TransitionRelationComputation(Program program, ActionInfo first, ActionInfo second)
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
                foreach (Variable v in program.GlobalVariables())
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
                    IdentifierExpr ie = varToExpr[v] as IdentifierExpr;
                    if (ie != null && !existsMap.ContainsKey(ie.Decl) && existsVars.Contains(ie.Decl))
                    {
                        existsMap[ie.Decl] = Expr.Ident(v);
                        existsVars.Remove(ie.Decl);
                    }
                    else
                    {
                        returnExpr = Expr.And(returnExpr, Expr.Eq(Expr.Ident(v), (new MyDuplicator()).VisitExpr(varToExpr[v])));
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

            public Expr LeftMoverCompute(Expr failureExpr)
            {
                Expr returnExpr = Expr.False;
                foreach (PathInfo path in paths)
                {
                    Expr expr = Substituter.Apply(Substituter.SubstitutionFromHashtable(path.varToExpr), failureExpr);
                    Dictionary<Variable, Expr> subst = new Dictionary<Variable, Expr>();
                    foreach (Expr x in path.pathExprs)
                    {
                        Variable boundVar;
                        Expr boundVarExpr;
                        if (InferSubstitution(x, out boundVar, out boundVarExpr) && path.existsVars.Contains(boundVar))
                        {
                            subst[boundVar] = boundVarExpr;
                            path.existsVars.Remove(boundVar);
                        }
                        else
                        {
                            expr = Expr.And(expr, x);
                        }
                    }
                    expr = Substituter.Apply(Substituter.SubstitutionFromHashtable(subst), expr);
                    expr = new OldExpr(Token.NoToken, expr);
                    if (path.existsVars.Count > 0)
                    {
                        expr = new ExistsExpr(Token.NoToken, new List<Variable>(path.existsVars), expr);
                    }
                    returnExpr = Expr.Or(returnExpr, expr);
                }
                return returnExpr;
            }

            public Expr TransitionRelationCompute()
            {
                Expr transitionRelation = Expr.False;
                foreach (PathInfo path in paths)
                {
                    transitionRelation = Expr.Or(transitionRelation, CalculatePathCondition(path));
                }
                return transitionRelation;
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

        private List<Requires> DisjointnessRequires(Program program, ActionInfo first, ActionInfo second)
        {
            List<Requires> requires = new List<Requires>();
            Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                domainNameToScope[domainName] = new HashSet<Variable>();
            }
            foreach (Variable v in program.GlobalVariables())
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

        private void CreateCommutativityChecker(Program program, ActionInfo first, ActionInfo second)
        {
            if (first == second && first.thatInParams.Count == 0 && first.thatOutParams.Count == 0)
                return;
            if (first.CommutesWith(second))
                return;
            Tuple<ActionInfo, ActionInfo> actionPair = new Tuple<ActionInfo, ActionInfo>(first, second);
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
            List<Requires> requires = DisjointnessRequires(program, first, second);
            List<Ensures> ensures = new List<Ensures>();
            Expr transitionRelation = (new TransitionRelationComputation(program, first, second)).TransitionRelationCompute();
            Ensures ensureCheck = new Ensures(false, transitionRelation);
            ensureCheck.ErrorData = string.Format("Commutativity check between {0} and {1} failed", first.proc.Name, second.proc.Name);
            ensures.Add(ensureCheck);
            string checkerName = string.Format("CommutativityChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            program.GlobalVariables().Iter(x => globalVars.Add(Expr.Ident(x)));
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateGatePreservationChecker(Program program, ActionInfo first, ActionInfo second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;
            Tuple<ActionInfo, ActionInfo> actionPair = new Tuple<ActionInfo, ActionInfo>(first, second);
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
            List<Requires> requires = DisjointnessRequires(program, first, second);
            List<Ensures> ensures = new List<Ensures>();
            foreach (AssertCmd assertCmd in first.thatGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
                Ensures ensureCheck = new Ensures(assertCmd.tok, false, assertCmd.Expr, null);
                ensureCheck.ErrorData = string.Format("Gate not preserved by {0}", second.proc.Name);
                ensures.Add(ensureCheck);
            }
            string checkerName = string.Format("GatePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            program.GlobalVariables().Iter(x => globalVars.Add(Expr.Ident(x)));
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, secondBlocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateFailurePreservationChecker(Program program, ActionInfo first, ActionInfo second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;

            Tuple<ActionInfo, ActionInfo> actionPair = new Tuple<ActionInfo, ActionInfo>(first, second); 
            if (failurePreservationCheckerCache.Contains(actionPair))
                return;
            failurePreservationCheckerCache.Add(actionPair);

            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(first.thatInParams);
            inputs.AddRange(second.thisInParams);

            Expr requiresExpr = Expr.True;
            foreach (AssertCmd assertCmd in first.thatGate)
            {
                requiresExpr = Expr.And(assertCmd.Expr, requiresExpr);
            }
            Expr failureExpr = Expr.Not(requiresExpr);
            List<Requires> requires = DisjointnessRequires(program, first, second);
            requires.Add(new Requires(false, failureExpr));
            foreach (AssertCmd assertCmd in second.thisGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }

            Expr ensuresExpr = (new TransitionRelationComputation(program, second)).LeftMoverCompute(failureExpr);
            List<Ensures> ensures = new List<Ensures>();
            Ensures ensureCheck = new Ensures(false, ensuresExpr);
            ensureCheck.ErrorData = string.Format("Gate failure of {0} not preserved by {1}", first.proc.Name, second.proc.Name);
            ensures.Add(ensureCheck);

            List<Block> blocks = new List<Block>();
            blocks.Add(new Block(Token.NoToken, "L", new List<Cmd>(), new ReturnCmd(Token.NoToken)));
            string checkerName = string.Format("FailurePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            program.GlobalVariables().Iter(x => globalVars.Add(Expr.Ident(x)));
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), new List<Variable>(), blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateNonBlockingChecker(Program program, ActionInfo second)
        {
            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(second.thisInParams);

            Expr failureExpr = Expr.True;
            List<Requires> requires = DisjointnessRequires(program, null, second);
            requires.Add(new Requires(false, failureExpr));
            foreach (AssertCmd assertCmd in second.thisGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }

            Expr ensuresExpr = (new TransitionRelationComputation(program, second)).LeftMoverCompute(failureExpr);
            List<Ensures> ensures = new List<Ensures>();
            Ensures ensureCheck = new Ensures(false, ensuresExpr);
            ensureCheck.ErrorData = string.Format("{0} is blocking", second.proc.Name);
            ensures.Add(ensureCheck);

            List<Block> blocks = new List<Block>();
            blocks.Add(new Block(Token.NoToken, "L", new List<Cmd>(), new ReturnCmd(Token.NoToken)));
            string checkerName = string.Format("NonBlockingChecker_{0}", second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            program.GlobalVariables().Iter(x => globalVars.Add(Expr.Ident(x)));
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), new List<Variable>(), blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }
    }
}