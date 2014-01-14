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
        private sealed class MySubstituter : Duplicator
        {
            private readonly Substitution outsideOld;
            private readonly Substitution insideOld;
            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(insideOld != null);
            }

            public MySubstituter(Substitution outsideOld, Substitution insideOld)
                : base()
            {
                Contract.Requires(outsideOld != null && insideOld != null);
                this.outsideOld = outsideOld;
                this.insideOld = insideOld;
            }

            private bool insideOldExpr = false;

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                Contract.Ensures(Contract.Result<Expr>() != null);
                Expr e = null;

                if (insideOldExpr)
                {
                    e = insideOld(node.Decl);
                }
                else
                {
                    e = outsideOld(node.Decl);
                }
                return e == null ? base.VisitIdentifierExpr(node) : e;
            }

            public override Expr VisitOldExpr(OldExpr node)
            {
                Contract.Ensures(Contract.Result<Expr>() != null);
                bool previouslyInOld = insideOldExpr;
                insideOldExpr = true;
                Expr tmp = (Expr)this.Visit(node.Expr);
                OldExpr e = new OldExpr(node.tok, tmp);
                insideOldExpr = previouslyInOld;
                return e;
            }
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
        }

        public class TransitionRelationComputation
        {
            private Program program;
            private ActionInfo first;  // corresponds to that*
            private ActionInfo second; // corresponds to this*
            private Stack<Cmd> path;
            private Expr transitionRelation;

            public TransitionRelationComputation(Program program, ActionInfo second)
            {
                this.program = program;
                this.first = null;
                this.second = second;
                this.path = new Stack<Cmd>();
                this.transitionRelation = Expr.False;
            }

            public TransitionRelationComputation(Program program, ActionInfo first, ActionInfo second)
            {
                this.program = program;
                this.first = first;
                this.second = second;
                this.path = new Stack<Cmd>();
                this.transitionRelation = Expr.False;
            }

            public Expr Compute()
            {
                List<IdentifierExpr> havocVars = new List<IdentifierExpr>();
                second.thisOutParams.ForEach(v => havocVars.Add(Expr.Ident(v)));
                second.thisAction.LocVars.ForEach(v => havocVars.Add(Expr.Ident(v)));
                if (havocVars.Count > 0)
                {
                    HavocCmd havocCmd = new HavocCmd(Token.NoToken, havocVars);
                    path.Push(havocCmd);
                }
                Search(second.thisAction.Blocks[0], false);
                return transitionRelation;
            }

            private void Substitute(Dictionary<Variable, Expr> map, ref Expr returnExpr, ref Dictionary<Variable, Expr> varToExpr)
            {
                Substitution subst = Substituter.SubstitutionFromHashtable(map);
                returnExpr = Substituter.Apply(subst, returnExpr);
                Dictionary<Variable, Expr> oldVarToExpr = varToExpr;
                varToExpr = new Dictionary<Variable, Expr>();
                foreach (Variable v in oldVarToExpr.Keys)
                {
                    varToExpr[v] = Substituter.Apply(subst, oldVarToExpr[v]);
                }
            }

            private Expr CalculatePathCondition()
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
                Expr returnExpr = Expr.True;
                int boundVariableCount = 0;
                foreach (Cmd cmd in path)
                {
                    if (cmd is AssumeCmd)
                    {
                        AssumeCmd assumeCmd = cmd as AssumeCmd;
                        returnExpr = Expr.And(new OldExpr(Token.NoToken, assumeCmd.Expr), returnExpr);
                    }
                    else if (cmd is AssignCmd)
                    {
                        AssignCmd assignCmd = (cmd as AssignCmd).AsSimpleAssignCmd;
                        Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                        for (int k = 0; k < assignCmd.Lhss.Count; k++)
                        {
                            map[assignCmd.Lhss[k].DeepAssignedVariable] = assignCmd.Rhss[k];
                        }
                        Substitute(map, ref returnExpr, ref varToExpr);
                    }
                    else if (cmd is HavocCmd)
                    {
                        HavocCmd havocCmd = cmd as HavocCmd;
                        Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                        foreach (IdentifierExpr ie in havocCmd.Vars)
                        {
                            BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "#tmp_" + boundVariableCount++, ie.Decl.TypedIdent.Type));
                            map[ie.Decl] = new IdentifierExpr(Token.NoToken, bv);
                            existsVars.Add(bv);
                        }
                        Substitute(map, ref returnExpr, ref varToExpr);
                    }
                    else
                    {
                        Debug.Assert(false);
                    }
                }
                Dictionary<Variable, Expr> existsMap = new Dictionary<Variable, Expr>();
                foreach (Variable v in varToExpr.Keys)
                {
                    IdentifierExpr ie = varToExpr[v] as IdentifierExpr;
                    if (ie != null && !existsMap.ContainsKey(ie.Decl) && existsVars.Contains(ie.Decl))
                    {
                        existsMap[ie.Decl] = Expr.Ident(v);
                        existsVars.Remove(ie.Decl);
                    }
                }
                Substitute(existsMap, ref returnExpr, ref varToExpr);
                returnExpr = new OldExpr(Token.NoToken, returnExpr);
                foreach (Variable v in varToExpr.Keys)
                {
                    returnExpr = Expr.And(returnExpr, Expr.Eq(Expr.Ident(v), varToExpr[v]));
                }
                if (existsVars.Count > 0)
                {
                    returnExpr = new ExistsExpr(Token.NoToken, new List<Variable>(existsVars), returnExpr);
                }
                return returnExpr;
            }

            private void Search(Block b, bool inFirst)
            {
                foreach (Cmd cmd in b.Cmds)
                {
                    path.Push(cmd);
                }
                if (b.TransferCmd is ReturnCmd)
                {
                    if (first == null || inFirst)
                    {
                        transitionRelation = Expr.Or(transitionRelation, CalculatePathCondition());
                    }
                    else
                    {
                        List<IdentifierExpr> havocVars = new List<IdentifierExpr>();
                        first.thatOutParams.ForEach(v => havocVars.Add(Expr.Ident(v)));
                        first.thatAction.LocVars.ForEach(v => havocVars.Add(Expr.Ident(v)));
                        if (havocVars.Count > 0)
                        {
                            HavocCmd havocCmd = new HavocCmd(Token.NoToken, havocVars);
                            path.Push(havocCmd);
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
                foreach (Cmd cmd in b.Cmds)
                {
                    path.Pop();
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
                domainNameToScope[domainName].Add(v);
            }
            foreach (Variable v in first.thatInParams)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
                domainNameToScope[domainName].Add(v);
            }
            foreach (Variable v in second.thisInParams)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
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
            Expr transitionRelation = (new TransitionRelationComputation(program, first, second)).Compute();
            Ensures ensureCheck = new Ensures(false, transitionRelation);
            ensureCheck.ErrorData = string.Format("Commutativity check between {0} and {1} failed", first.proc.Name, second.proc.Name);
            ensures.Add(ensureCheck);
            string checkerName = string.Format("CommutativityChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            program.GlobalVariables().Iter(x => globalVars.Add(new IdentifierExpr(Token.NoToken, x)));
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
            program.GlobalVariables().Iter(x => globalVars.Add(new IdentifierExpr(Token.NoToken, x)));
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, secondBlocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateFailurePreservationChecker(Program program, ActionInfo first, ActionInfo second)
        {
            Debug.Assert(second.isNonBlocking);
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0)
                return;
            Tuple<ActionInfo, ActionInfo> actionPair = new Tuple<ActionInfo, ActionInfo>(first, second);
            if (failurePreservationCheckerCache.Contains(actionPair))
                return;
            failurePreservationCheckerCache.Add(actionPair);

            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(first.thatInParams);
            inputs.AddRange(second.thisInParams);

            Expr failureExpr = Expr.True;
            foreach (AssertCmd assertCmd in first.thatGate)
            {
                failureExpr = Expr.And(assertCmd.Expr, failureExpr);
            }
            failureExpr = Expr.Not(failureExpr);

            List<Requires> requires = DisjointnessRequires(program, first, second);
            requires.Add(new Requires(false, failureExpr));

            List<Ensures> ensures = new List<Ensures>();
            Ensures ensureCheck = new Ensures(false, failureExpr);
            ensureCheck.ErrorData = string.Format("Gate failure of {0} not preserved by {1}", first.proc.Name, second.proc.Name);
            ensures.Add(ensureCheck);

            List<Variable> outputs = new List<Variable>();
            outputs.AddRange(first.thatOutParams);
            outputs.AddRange(second.thisOutParams);
            List<Variable> locals = new List<Variable>();
            locals.AddRange(second.thisAction.LocVars);
            List<Block> secondBlocks = CloneBlocks(second.thisAction.Blocks);
            string checkerName = string.Format("FailurePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            program.GlobalVariables().Iter(x => globalVars.Add(new IdentifierExpr(Token.NoToken, x)));
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, secondBlocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateFailurePreservationCheckerExists(Program program, ActionInfo first, ActionInfo second)
        {
            if (first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Count() == 0 && second.isNonBlocking)
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
            requiresExpr = Expr.Not(requiresExpr);
            List<Requires> requires = DisjointnessRequires(program, first, second);
            requires.Add(new Requires(false, requiresExpr));
            foreach (AssertCmd assertCmd in second.thisGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }

            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> oldMap = new Dictionary<Variable, Expr>();
            List<Variable> boundVars = new List<Variable>();
            foreach (Variable v in program.GlobalVariables())
            {
                if (second.modifiedGlobalVars.Contains(v))
                {
                    BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "post_" + v.Name, v.TypedIdent.Type));
                    boundVars.Add(bv);
                    map[v] = new IdentifierExpr(Token.NoToken, bv);
                }
                else
                {
                    map[v] = new OldExpr(Token.NoToken, Expr.Ident(v));
                }
                oldMap[v] = Expr.Ident(v);
            }
            foreach (Variable v in second.thisOutParams)
            {
                BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "post_" + v.Name, v.TypedIdent.Type));
                boundVars.Add(bv);
                map[v] = new IdentifierExpr(Token.NoToken, bv);
            }

            Expr ensuresExpr = Expr.And((new TransitionRelationComputation(program, second)).Compute(), requiresExpr);
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            Substitution oldSubst = Substituter.SubstitutionFromHashtable(oldMap);
            ensuresExpr = Substituter.Apply(subst, oldSubst, ensuresExpr);
            if (boundVars.Count > 0)
            {
                ensuresExpr = new ExistsExpr(Token.NoToken, boundVars, ensuresExpr);
            }
            List<Ensures> ensures = new List<Ensures>();
            Ensures ensureCheck = new Ensures(false, ensuresExpr);
            ensureCheck.ErrorData = string.Format("Gate failure of {0} not preserved by {1}", first.proc.Name, second.proc.Name);
            ensures.Add(ensureCheck);

            List<Block> blocks = new List<Block>();
            blocks.Add(new Block(Token.NoToken, "L", new List<Cmd>(), new ReturnCmd(Token.NoToken)));
            string checkerName = string.Format("FailurePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<IdentifierExpr> globalVars = new List<IdentifierExpr>();
            program.GlobalVariables().Iter(x => globalVars.Add(new IdentifierExpr(Token.NoToken, x)));
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), requires, globalVars, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, new List<Variable>(), new List<Variable>(), blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }
    }
}