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
            foreach (int phaseNum in pools.Keys)
            {
                foreach (ActionInfo first in pools[phaseNum])
                {
                    Debug.Assert(first.moverType != MoverType.Top);
                    if (first.moverType == MoverType.Atomic)
                        continue;
                    foreach (ActionInfo second in pools[phaseNum])
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

        class TransitionRelationComputation
        {
            private Program program;
            private ActionInfo first;
            private ActionInfo second;
            private Stack<Block> dfsStack;
            private Expr transitionRelation;
            private int boundVariableCount;

            public TransitionRelationComputation(Program program, ActionInfo second)
            {
                this.program = program;
                this.first = null;
                this.second = second;
                this.dfsStack = new Stack<Block>();
                this.transitionRelation = Expr.False;
                this.boundVariableCount = 0;
            }

            public TransitionRelationComputation(Program program, ActionInfo first, ActionInfo second)
            {
                this.program = program;
                this.first = first;
                this.second = second;
                this.dfsStack = new Stack<Block>();
                this.transitionRelation = Expr.False;
                this.boundVariableCount = 0;
            }

            private BoundVariable GetBoundVariable(Type type)
            {
                return new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "#tmp_" + boundVariableCount++, type));
            }

            public Expr Compute()
            {
                Search(second.thatAction.Blocks[0], false);
                Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                List<Variable> boundVars = new List<Variable>();
                if (first != null)
                {
                    foreach (Variable v in first.thisAction.LocVars)
                    {
                        BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type));
                        map[v] = new IdentifierExpr(Token.NoToken, bv);
                        boundVars.Add(bv);
                    }
                }
                foreach (Variable v in second.thatAction.LocVars)
                {
                    BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type));
                    map[v] = new IdentifierExpr(Token.NoToken, bv);
                    boundVars.Add(bv);
                }
                Substitution subst = Substituter.SubstitutionFromHashtable(map);
                if (boundVars.Count > 0)
                    return new ExistsExpr(Token.NoToken, boundVars, Substituter.Apply(subst, transitionRelation));
                else
                    return transitionRelation;
            }

            private Expr CalculatePathCondition()
            {
                Expr returnExpr = Expr.True;
                foreach (Variable v in program.GlobalVariables())
                {
                    var eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, v), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                    returnExpr = Expr.And(eqExpr, returnExpr);
                }
                if (first != null)
                {
                    foreach (Variable v in first.thisOutParams)
                    {
                        var eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, v), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                        returnExpr = Expr.And(eqExpr, returnExpr);
                    }
                }
                foreach (Variable v in second.thatOutParams)
                {
                    var eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, v), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                    returnExpr = Expr.And(eqExpr, returnExpr);
                }
                Block[] dfsStackAsArray = dfsStack.Reverse().ToArray();
                for (int i = dfsStackAsArray.Length - 1; i >= 0; i--)
                {
                    Block b = dfsStackAsArray[i];
                    for (int j = b.Cmds.Count - 1; j >= 0; j--)
                    {
                        Cmd cmd = b.Cmds[j];
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
                            Substitution subst = Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>());
                            Substitution oldSubst = Substituter.SubstitutionFromHashtable(map);
                            returnExpr = (Expr) new MySubstituter(subst, oldSubst).Visit(returnExpr);
                        }
                        else if (cmd is HavocCmd)
                        {
                            HavocCmd havocCmd = cmd as HavocCmd;
                            List<Variable> existVars = new List<Variable>();
                            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                            foreach (IdentifierExpr ie in havocCmd.Vars)
                            {
                                BoundVariable bv = GetBoundVariable(ie.Decl.TypedIdent.Type);
                                map[ie.Decl] = new IdentifierExpr(Token.NoToken, bv);
                                existVars.Add(bv);
                            }
                            Substitution subst = Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>());
                            Substitution oldSubst = Substituter.SubstitutionFromHashtable(map);
                            returnExpr = new ExistsExpr(Token.NoToken, existVars, (Expr) new MySubstituter(subst, oldSubst).Visit(returnExpr));
                        }
                        else
                        {
                            Debug.Assert(false);
                        }
                    }
                }
                return returnExpr;
            }

            private void Search(Block b, bool inFirst)
            {
                dfsStack.Push(b);
                if (b.TransferCmd is ReturnCmd)
                {
                    if (first == null || inFirst)
                    {
                        transitionRelation = Expr.Or(transitionRelation, CalculatePathCondition());
                    }
                    else
                    {
                        Search(first.thisAction.Blocks[0], true);
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
                dfsStack.Pop();
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
            foreach (Variable v in first.thisInParams)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
                domainNameToScope[domainName].Add(v);
            }
            for (int i = 0; i < second.thatInParams.Count; i++)
            {
                var domainName = linearTypeChecker.FindDomainName(second.thisInParams[i]);
                if (domainName == null) continue;
                domainNameToScope[domainName].Add(second.thatInParams[i]);
            }
            foreach (string domainName in domainNameToScope.Keys)
            {
                requires.Add(new Requires(false, linearTypeChecker.DisjointnessExpr(domainName, domainNameToScope[domainName])));
            }
            return requires;
        }

        private void CreateCommutativityChecker(Program program, ActionInfo first, ActionInfo second)
        {
            Tuple<ActionInfo, ActionInfo> actionPair = new Tuple<ActionInfo, ActionInfo>(first, second);
            if (commutativityCheckerCache.Contains(actionPair))
                return;
            commutativityCheckerCache.Add(actionPair);

            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(first.thisInParams);
            inputs.AddRange(second.thatInParams);
            List<Variable> outputs = new List<Variable>();
            outputs.AddRange(first.thisOutParams);
            outputs.AddRange(second.thatOutParams);
            List<Variable> locals = new List<Variable>();
            locals.AddRange(first.thisAction.LocVars);
            locals.AddRange(second.thatAction.LocVars);
            List<Block> firstBlocks = CloneBlocks(first.thisAction.Blocks);
            List<Block> secondBlocks = CloneBlocks(second.thatAction.Blocks);
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
            ensures.Add(new Ensures(false, transitionRelation));
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
            Tuple<ActionInfo, ActionInfo> actionPair = new Tuple<ActionInfo, ActionInfo>(first, second);
            if (gatePreservationCheckerCache.Contains(actionPair))
                return;
            gatePreservationCheckerCache.Add(actionPair);

            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(first.thisInParams);
            inputs.AddRange(second.thatInParams);
            List<Variable> outputs = new List<Variable>();
            outputs.AddRange(first.thisOutParams);
            outputs.AddRange(second.thatOutParams);
            List<Variable> locals = new List<Variable>();
            locals.AddRange(second.thatAction.LocVars);
            List<Block> secondBlocks = CloneBlocks(second.thatAction.Blocks);
            List<Requires> requires = DisjointnessRequires(program, first, second);
            List<Ensures> ensures = new List<Ensures>();
            foreach (AssertCmd assertCmd in first.thisGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
                ensures.Add(new Ensures(false, assertCmd.Expr));
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
            Tuple<ActionInfo, ActionInfo> actionPair = new Tuple<ActionInfo, ActionInfo>(first, second); 
            if (failurePreservationCheckerCache.Contains(actionPair))
                return;
            failurePreservationCheckerCache.Add(actionPair);

            List<Variable> inputs = new List<Variable>();
            inputs.AddRange(first.thisInParams);
            inputs.AddRange(second.thatInParams);

            Expr transitionRelation = (new TransitionRelationComputation(program, second)).Compute();
            Expr expr = Expr.True;
            foreach (AssertCmd assertCmd in first.thisGate)
            {
                expr = Expr.And(assertCmd.Expr, expr);
            }
            List<Requires> requires = DisjointnessRequires(program, first, second);
            requires.Add(new Requires(false, Expr.Not(expr)));
            foreach (AssertCmd assertCmd in second.thatGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }
            
            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> oldMap = new Dictionary<Variable, Expr>();
            List<Variable> boundVars = new List<Variable>();
            foreach (Variable v in program.GlobalVariables())
            {
                BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "post_" + v.Name, v.TypedIdent.Type));
                boundVars.Add(bv);
                map[v] = new IdentifierExpr(Token.NoToken, bv);
            }
            foreach (Variable v in second.thatOutParams)
            {
                {
                    BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "post_" + v.Name, v.TypedIdent.Type));
                    boundVars.Add(bv);
                    map[v] = new IdentifierExpr(Token.NoToken, bv);
                }
                {
                    BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "pre_" + v.Name, v.TypedIdent.Type));
                    boundVars.Add(bv);
                    oldMap[v] = new IdentifierExpr(Token.NoToken, bv);
                }
            }
            foreach (Variable v in second.thatAction.LocVars)
            {
                BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "pre_" + v.Name, v.TypedIdent.Type));
                boundVars.Add(bv);
                oldMap[v] = new IdentifierExpr(Token.NoToken, bv);
            }

            Expr ensuresExpr = Expr.And(transitionRelation, Expr.Not(expr));
            if (boundVars.Count > 0)
            {
                Substitution subst = Substituter.SubstitutionFromHashtable(map);
                Substitution oldSubst = Substituter.SubstitutionFromHashtable(oldMap);
                ensuresExpr = new ExistsExpr(Token.NoToken, boundVars, (Expr)new MySubstituter(subst, oldSubst).Visit(ensuresExpr));
            }
            List<Ensures> ensures = new List<Ensures>();
            ensures.Add(new Ensures(false, ensuresExpr));
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