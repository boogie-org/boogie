using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    class NoninterferenceInstrumentation
    {
        private CivlTypeChecker civlTypeChecker;
        private LinearTypeChecker linearTypeChecker;
        private Dictionary<Variable, Variable> ogOldGlobalMap;
        private Dictionary<string, Variable> domainNameToLocalVar;
        private Procedure yieldProc;

        public NoninterferenceInstrumentation(
            CivlTypeChecker civlTypeChecker,
            LinearTypeChecker linearTypeChecker,
            int layerNum,
            Dictionary<Variable, Variable> ogOldGlobalMap,
            Dictionary<string, Variable> domainNameToLocalVar,
            Procedure yieldProc)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.ogOldGlobalMap = ogOldGlobalMap;
            this.domainNameToLocalVar = domainNameToLocalVar;
            this.yieldProc = yieldProc;
        }

        public List<Cmd> AddUpdatesToOldGlobalVars(Dictionary<string, Expr> domainNameToExpr)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(domainNameToLocalVar[domainName])));
                rhss.Add(domainNameToExpr[domainName]);
            }
            foreach (Variable g in ogOldGlobalMap.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(ogOldGlobalMap[g])));
                rhss.Add(Expr.Ident(g));
            }
            var cmds = new List<Cmd>();
            if (lhss.Count > 0)
            {
                cmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }
            return cmds;
        }

        public List<Cmd> CreateInitCmds(Implementation impl)
        {
            Dictionary<string, Expr> domainNameToExpr = new Dictionary<string, Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                var domain = linearTypeChecker.linearDomains[domainName];
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new Expr[] {Expr.False});
                domainNameToExpr[domainName] = expr;
            }

            foreach (var inParam in impl.InParams)
            {
                var domainName = linearTypeChecker.FindDomainName(inParam);
                if (domainName == null) continue;
                var domain = linearTypeChecker.linearDomains[domainName];
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[inParam.TypedIdent.Type]),
                    new List<Expr> {Expr.Ident(inParam)});
                domainNameToExpr[domainName] = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool),
                    new List<Expr> {ie, domainNameToExpr[domainName]});
            }

            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(domainNameToLocalVar[domainName])));
                rhss.Add(domainNameToExpr[domainName]);
            }

            foreach (Variable g in ogOldGlobalMap.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(ogOldGlobalMap[g])));
                rhss.Add(Expr.Ident(g));
            }

            var initCmds = new List<Cmd>();
            if (lhss.Count > 0)
            {
                initCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }

            return initCmds;
        }

        public CallCmd CallToYieldProc(IToken tok)
        {
            List<Expr> exprSeq = new List<Expr>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                exprSeq.Add(Expr.Ident(domainNameToLocalVar[domainName]));
            }

            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                exprSeq.Add(Expr.Ident(ogOldGlobalMap[g]));
            }

            CallCmd yieldCallCmd = new CallCmd(Token.NoToken, yieldProc.Name, exprSeq, new List<IdentifierExpr>());
            yieldCallCmd.Proc = yieldProc;
            return yieldCallCmd;
        }

        public List<Cmd> CreateAssumeCmds(Dictionary<string, Expr> domainNameToExpr)
        {
            List<Cmd> newCmds = new List<Cmd>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                newCmds.Add(new AssumeCmd(Token.NoToken,
                    Expr.Eq(Expr.Ident(domainNameToLocalVar[domainName]), domainNameToExpr[domainName])));
            }

            foreach (Variable v in ogOldGlobalMap.Keys)
            {
                newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Eq(Expr.Ident(v), Expr.Ident(ogOldGlobalMap[v]))));
            }

            return newCmds;
        }

        public void CreateYieldCheckerImpl(
            Implementation impl,
            List<List<PredicateCmd>> yields,
            out Procedure yieldCheckerProc,
            out Implementation yieldCheckerImpl)
        {
            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            List<Variable> locals = new List<Variable>();
            List<Variable> inputs = new List<Variable>();

            foreach (Variable local in impl.LocVars.Union(impl.InParams).Union(impl.OutParams))
            {
                var copy = CopyLocal(local);
                locals.Add(copy);
                map[local] = Expr.Ident(copy);
            }

            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                var inParam = linearTypeChecker.LinearDomainInFormal(domainName);
                inputs.Add(inParam);
                map[linearTypeChecker.domainNameToHoleVar[domainName]] = Expr.Ident(inParam);
            }

            Dictionary<Variable, Expr> ogOldLocalMap = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> assumeMap = new Dictionary<Variable, Expr>(map);
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                var copy = OgOldLocalLocal(g);
                locals.Add(copy);
                ogOldLocalMap[g] = Expr.Ident(copy);
                Formal f = OgOldGlobalFormal(g);
                inputs.Add(f);
                assumeMap[g] = Expr.Ident(f);
            }

            Substitution assumeSubst = Substituter.SubstitutionFromHashtable(assumeMap);
            Substitution oldSubst = Substituter.SubstitutionFromHashtable(ogOldLocalMap);
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            List<Block> yieldCheckerBlocks = new List<Block>();
            List<String> labels = new List<String>();
            List<Block> labelTargets = new List<Block>();
            Block yieldCheckerBlock = new Block(Token.NoToken, "exit", new List<Cmd>(), new ReturnCmd(Token.NoToken));
            labels.Add(yieldCheckerBlock.Label);
            labelTargets.Add(yieldCheckerBlock);
            yieldCheckerBlocks.Add(yieldCheckerBlock);
            int yieldCount = 0;
            foreach (var cs in yields)
            {
                List<Cmd> newCmds = new List<Cmd>();
                foreach (var predCmd in cs)
                {
                    var newExpr = Substituter.ApplyReplacingOldExprs(assumeSubst, oldSubst, predCmd.Expr);
                    newCmds.Add(new AssumeCmd(Token.NoToken, newExpr));
                }

                foreach (var predCmd in cs)
                {
                    if (predCmd is AssertCmd)
                    {
                        var newExpr = Substituter.ApplyReplacingOldExprs(subst, oldSubst, predCmd.Expr);
                        AssertCmd assertCmd = new AssertCmd(predCmd.tok, newExpr, predCmd.Attributes);
                        assertCmd.ErrorData = "Non-interference check failed";
                        newCmds.Add(assertCmd);
                    }

                    /*
                    Disjointness assumes injected by LinearTypeChecker are dropped now because the 
                    previous loop has already substituted the old global state in these assumes.
                    It would be unsound to have these assumes on the current global state.
                    */
                }

                newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                yieldCheckerBlock = new Block(Token.NoToken, "L" + yieldCount++, newCmds, new ReturnCmd(Token.NoToken));
                labels.Add(yieldCheckerBlock.Label);
                labelTargets.Add(yieldCheckerBlock);
                yieldCheckerBlocks.Add(yieldCheckerBlock);
            }

            yieldCheckerBlocks.Insert(0,
                new Block(Token.NoToken, "enter", new List<Cmd>(), new GotoCmd(Token.NoToken, labels, labelTargets)));

            // Create the yield checker procedure
            var yieldCheckerName = string.Format("Impl_YieldChecker_{0}", impl.Name);
            yieldCheckerProc = new Procedure(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs,
                new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            CivlUtil.AddInlineAttribute(yieldCheckerProc);

            // Create the yield checker implementation
            yieldCheckerImpl = new Implementation(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs,
                new List<Variable>(), locals, yieldCheckerBlocks);
            yieldCheckerImpl.Proc = yieldCheckerProc;
            CivlUtil.AddInlineAttribute(yieldCheckerImpl);
        }

        public void UnifyCallsToYieldProc(Implementation impl)
        {
            CallCmd yieldCallCmd = CallToYieldProc(Token.NoToken);
            Block yieldCheckBlock = new Block(Token.NoToken, "CallToYieldProc",
                new List<Cmd> {yieldCallCmd, new AssumeCmd(Token.NoToken, Expr.False)}, new ReturnCmd(Token.NoToken));
            List<Block> newBlocks = new List<Block>();
            foreach (Block b in impl.Blocks)
            {
                TransferCmd transferCmd = b.TransferCmd;
                List<Cmd> newCmds = new List<Cmd>();
                for (int i = b.Cmds.Count - 1; i >= 0; i--)
                {
                    if (b.Cmds[i] is CallCmd callCmd && callCmd.Proc == yieldProc)
                    {
                        Block newBlock = new Block(Token.NoToken, b.Label + i, newCmds, transferCmd);
                        newCmds = new List<Cmd>();
                        transferCmd = new GotoCmd(Token.NoToken,
                            new List<string> {newBlock.Label, yieldCheckBlock.Label},
                            new List<Block> {newBlock, yieldCheckBlock});
                        newBlocks.Add(newBlock);
                    }
                    else
                    {
                        newCmds.Insert(0, b.Cmds[i]);
                    }
                }

                b.Cmds = newCmds;
                b.TransferCmd = transferCmd;
            }

            impl.Blocks.AddRange(newBlocks);
            impl.Blocks.Add(yieldCheckBlock);
        }

        private Formal OgOldGlobalFormal(Variable v)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", v.Name), v.TypedIdent.Type), true);
        }

        private LocalVariable OgOldLocalLocal(Variable v)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format("og_local_old_{0}", v.Name), v.TypedIdent.Type));
        }

        private LocalVariable CopyLocal(Variable v)
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type));
        }
    }
}