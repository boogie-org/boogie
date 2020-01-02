using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    interface NoninterferenceInstrumentation
    {
        List<Variable> NewLocalVars { get; }
        List<Cmd> CreateUpdatesToPermissionCollector(Absy absy);
        List<Cmd> CreateInitCmds(Implementation impl);
        List<Declaration> CreateYieldCheckerProcImpl(Implementation impl, IEnumerable<List<PredicateCmd>> yields);
        List<Cmd> CreateCallToYieldProc();
    }
    
    class NoneNoninterferenceInstrumentation : NoninterferenceInstrumentation
    {
        public List<Variable> NewLocalVars => new List<Variable>();
        
        public List<Cmd> CreateUpdatesToPermissionCollector(Absy absy)
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateInitCmds(Implementation impl)
        {
            return new List<Cmd>();
        }

        public List<Declaration> CreateYieldCheckerProcImpl(Implementation impl, IEnumerable<List<PredicateCmd>> yields)
        {
            return new List<Declaration>();
        }

        public List<Cmd> CreateCallToYieldProc()
        {
            return new List<Cmd>();
        }
    }

    class SomeNoninterferenceInstrumentation : NoninterferenceInstrumentation
    {
        private CivlTypeChecker civlTypeChecker;
        private LinearTypeChecker linearTypeChecker;
        private int layerNum;
        private Dictionary<Absy, Absy> absyMap;
        private Dictionary<Variable, Variable> oldGlobalMap;
        private List<Variable> newLocalVars;
        private Dictionary<string, Variable> domainNameToLocalVar;
        private Procedure yieldProc;

        public SomeNoninterferenceInstrumentation(
            CivlTypeChecker civlTypeChecker,
            LinearTypeChecker linearTypeChecker,
            int layerNum,
            Dictionary<Absy, Absy> absyMap,
            Dictionary<Variable, Variable> oldGlobalMap,
            Procedure yieldProc)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.layerNum = layerNum;
            this.absyMap = absyMap;
            this.oldGlobalMap = oldGlobalMap;
            this.yieldProc = yieldProc;
            this.newLocalVars = new List<Variable>();
            this.domainNameToLocalVar = new Dictionary<string, Variable>();
            {
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable l = linearTypeChecker.LinearDomainAvailableLocal(domainName);
                    domainNameToLocalVar[domainName] = l;
                    newLocalVars.Add(l);
                }
            }
        }

        public List<Variable> NewLocalVars => newLocalVars;

        public List<Cmd> CreateUpdatesToPermissionCollector(Absy absy)
        {
            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(AvailableLinearVars(absy));
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(domainNameToLocalVar[domainName])));
                rhss.Add(domainNameToExpr[domainName]);
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
            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(impl.InParams.FindAll(x => linearTypeChecker.FindDomainName(x) != null));
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(domainNameToLocalVar[domainName])));
                rhss.Add(domainNameToExpr[domainName]);
            }
            var initCmds = new List<Cmd>();
            if (lhss.Count > 0)
            {
                initCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }
            return initCmds;
        }

        public List<Declaration> CreateYieldCheckerProcImpl(
            Implementation impl,
            IEnumerable<List<PredicateCmd>> yields)
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

            Dictionary<Variable, Expr> oldLocalMap = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> assumeMap = new Dictionary<Variable, Expr>(map);
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                var copy = OldLocalLocal(g);
                locals.Add(copy);
                oldLocalMap[g] = Expr.Ident(copy);
                Formal f = OldGlobalFormal(g);
                inputs.Add(f);
                assumeMap[g] = Expr.Ident(f);
            }

            Substitution assumeSubst = Substituter.SubstitutionFromHashtable(assumeMap);
            Substitution oldSubst = Substituter.SubstitutionFromHashtable(oldLocalMap);
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
            var yieldCheckerName = $"Impl_YieldChecker_{impl.Name}";
            var yieldCheckerProc = new Procedure(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs,
                new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            CivlUtil.AddInlineAttribute(yieldCheckerProc);

            // Create the yield checker implementation
            var yieldCheckerImpl = new Implementation(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs,
                new List<Variable>(), locals, yieldCheckerBlocks);
            yieldCheckerImpl.Proc = yieldCheckerProc;
            CivlUtil.AddInlineAttribute(yieldCheckerImpl);
            return new List<Declaration>{ yieldCheckerProc, yieldCheckerImpl };
        }

        public List<Cmd> CreateCallToYieldProc()
        {
            List<Expr> exprSeq = new List<Expr>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                exprSeq.Add(Expr.Ident(domainNameToLocalVar[domainName]));
            }

            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                exprSeq.Add(Expr.Ident(oldGlobalMap[g]));
            }

            CallCmd yieldCallCmd = new CallCmd(Token.NoToken, yieldProc.Name, exprSeq, new List<IdentifierExpr>());
            yieldCallCmd.Proc = yieldProc;
            return new List<Cmd> {yieldCallCmd};
        }

        private IEnumerable<Variable> AvailableLinearVars(Absy absy)
        {
            HashSet<Variable> availableVars =
                new HashSet<Variable>(linearTypeChecker.AvailableLinearVars(absyMap[absy]));

            // A bit hackish, since GlobalVariableLayerRange and LocalVariableIntroLayer return maximum layer range
            // respectively minimum layer if called on non-global respectively non-local variable.
            availableVars.RemoveWhere(v =>
                !civlTypeChecker.GlobalVariableLayerRange(v).Contains(layerNum) ||
                layerNum < civlTypeChecker.LocalVariableIntroLayer(v)
            );

            return availableVars;
        }

        private Dictionary<string, Expr> ComputeAvailableExprs(IEnumerable<Variable> availableLinearVars)
        {
            Dictionary<string, Expr> domainNameToExpr = new Dictionary<string, Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                var domain = linearTypeChecker.linearDomains[domainName];
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new Expr[] {Expr.False});
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }

            foreach (Variable v in availableLinearVars)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                var domain = linearTypeChecker.linearDomains[domainName];
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]),
                    new List<Expr> {Expr.Ident(v)});
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool),
                    new List<Expr> {ie, domainNameToExpr[domainName]});
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }

            return domainNameToExpr;
        }

        private Formal OldGlobalFormal(Variable v)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, $"og_global_old_{v.Name}", v.TypedIdent.Type), true);
        }

        private LocalVariable OldLocalLocal(Variable v)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, $"og_local_old_{v.Name}", v.TypedIdent.Type));
        }

        private LocalVariable CopyLocal(Variable v)
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type));
        }
    }
}
