using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
    public class MyDuplicator : Duplicator
    {
        CivlTypeChecker civlTypeChecker;
        public int layerNum;
        Procedure enclosingProc;
        Implementation enclosingImpl;
        public Dictionary<Procedure, Procedure> procMap; /* Original -> Duplicate */
        public Dictionary<Absy, Absy> absyMap; /* Duplicate -> Original */
        public Dictionary<Implementation, Implementation> implMap; /* Duplicate -> Original */
        public HashSet<Procedure> yieldingProcs;
        public List<Implementation> impls;

        public MyDuplicator(CivlTypeChecker civlTypeChecker, int layerNum)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.layerNum = layerNum;
            this.enclosingProc = null;
            this.enclosingImpl = null;
            this.procMap = new Dictionary<Procedure, Procedure>();
            this.absyMap = new Dictionary<Absy, Absy>();
            this.implMap = new Dictionary<Implementation, Implementation>();
            this.yieldingProcs = new HashSet<Procedure>();
            this.impls = new List<Implementation>();
        }

        private void ProcessCallCmd(CallCmd originalCallCmd, CallCmd callCmd, List<Cmd> newCmds)
        {
            int enclosingProcLayerNum = civlTypeChecker.procToActionInfo[enclosingImpl.Proc].createdAtLayerNum;
            Procedure originalProc = originalCallCmd.Proc;
            
            if (civlTypeChecker.procToAtomicProcedureInfo.ContainsKey(originalProc))
            {
                if (civlTypeChecker.CallExists(originalCallCmd, enclosingProcLayerNum, layerNum))
                {
                    newCmds.Add(callCmd);
                }
            }
            else if (civlTypeChecker.procToActionInfo.ContainsKey(originalProc))
            {
                AtomicActionInfo atomicActionInfo = civlTypeChecker.procToActionInfo[originalProc] as AtomicActionInfo;
                if (atomicActionInfo != null && atomicActionInfo.gate.Count > 0 && layerNum == enclosingProcLayerNum)
                {
                    newCmds.Add(new HavocCmd(Token.NoToken, new List<IdentifierExpr>(new IdentifierExpr[] { Expr.Ident(dummyLocalVar) })));
                    Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                    for (int i = 0; i < originalProc.InParams.Count; i++)
                    {
                        map[originalProc.InParams[i]] = callCmd.Ins[i];
                    }
                    Substitution subst = Substituter.SubstitutionFromHashtable(map);
                    foreach (AssertCmd assertCmd in atomicActionInfo.gate)
                    {
                        newCmds.Add(Substituter.Apply(subst, assertCmd));
                    }
                }
                newCmds.Add(callCmd);
            }
            else
            {
                Debug.Assert(false);
            }
        }

        private void ProcessParCallCmd(ParCallCmd originalParCallCmd, ParCallCmd parCallCmd, List<Cmd> newCmds)
        {
            int maxCalleeLayerNum = 0;
            foreach (CallCmd iter in originalParCallCmd.CallCmds)
            {
                int calleeLayerNum = civlTypeChecker.procToActionInfo[iter.Proc].createdAtLayerNum;
                if (calleeLayerNum > maxCalleeLayerNum)
                    maxCalleeLayerNum = calleeLayerNum;
            }
            if (layerNum > maxCalleeLayerNum)
            {
                for (int i = 0; i < parCallCmd.CallCmds.Count; i++) 
                {
                    ProcessCallCmd(originalParCallCmd.CallCmds[i], parCallCmd.CallCmds[i], newCmds);
                    absyMap[parCallCmd.CallCmds[i]] = originalParCallCmd;
                }
            }
            else
            {
                newCmds.Add(parCallCmd);
            }
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> cmds = base.VisitCmdSeq(cmdSeq);
            List<Cmd> newCmds = new List<Cmd>();
            for (int i = 0; i < cmds.Count; i++)
            {
                Cmd originalCmd = cmdSeq[i];
                Cmd cmd = cmds[i];

                CallCmd originalCallCmd = originalCmd as CallCmd;
                if (originalCallCmd != null)
                {
                    ProcessCallCmd(originalCallCmd, cmd as CallCmd, newCmds);
                    continue;
                }

                ParCallCmd originalParCallCmd = originalCmd as ParCallCmd;
                if (originalParCallCmd != null)
                {
                    ProcessParCallCmd(originalParCallCmd, cmd as ParCallCmd, newCmds);
                    continue;
                }
             
                newCmds.Add(cmd);
            }
            return newCmds;
        }

        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            YieldCmd yieldCmd = base.VisitYieldCmd(node);
            absyMap[yieldCmd] = node;
            return yieldCmd;
        }
        
        public override Block VisitBlock(Block node)
        {
            Block block = base.VisitBlock(node);
            absyMap[block] = node;
            return block;
        }
        
        public override Cmd VisitCallCmd(CallCmd node)
        {
            CallCmd callCmd = (CallCmd) base.VisitCallCmd(node);
            callCmd.Proc = VisitProcedure(callCmd.Proc);
            callCmd.callee = callCmd.Proc.Name;
            absyMap[callCmd] = node;
            return callCmd;
        }

        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            ParCallCmd parCallCmd = (ParCallCmd) base.VisitParCallCmd(node);
            absyMap[parCallCmd] = node;
            return parCallCmd;
        }

        public override Procedure VisitProcedure(Procedure node)
        {
            if (!civlTypeChecker.procToActionInfo.ContainsKey(node))
                return node;
            if (!procMap.ContainsKey(node))
            {
                enclosingProc = node;
                Procedure proc = (Procedure)node.Clone();
                proc.Name = string.Format("{0}_{1}", node.Name, layerNum);
                proc.InParams = this.VisitVariableSeq(node.InParams);
                proc.Modifies = this.VisitIdentifierExprSeq(node.Modifies);
                proc.OutParams = this.VisitVariableSeq(node.OutParams);

                ActionInfo actionInfo = civlTypeChecker.procToActionInfo[node];
                if (actionInfo.createdAtLayerNum < layerNum)
                {
                    proc.Requires = new List<Requires>();
                    proc.Ensures = new List<Ensures>();
                    Implementation impl;
                    AtomicActionInfo atomicActionInfo = actionInfo as AtomicActionInfo;
                    if (atomicActionInfo != null)
                    {
                        CodeExpr action = (CodeExpr)VisitCodeExpr(atomicActionInfo.action);
                        List<Cmd> cmds = new List<Cmd>();
                        foreach (AssertCmd assertCmd in atomicActionInfo.gate)
                        {
                            cmds.Add(new AssumeCmd(Token.NoToken, (Expr)Visit(assertCmd.Expr)));
                        }
                        Block newInitBlock = new Block(Token.NoToken, "_init", cmds,
                            new GotoCmd(Token.NoToken, new List<string>(new string[] { action.Blocks[0].Label }),
                                                       new List<Block>(new Block[] { action.Blocks[0] })));
                        List<Block> newBlocks = new List<Block>();
                        newBlocks.Add(newInitBlock);
                        newBlocks.AddRange(action.Blocks);
                        impl = new Implementation(Token.NoToken, proc.Name, node.TypeParameters, node.InParams, node.OutParams, action.LocVars, newBlocks);
                    }
                    else
                    {
                        Block newInitBlock = new Block(Token.NoToken, "_init", new List<Cmd>(), new ReturnCmd(Token.NoToken));
                        List<Block> newBlocks = new List<Block>();
                        newBlocks.Add(newInitBlock);
                        impl = new Implementation(Token.NoToken, proc.Name, node.TypeParameters, node.InParams, node.OutParams, new List<Variable>(), newBlocks);
                    }
                    impl.Proc = proc;
                    impl.Proc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                    impl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                    impls.Add(impl);
                }
                else
                {
                    yieldingProcs.Add(proc);
                    proc.Requires = this.VisitRequiresSeq(node.Requires);
                    proc.Ensures = this.VisitEnsuresSeq(node.Ensures);
                }
                procMap[node] = proc;
                proc.Modifies = new List<IdentifierExpr>();
                civlTypeChecker.SharedVariables.Iter(x => proc.Modifies.Add(Expr.Ident(x)));
            }
            return procMap[node];
        }

        private Variable dummyLocalVar;
        public override Implementation VisitImplementation(Implementation node)
        {
            enclosingImpl = node;
            dummyLocalVar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_dummy", Type.Bool));
            Implementation impl = base.VisitImplementation(node);
            implMap[impl] = node;
            impl.LocVars.Add(dummyLocalVar);
            impl.Name = impl.Proc.Name;
            return impl;
        }

        public override Requires VisitRequires(Requires node)
        {
            Requires requires = base.VisitRequires(node);
            if (node.Free)
                return requires;
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                requires.Condition = Expr.True;
            return requires;
        }

        public override Ensures VisitEnsures(Ensures node)
        {
            Ensures ensures = base.VisitEnsures(node);
            if (node.Free)
                return ensures;
            AtomicActionInfo atomicActionInfo =  civlTypeChecker.procToActionInfo[enclosingProc] as AtomicActionInfo;
            bool isAtomicSpecification = atomicActionInfo != null && atomicActionInfo.ensures == node;
            if (isAtomicSpecification || !civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
            {
                ensures.Condition = Expr.True;
                ensures.Attributes = CivlRefinement.RemoveMoverAttribute(ensures.Attributes);
            }
            return ensures;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            AssertCmd assertCmd = (AssertCmd) base.VisitAssertCmd(node);
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                assertCmd.Expr = Expr.True;
            return assertCmd;
        }
    }

    public class CivlRefinement
    {
        LinearTypeChecker linearTypeChecker;
        CivlTypeChecker civlTypeChecker;
        Dictionary<Absy, Absy> absyMap;
        Dictionary<Implementation, Implementation> implMap;
        HashSet<Procedure> yieldingProcs;
        int layerNum;
        List<IdentifierExpr> globalMods;
        Dictionary<string, Procedure> asyncAndParallelCallDesugarings;
        List<Procedure> yieldCheckerProcs;
        List<Implementation> yieldCheckerImpls;
        Procedure yieldProc;

        Variable pc;
        Variable ok;
        Expr alpha;
        Expr beta;
        HashSet<Variable> frame;

        public CivlRefinement(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, MyDuplicator duplicator)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.civlTypeChecker = civlTypeChecker;
            this.absyMap = duplicator.absyMap;
            this.layerNum = duplicator.layerNum;
            this.implMap = duplicator.implMap;
            this.yieldingProcs = duplicator.yieldingProcs;
            Program program = linearTypeChecker.program;
            globalMods = new List<IdentifierExpr>();
            foreach (Variable g in civlTypeChecker.SharedVariables)
            {
                globalMods.Add(Expr.Ident(g));
            }
            asyncAndParallelCallDesugarings = new Dictionary<string, Procedure>();
            yieldCheckerProcs = new List<Procedure>();
            yieldCheckerImpls = new List<Implementation>();
            yieldProc = null;
        }

        private IEnumerable<Variable> AvailableLinearVars(Absy absy)
        {
            HashSet<Variable> availableVars = new HashSet<Variable>(linearTypeChecker.AvailableLinearVars(absyMap[absy]));
            foreach (var g in civlTypeChecker.globalVarToSharedVarInfo.Keys)
            {
                SharedVariableInfo info = civlTypeChecker.globalVarToSharedVarInfo[g];
                if (!(info.introLayerNum <= layerNum && layerNum <= info.hideLayerNum))
                {
                    availableVars.Remove(g);
                }
            }
            foreach (var v in civlTypeChecker.localVarToLocalVariableInfo.Keys)
            {
                LocalVariableInfo info = civlTypeChecker.localVarToLocalVariableInfo[v];
                if (layerNum < info.layer)
                {
                    availableVars.Remove(v);
                }
            }
            return availableVars;
        }

        private CallCmd CallToYieldProc(IToken tok, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar)
        {
            List<Expr> exprSeq = new List<Expr>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                exprSeq.Add(Expr.Ident(domainNameToLocalVar[domainName]));
            }
            foreach (IdentifierExpr ie in globalMods)
            {
                exprSeq.Add(Expr.Ident(ogOldGlobalMap[ie.Decl]));
            }
            if (yieldProc == null)
            {
                List<Variable> inputs = new List<Variable>();
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    var domain = linearTypeChecker.linearDomains[domainName];
                    Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "linear_" + domainName + "_in", new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { domain.elementType }, Type.Bool)), true);
                    inputs.Add(f);
                }
                foreach (IdentifierExpr ie in globalMods)
                {
                    Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", ie.Decl.Name), ie.Decl.TypedIdent.Type), true);
                    inputs.Add(f);
                }
                yieldProc = new Procedure(Token.NoToken, string.Format("og_yield_{0}", layerNum), new List<TypeVariable>(), inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
                yieldProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            }
            CallCmd yieldCallCmd = new CallCmd(Token.NoToken, yieldProc.Name, exprSeq, new List<IdentifierExpr>());
            yieldCallCmd.Proc = yieldProc;
            return yieldCallCmd;
        }

        private void AddCallToYieldProc(IToken tok, List<Cmd> newCmds, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar)
        {
            if (!CommandLineOptions.Clo.TrustNonInterference)
            {
                CallCmd yieldCallCmd = CallToYieldProc(tok, ogOldGlobalMap, domainNameToLocalVar);
                newCmds.Add(yieldCallCmd);
            }

            if (pc != null)
            {
                Expr aa = OldEqualityExprForGlobals(ogOldGlobalMap);
                Expr bb = OldEqualityExpr(ogOldGlobalMap);

                // assert pc || g_old == g || beta(i, g_old, o, g);
                Expr assertExpr = Expr.Or(Expr.Ident(pc), Expr.Or(aa, beta));
                assertExpr.Typecheck(new TypecheckingContext(null));
                AssertCmd skipOrBetaAssertCmd = new AssertCmd(tok, assertExpr);
                skipOrBetaAssertCmd.ErrorData = "Transition invariant in initial state violated";
                newCmds.Add(skipOrBetaAssertCmd);

                // assert pc ==> o_old == o && g_old == g;
                assertExpr = Expr.Imp(Expr.Ident(pc), bb);
                assertExpr.Typecheck(new TypecheckingContext(null));
                AssertCmd skipAssertCmd = new AssertCmd(tok, assertExpr);
                skipAssertCmd.ErrorData = "Transition invariant in final state violated"; ;
                newCmds.Add(skipAssertCmd);

                // pc, ok := g_old == g ==> pc, ok || beta(i, g_old, o, g);
                List<AssignLhs> pcUpdateLHS = new List<AssignLhs>(
                    new AssignLhs[] { 
                        new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)), 
                        new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok))
                    });
                List<Expr> pcUpdateRHS = new List<Expr>(
                    new Expr[] { 
                        Expr.Imp(aa, Expr.Ident(pc)),
                        Expr.Or(Expr.Ident(ok), beta)
                    });
                foreach (Expr e in pcUpdateRHS)
                {
                    e.Typecheck(new TypecheckingContext(null));
                }
                newCmds.Add(new AssignCmd(Token.NoToken, pcUpdateLHS, pcUpdateRHS));
            }
        }

        private Dictionary<string, Expr> ComputeAvailableExprs(IEnumerable<Variable> availableLinearVars, Dictionary<string, Variable> domainNameToInputVar)
        {
            Dictionary<string, Expr> domainNameToExpr = new Dictionary<string, Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                var expr = Expr.Ident(domainNameToInputVar[domainName]);
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }
            foreach (Variable v in availableLinearVars)
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                var domain = linearTypeChecker.linearDomains[domainName];
                if (!domain.collectors.ContainsKey(v.TypedIdent.Type)) continue;
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]), new List<Expr> { Expr.Ident(v) });
                var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new List<Expr> { ie, domainNameToExpr[domainName] });
                expr.Resolve(new ResolutionContext(null));
                expr.Typecheck(new TypecheckingContext(null));
                domainNameToExpr[domainName] = expr;
            }
            return domainNameToExpr;
        }

        private void AddUpdatesToOldGlobalVars(List<Cmd> newCmds, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar, Dictionary<string, Expr> domainNameToExpr)
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
            if (lhss.Count > 0)
            {
                newCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }
        }

        private Expr OldEqualityExpr(Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            Expr bb = Expr.True;
            foreach (Variable o in ogOldGlobalMap.Keys)
            {
                if (o is GlobalVariable && !frame.Contains(o)) continue;
                bb = Expr.And(bb, Expr.Eq(Expr.Ident(o), Expr.Ident(ogOldGlobalMap[o])));
                bb.Type = Type.Bool;
            }
            return bb;
        }

        private Expr OldEqualityExprForGlobals(Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            Expr bb = Expr.True;
            foreach (Variable o in ogOldGlobalMap.Keys)
            {
                if (o is GlobalVariable && frame.Contains(o))
                {
                    bb = Expr.And(bb, Expr.Eq(Expr.Ident(o), Expr.Ident(ogOldGlobalMap[o])));
                    bb.Type = Type.Bool;
                }
            }
            return bb;
        }

        private void DesugarYield(YieldCmd yieldCmd, List<Cmd> cmds, List<Cmd> newCmds, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToInputVar, Dictionary<string, Variable> domainNameToLocalVar)
        {
            AddCallToYieldProc(yieldCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);

            if (globalMods.Count > 0)
            {
                newCmds.Add(new HavocCmd(Token.NoToken, globalMods));
                if (pc != null)
                {
                    // assume pc || alpha(i, g);
                    Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
                    assumeExpr.Type = Type.Bool;
                    newCmds.Add(new AssumeCmd(Token.NoToken, assumeExpr));
                }
            }

            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(AvailableLinearVars(yieldCmd), domainNameToInputVar);
            AddUpdatesToOldGlobalVars(newCmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);

            for (int j = 0; j < cmds.Count; j++)
            {
                PredicateCmd predCmd = (PredicateCmd)cmds[j];
                newCmds.Add(new AssumeCmd(Token.NoToken, predCmd.Expr));
            }
        }

        public void DesugarParallelCallCmd(List<Cmd> newCmds, ParCallCmd parCallCmd)
        {
            List<string> parallelCalleeNames = new List<string>();
            List<Expr> ins = new List<Expr>();
            List<IdentifierExpr> outs = new List<IdentifierExpr>();
            string procName = "og";
            foreach (CallCmd callCmd in parCallCmd.CallCmds)
            {
                procName = procName + "_" + callCmd.Proc.Name;
                ins.AddRange(callCmd.Ins);
                outs.AddRange(callCmd.Outs);
            }
            Procedure proc;
            if (asyncAndParallelCallDesugarings.ContainsKey(procName))
            {
                proc = asyncAndParallelCallDesugarings[procName];
            }
            else
            {
                List<Variable> inParams = new List<Variable>();
                List<Variable> outParams = new List<Variable>();
                List<Requires> requiresSeq = new List<Requires>();
                List<Ensures> ensuresSeq = new List<Ensures>();
                int count = 0;
                foreach (CallCmd callCmd in parCallCmd.CallCmds)
                {
                    Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                    foreach (Variable x in callCmd.Proc.InParams)
                    {
                        Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_{0}_{1}", count, x.Name), x.TypedIdent.Type), true);
                        inParams.Add(y);
                        map[x] = Expr.Ident(y);
                    }
                    foreach (Variable x in callCmd.Proc.OutParams)
                    {
                        Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_{0}_{1}", count, x.Name), x.TypedIdent.Type), false);
                        outParams.Add(y);
                        map[x] = Expr.Ident(y);
                    }
                    Contract.Assume(callCmd.Proc.TypeParameters.Count == 0);
                    Substitution subst = Substituter.SubstitutionFromHashtable(map);
                    foreach (Requires req in callCmd.Proc.Requires)
                    {
                        requiresSeq.Add(new Requires(req.tok, req.Free, Substituter.Apply(subst, req.Condition), null, req.Attributes));
                    }
                    foreach (Ensures ens in callCmd.Proc.Ensures)
                    {
                        ensuresSeq.Add(new Ensures(ens.tok, ens.Free, Substituter.Apply(subst, ens.Condition), null, ens.Attributes));
                    }
                    count++;
                }
                proc = new Procedure(Token.NoToken, procName, new List<TypeVariable>(), inParams, outParams, requiresSeq, globalMods, ensuresSeq);
                asyncAndParallelCallDesugarings[procName] = proc;
            }
            CallCmd dummyCallCmd = new CallCmd(parCallCmd.tok, proc.Name, ins, outs, parCallCmd.Attributes);
            dummyCallCmd.Proc = proc;
            newCmds.Add(dummyCallCmd);
        }

        private void CreateYieldCheckerImpl(Implementation impl, List<List<Cmd>> yields)
        {
            if (yields.Count == 0) return;

            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            foreach (Variable local in impl.LocVars)
            {
                var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, local.Name, local.TypedIdent.Type));
                map[local] = Expr.Ident(copy);
            }

            Program program = linearTypeChecker.program;
            List<Variable> locals = new List<Variable>();
            List<Variable> inputs = new List<Variable>();
            foreach (IdentifierExpr ie in map.Values)
            {
                locals.Add(ie.Decl);
            }
            for (int i = 0; i < impl.InParams.Count - linearTypeChecker.linearDomains.Count; i++)
            {
                Variable inParam = impl.InParams[i];
                Variable copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name, inParam.TypedIdent.Type));
                locals.Add(copy);
                map[impl.InParams[i]] = Expr.Ident(copy);
            }
            {
                int i = impl.InParams.Count - linearTypeChecker.linearDomains.Count;
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable inParam = impl.InParams[i];
                    Variable copy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name, inParam.TypedIdent.Type), true);
                    inputs.Add(copy);
                    map[impl.InParams[i]] = Expr.Ident(copy);
                    i++;
                }
            }
            for (int i = 0; i < impl.OutParams.Count; i++)
            {
                Variable outParam = impl.OutParams[i];
                var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, outParam.Name, outParam.TypedIdent.Type));
                locals.Add(copy);
                map[impl.OutParams[i]] = Expr.Ident(copy);
            }
            Dictionary<Variable, Expr> ogOldLocalMap = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> assumeMap = new Dictionary<Variable, Expr>(map);
            foreach (IdentifierExpr ie in globalMods)
            {
                Variable g = ie.Decl;
                var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_local_old_{0}", g.Name), g.TypedIdent.Type));
                locals.Add(copy);
                ogOldLocalMap[g] = Expr.Ident(copy);
                Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", g.Name), g.TypedIdent.Type), true);
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
            foreach (List<Cmd> cs in yields)
            {
                List<Cmd> newCmds = new List<Cmd>();
                foreach (Cmd cmd in cs)
                {
                    PredicateCmd predCmd = (PredicateCmd)cmd;
                    newCmds.Add(new AssumeCmd(Token.NoToken, Substituter.ApplyReplacingOldExprs(assumeSubst, oldSubst, predCmd.Expr)));
                }
                foreach (Cmd cmd in cs)
                {
                    PredicateCmd predCmd = (PredicateCmd)cmd;
                    var newExpr = Substituter.ApplyReplacingOldExprs(subst, oldSubst, predCmd.Expr);
                    if (predCmd is AssertCmd)
                    {
                        AssertCmd assertCmd = new AssertCmd(predCmd.tok, newExpr, predCmd.Attributes);
                        assertCmd.ErrorData = "Non-interference check failed";
                        newCmds.Add(assertCmd);
                    }
                    else
                    {
                        newCmds.Add(new AssumeCmd(Token.NoToken, newExpr));
                    }
                }
                newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                yieldCheckerBlock = new Block(Token.NoToken, "L" + yieldCount++, newCmds, new ReturnCmd(Token.NoToken));
                labels.Add(yieldCheckerBlock.Label);
                labelTargets.Add(yieldCheckerBlock);
                yieldCheckerBlocks.Add(yieldCheckerBlock);
            }
            yieldCheckerBlocks.Insert(0, new Block(Token.NoToken, "enter", new List<Cmd>(), new GotoCmd(Token.NoToken, labels, labelTargets)));

            // Create the yield checker procedure
            var yieldCheckerName = string.Format("{0}_YieldChecker_{1}", "Impl", impl.Name);
            var yieldCheckerProc = new Procedure(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            yieldCheckerProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            yieldCheckerProcs.Add(yieldCheckerProc);

            // Create the yield checker implementation
            var yieldCheckerImpl = new Implementation(Token.NoToken, yieldCheckerName, impl.TypeParameters, inputs, new List<Variable>(), locals, yieldCheckerBlocks);
            yieldCheckerImpl.Proc = yieldCheckerProc;
            yieldCheckerImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            yieldCheckerImpls.Add(yieldCheckerImpl);
        }

        private bool IsYieldingHeader(Graph<Block> graph, Block header)
        {
            foreach (Block backEdgeNode in graph.BackEdgeNodes(header))
            {
                foreach (Block x in graph.NaturalLoops(header, backEdgeNode))
                {
                    foreach (Cmd cmd in x.Cmds)
                    {
                        if (cmd is YieldCmd)
                            return true;
                        if (cmd is ParCallCmd)
                            return true;
                        CallCmd callCmd = cmd as CallCmd;
                        if (callCmd == null) continue;
                        if (yieldingProcs.Contains(callCmd.Proc))
                            return true;
                    }
                }
            }
            return false;
        }

        private Graph<Block> ComputeYieldingLoopHeaders(Implementation impl, out HashSet<Block> yieldingHeaders)
        {
            Graph<Block> graph; 
            impl.PruneUnreachableBlocks();
            impl.ComputePredecessorsForBlocks();
            graph = Program.GraphFromImpl(impl);
            graph.ComputeLoops();
            if (!graph.Reducible)
            {
                throw new Exception("Irreducible flow graphs are unsupported.");
            }
            yieldingHeaders = new HashSet<Block>();
            IEnumerable<Block> sortedHeaders = graph.SortHeadersByDominance();
            foreach (Block header in sortedHeaders)
            {
                if (yieldingHeaders.Any(x => graph.DominatorMap.DominatedBy(x, header)))
                {
                    yieldingHeaders.Add(header);
                }
                else if (IsYieldingHeader(graph, header))
                {
                    yieldingHeaders.Add(header);
                }
                else
                {
                    continue;
                }
            }
            return graph;
        }

        private void SetupRefinementCheck(Implementation impl, 
            out List<Variable> newLocalVars,
            out Dictionary<string, Variable> domainNameToInputVar, out Dictionary<string, Variable> domainNameToLocalVar, out Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            pc = null;
            ok = null;
            alpha = null;
            beta = null;
            frame = null;
            
            newLocalVars = new List<Variable>();
            Program program = linearTypeChecker.program;
            ogOldGlobalMap = new Dictionary<Variable, Variable>();
            foreach (IdentifierExpr ie in globalMods)
            {
                Variable g = ie.Decl;
                LocalVariable l = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", g.Name), g.TypedIdent.Type));
                ogOldGlobalMap[g] = l;
                newLocalVars.Add(l);
            }

            Procedure originalProc = implMap[impl].Proc;
            ActionInfo actionInfo = civlTypeChecker.procToActionInfo[originalProc];
            if (actionInfo.createdAtLayerNum == this.layerNum)
            {
                pc = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_pc", Type.Bool));
                newLocalVars.Add(pc);
                ok = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_ok", Type.Bool));
                newLocalVars.Add(ok);
                Dictionary<Variable, Expr> alwaysMap = new Dictionary<Variable, Expr>();
                for (int i = 0; i < originalProc.InParams.Count; i++)
                {
                    alwaysMap[originalProc.InParams[i]] = Expr.Ident(impl.InParams[i]);
                }
                for (int i = 0; i < originalProc.OutParams.Count; i++)
                {
                    alwaysMap[originalProc.OutParams[i]] = Expr.Ident(impl.OutParams[i]);
                }
                Substitution always = Substituter.SubstitutionFromHashtable(alwaysMap);
                Dictionary<Variable, Expr> foroldMap = new Dictionary<Variable, Expr>();
                foreach (IdentifierExpr ie in globalMods)
                {
                    foroldMap[ie.Decl] = Expr.Ident(ogOldGlobalMap[ie.Decl]);
                }
                Substitution forold = Substituter.SubstitutionFromHashtable(foroldMap);
                frame = new HashSet<Variable>(civlTypeChecker.SharedVariables);
                foreach (Variable v in civlTypeChecker.SharedVariables)
                {
                    if (civlTypeChecker.globalVarToSharedVarInfo[v].hideLayerNum <= actionInfo.createdAtLayerNum || 
                        civlTypeChecker.globalVarToSharedVarInfo[v].introLayerNum > actionInfo.createdAtLayerNum)
                    {
                        frame.Remove(v);
                    }
                }
                AtomicActionInfo atomicActionInfo = actionInfo as AtomicActionInfo;
                if (atomicActionInfo == null)
                {
                    beta = Expr.True;
                    foreach (var v in frame)
                    {
                        beta = Expr.And(beta, Expr.Eq(Expr.Ident(v), foroldMap[v]));
                    }
                    alpha = Expr.True;
                }
                else
                {
                    Expr betaExpr = (new MoverCheck.TransitionRelationComputation(civlTypeChecker.program, atomicActionInfo, frame, new HashSet<Variable>())).TransitionRelationCompute(true);
                    beta = Substituter.ApplyReplacingOldExprs(always, forold, betaExpr);
                    Expr alphaExpr = Expr.True;
                    foreach (AssertCmd assertCmd in atomicActionInfo.gate)
                    {
                        alphaExpr = Expr.And(alphaExpr, assertCmd.Expr);
                        alphaExpr.Type = Type.Bool;
                    }
                    alpha = Substituter.Apply(always, alphaExpr);
                }
                foreach (Variable f in impl.OutParams)
                {
                    LocalVariable copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_old_{0}", f.Name), f.TypedIdent.Type));
                    newLocalVars.Add(copy);
                    ogOldGlobalMap[f] = copy;
                }
            }

            domainNameToInputVar = new Dictionary<string, Variable>();
            domainNameToLocalVar = new Dictionary<string, Variable>();
            {
                int i = impl.InParams.Count - linearTypeChecker.linearDomains.Count;
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable inParam = impl.InParams[i];
                    domainNameToInputVar[domainName] = inParam;
                    Variable l = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name + "_local", inParam.TypedIdent.Type));
                    domainNameToLocalVar[domainName] = l;
                    newLocalVars.Add(l);
                    i++;
                }
            }
        }

        private void TransformImpl(Implementation impl)
        {
            HashSet<Block> yieldingHeaders;
            Graph<Block> graph = ComputeYieldingLoopHeaders(impl, out yieldingHeaders);

            List<Variable> newLocalVars;
            Dictionary<string, Variable> domainNameToInputVar, domainNameToLocalVar;
            Dictionary<Variable, Variable> ogOldGlobalMap;
            SetupRefinementCheck(impl, out newLocalVars, out domainNameToInputVar, out domainNameToLocalVar, out ogOldGlobalMap);

            List<List<Cmd>> yields = CollectAndDesugarYields(impl, domainNameToInputVar, domainNameToLocalVar, ogOldGlobalMap);

            List<Variable> oldPcs, oldOks;
            ProcessLoopHeaders(impl, graph, yieldingHeaders, domainNameToInputVar, domainNameToLocalVar, ogOldGlobalMap, out oldPcs, out oldOks);

            AddInitialBlock(impl, oldPcs, oldOks, domainNameToInputVar, domainNameToLocalVar, ogOldGlobalMap);

            CreateYieldCheckerImpl(impl, yields);
            
            impl.LocVars.AddRange(newLocalVars);
            impl.LocVars.AddRange(oldPcs);
            impl.LocVars.AddRange(oldOks);

            UnifyCallsToYieldProc(impl, ogOldGlobalMap, domainNameToLocalVar);
        }

        private void UnifyCallsToYieldProc(Implementation impl, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar)
        {
            CallCmd yieldCallCmd = CallToYieldProc(Token.NoToken, ogOldGlobalMap, domainNameToLocalVar);
            Block yieldCheckBlock = new Block(Token.NoToken, "CallToYieldProc", new List<Cmd>(new Cmd[] { yieldCallCmd, new AssumeCmd(Token.NoToken, Expr.False) }), new ReturnCmd(Token.NoToken));
            List<Block> newBlocks = new List<Block>();
            foreach (Block b in impl.Blocks)
            {
                TransferCmd transferCmd = b.TransferCmd;
                List<Cmd> newCmds = new List<Cmd>();
                for (int i = b.Cmds.Count-1; i >= 0; i--)
                {
                    CallCmd callCmd = b.Cmds[i] as CallCmd;
                    if (callCmd == null || callCmd.Proc != yieldProc)
                    {
                        newCmds.Insert(0, b.Cmds[i]);
                    }
                    else
                    {
                        Block newBlock = new Block(Token.NoToken, b.Label + i, newCmds, transferCmd);
                        newCmds = new List<Cmd>();
                        transferCmd = new GotoCmd(Token.NoToken, new List<string>(new string[] { newBlock.Label, yieldCheckBlock.Label }), 
                                                                 new List<Block>(new Block[] { newBlock, yieldCheckBlock }));
                        newBlocks.Add(newBlock);
                    }
                }
                b.Cmds = newCmds;
                b.TransferCmd = transferCmd;
            }
            impl.Blocks.AddRange(newBlocks);
            impl.Blocks.Add(yieldCheckBlock);
        }

        private List<List<Cmd>> CollectAndDesugarYields(Implementation impl,
            Dictionary<string, Variable> domainNameToInputVar, Dictionary<string, Variable> domainNameToLocalVar, Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            // Collect the yield predicates and desugar yields
            List<List<Cmd>> yields = new List<List<Cmd>>();
            List<Cmd> cmds = new List<Cmd>();
            foreach (Block b in impl.Blocks)
            {
                YieldCmd yieldCmd = null;
                List<Cmd> newCmds = new List<Cmd>();
                for (int i = 0; i < b.Cmds.Count; i++)
                {
                    Cmd cmd = b.Cmds[i];
                    if (cmd is YieldCmd)
                    {
                        yieldCmd = (YieldCmd)cmd;
                        continue;
                    }
                    if (yieldCmd != null)
                    {
                        PredicateCmd pcmd = cmd as PredicateCmd;
                        if (pcmd == null)
                        {
                            DesugarYield(yieldCmd, cmds, newCmds, ogOldGlobalMap, domainNameToInputVar, domainNameToLocalVar);
                            if (cmds.Count > 0)
                            {
                                yields.Add(cmds);
                                cmds = new List<Cmd>();
                            }
                            yieldCmd = null;
                        }
                        else
                        {
                            cmds.Add(pcmd);
                        }
                    }

                    if (cmd is CallCmd)
                    {
                        CallCmd callCmd = cmd as CallCmd;
                        if (yieldingProcs.Contains(callCmd.Proc))
                        {
                            AddCallToYieldProc(callCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                        }
                        if (callCmd.IsAsync)
                        {
                            if (!asyncAndParallelCallDesugarings.ContainsKey(callCmd.Proc.Name))
                            {
                                asyncAndParallelCallDesugarings[callCmd.Proc.Name] = new Procedure(Token.NoToken, string.Format("DummyAsyncTarget_{0}", callCmd.Proc.Name), callCmd.Proc.TypeParameters, callCmd.Proc.InParams, callCmd.Proc.OutParams, callCmd.Proc.Requires, new List<IdentifierExpr>(), new List<Ensures>());
                            }
                            var dummyAsyncTargetProc = asyncAndParallelCallDesugarings[callCmd.Proc.Name];
                            CallCmd dummyCallCmd = new CallCmd(callCmd.tok, dummyAsyncTargetProc.Name, callCmd.Ins, callCmd.Outs, callCmd.Attributes);
                            dummyCallCmd.Proc = dummyAsyncTargetProc;
                            newCmds.Add(dummyCallCmd);
                        }
                        else
                        {
                            newCmds.Add(callCmd);
                        }
                        if (yieldingProcs.Contains(callCmd.Proc))
                        {
                            HashSet<Variable> availableLinearVars = new HashSet<Variable>(AvailableLinearVars(callCmd));
                            linearTypeChecker.AddAvailableVars(callCmd, availableLinearVars);

                            if (!callCmd.IsAsync && globalMods.Count > 0 && pc != null)
                            {
                                // assume pc || alpha(i, g);
                                Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
                                assumeExpr.Type = Type.Bool;
                                newCmds.Add(new AssumeCmd(Token.NoToken, assumeExpr));
                            }

                            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(availableLinearVars, domainNameToInputVar);
                            AddUpdatesToOldGlobalVars(newCmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);
                        }
                    }
                    else if (cmd is ParCallCmd)
                    {
                        ParCallCmd parCallCmd = cmd as ParCallCmd;
                        AddCallToYieldProc(parCallCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                        DesugarParallelCallCmd(newCmds, parCallCmd);
                        HashSet<Variable> availableLinearVars = new HashSet<Variable>(AvailableLinearVars(parCallCmd));
                        linearTypeChecker.AddAvailableVars(parCallCmd, availableLinearVars);

                        if (globalMods.Count > 0 && pc != null)
                        {
                            // assume pc || alpha(i, g);
                            Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
                            assumeExpr.Type = Type.Bool;
                            newCmds.Add(new AssumeCmd(Token.NoToken, assumeExpr));
                        }

                        Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(availableLinearVars, domainNameToInputVar);
                        AddUpdatesToOldGlobalVars(newCmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);
                    }
                    else
                    {
                        newCmds.Add(cmd);
                    }
                }
                if (yieldCmd != null)
                {
                    DesugarYield(yieldCmd, cmds, newCmds, ogOldGlobalMap, domainNameToInputVar, domainNameToLocalVar);
                    if (cmds.Count > 0)
                    {
                        yields.Add(cmds);
                        cmds = new List<Cmd>();
                    }
                }
                if (b.TransferCmd is ReturnCmd)
                {
                    AddCallToYieldProc(b.TransferCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                    if (pc != null)
                    {
                        AssertCmd assertCmd = new AssertCmd(b.TransferCmd.tok, Expr.Ident(ok));
                        assertCmd.ErrorData = "Failed to execute atomic action before procedure return";
                        newCmds.Add(assertCmd);
                    }
                }
                b.Cmds = newCmds;
            }
            return yields;
        }

        private void ProcessLoopHeaders(Implementation impl, Graph<Block> graph, HashSet<Block> yieldingHeaders, 
            Dictionary<string, Variable> domainNameToInputVar, Dictionary<string, Variable> domainNameToLocalVar, Dictionary<Variable, Variable> ogOldGlobalMap,
            out List<Variable> oldPcs, out List<Variable> oldOks)
        {
            oldPcs = new List<Variable>();
            oldOks = new List<Variable>();
            foreach (Block header in yieldingHeaders)
            {
                LocalVariable oldPc = null;
                LocalVariable oldOk = null;
                if (pc != null)
                {
                    oldPc = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("{0}_{1}", pc.Name, header.Label), Type.Bool));
                    oldPcs.Add(oldPc);
                    oldOk = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("{0}_{1}", ok.Name, header.Label), Type.Bool));
                    oldOks.Add(oldOk);
                }
                Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(AvailableLinearVars(header), domainNameToInputVar);
                foreach (Block pred in header.Predecessors)
                {
                    AddCallToYieldProc(header.tok, pred.Cmds, ogOldGlobalMap, domainNameToLocalVar);
                    if (pc != null && !graph.BackEdgeNodes(header).Contains(pred))
                    {
                        pred.Cmds.Add(new AssignCmd(Token.NoToken, new List<AssignLhs>(
                            new AssignLhs[] { new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldPc)), new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldOk)) }),
                            new List<Expr>(new Expr[] { Expr.Ident(pc), Expr.Ident(ok) })));
                    }
                    AddUpdatesToOldGlobalVars(pred.Cmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);
                }
                List<Cmd> newCmds = new List<Cmd>();
                if (pc != null)
                {
                    AssertCmd assertCmd;
                    assertCmd = new AssertCmd(header.tok, Expr.Eq(Expr.Ident(oldPc), Expr.Ident(pc)));
                    assertCmd.ErrorData = "Specification state must not change for transitions ending in loop headers";
                    newCmds.Add(assertCmd);
                    assertCmd = new AssertCmd(header.tok, Expr.Imp(Expr.Ident(oldOk), Expr.Ident(ok)));
                    assertCmd.ErrorData = "Specification state must not change for transitions ending in loop headers";
                    newCmds.Add(assertCmd);
                }
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Eq(Expr.Ident(domainNameToLocalVar[domainName]), domainNameToExpr[domainName])));
                }
                foreach (Variable v in ogOldGlobalMap.Keys)
                {
                    newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Eq(Expr.Ident(v), Expr.Ident(ogOldGlobalMap[v]))));
                }
                newCmds.AddRange(header.Cmds);
                header.Cmds = newCmds;
            }
        }

        private void AddInitialBlock(Implementation impl, List<Variable> oldPcs, List<Variable> oldOks,
            Dictionary<string, Variable> domainNameToInputVar, Dictionary<string, Variable> domainNameToLocalVar, Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            // Add initial block
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            if (pc != null)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)));
                rhss.Add(Expr.False);
                foreach (Variable oldPc in oldPcs)
                {
                    lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldPc)));
                    rhss.Add(Expr.False);
                }
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok)));
                rhss.Add(Expr.False);
                foreach (Variable oldOk in oldOks)
                {
                    lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldOk)));
                    rhss.Add(Expr.False);
                }
            }
            Dictionary<string, Expr> domainNameToExpr = new Dictionary<string, Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                domainNameToExpr[domainName] = Expr.Ident(domainNameToInputVar[domainName]);
            }
            for (int i = 0; i < impl.InParams.Count - linearTypeChecker.linearDomains.Count; i++)
            {
                Variable v = impl.InParams[i];
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
                if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                var domain = linearTypeChecker.linearDomains[domainName];
                if (!domain.collectors.ContainsKey(v.TypedIdent.Type)) continue;
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]), new List<Expr> { Expr.Ident(v) });
                domainNameToExpr[domainName] = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new List<Expr> { ie, domainNameToExpr[domainName] });
            }
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
            if (lhss.Count > 0)
            {
                Block initBlock = new Block(Token.NoToken, "og_init", new List<Cmd> { new AssignCmd(Token.NoToken, lhss, rhss) }, new GotoCmd(Token.NoToken, new List<String> { impl.Blocks[0].Label }, new List<Block> { impl.Blocks[0] }));
                impl.Blocks.Insert(0, initBlock);
            }
        }

        private void AddYieldProcAndImpl(List<Declaration> decls) 
        {
            if (yieldProc == null) return;

            Program program = linearTypeChecker.program;
            List<Variable> inputs = new List<Variable>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                var domain = linearTypeChecker.linearDomains[domainName];
                Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "linear_" + domainName + "_in", new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { domain.elementType }, Type.Bool)), true);
                inputs.Add(f);
            }
            foreach (IdentifierExpr ie in globalMods)
            {
                Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", ie.Decl.Name), ie.Decl.TypedIdent.Type), true);
                inputs.Add(f);
            } 
            List<Block> blocks = new List<Block>();
            TransferCmd transferCmd = new ReturnCmd(Token.NoToken);
            if (yieldCheckerProcs.Count > 0)
            {
                List<Block> blockTargets = new List<Block>();
                List<String> labelTargets = new List<String>();
                int labelCount = 0;
                foreach (Procedure proc in yieldCheckerProcs)
                {
                    List<Expr> exprSeq = new List<Expr>();
                    foreach (Variable v in inputs)
                    {
                        exprSeq.Add(Expr.Ident(v));
                    }
                    CallCmd callCmd = new CallCmd(Token.NoToken, proc.Name, exprSeq, new List<IdentifierExpr>());
                    callCmd.Proc = proc;
                    string label = string.Format("L_{0}", labelCount++);
                    Block block = new Block(Token.NoToken, label, new List<Cmd> { callCmd }, new ReturnCmd(Token.NoToken));
                    labelTargets.Add(label);
                    blockTargets.Add(block);
                    blocks.Add(block);
                }
                transferCmd = new GotoCmd(Token.NoToken, labelTargets, blockTargets);
            }
            blocks.Insert(0, new Block(Token.NoToken, "enter", new List<Cmd>(), transferCmd));
            
            var yieldImpl = new Implementation(Token.NoToken, yieldProc.Name, new List<TypeVariable>(), inputs, new List<Variable>(), new List<Variable>(), blocks);
            yieldImpl.Proc = yieldProc;
            yieldImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            decls.Add(yieldProc);
            decls.Add(yieldImpl);
        }

        public static QKeyValue RemoveYieldsAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveYieldsAttribute(iter.Next);
            return (iter.Key == "yields") ? iter.Next : iter;
        }

        public static QKeyValue RemoveMoverAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveMoverAttribute(iter.Next);
            if (iter.Key == "atomic" || iter.Key == "right" || iter.Key == "left" || iter.Key == "both") 
                return iter.Next;
            else 
                return iter;
        }

        private List<Declaration> Collect()
        {
            List<Declaration> decls = new List<Declaration>();
            foreach (Procedure proc in yieldCheckerProcs)
            {
                decls.Add(proc);
            }
            foreach (Implementation impl in yieldCheckerImpls)
            {
                decls.Add(impl);
            }
            foreach (Procedure proc in asyncAndParallelCallDesugarings.Values)
            {
                decls.Add(proc);
            }
            AddYieldProcAndImpl(decls);
            return decls;
        }

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            Program program = linearTypeChecker.program;
            foreach (int layerNum in civlTypeChecker.AllLayerNums)
            {
                if (CommandLineOptions.Clo.TrustLayersDownto <= layerNum || layerNum <= CommandLineOptions.Clo.TrustLayersUpto) continue;

                MyDuplicator duplicator = new MyDuplicator(civlTypeChecker, layerNum);
                foreach (var proc in program.Procedures)
                {
                    if (!civlTypeChecker.procToActionInfo.ContainsKey(proc)) continue;
                    Procedure duplicateProc = duplicator.VisitProcedure(proc);
                    decls.Add(duplicateProc);
                }
                decls.AddRange(duplicator.impls);
                CivlRefinement civlTransform = new CivlRefinement(linearTypeChecker, civlTypeChecker, duplicator);
                foreach (var impl in program.Implementations)
                {
                    if (!civlTypeChecker.procToActionInfo.ContainsKey(impl.Proc) || civlTypeChecker.procToActionInfo[impl.Proc].createdAtLayerNum < layerNum)
                        continue;
                    Implementation duplicateImpl = duplicator.VisitImplementation(impl);
                    civlTransform.TransformImpl(duplicateImpl);
                    decls.Add(duplicateImpl);
                }
                decls.AddRange(civlTransform.Collect());
            }
        }
    }
}
