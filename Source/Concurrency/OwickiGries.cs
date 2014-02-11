using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
    public class MyDuplicator : Duplicator
    {
        MoverTypeChecker moverTypeChecker;
        public int phaseNum;
        int enclosingProcPhaseNum;
        public Dictionary<Procedure, Procedure> procMap; /* Original -> Duplicate */
        public Dictionary<Absy, Absy> absyMap; /* Duplicate -> Original */
        public Dictionary<Block, Block> blockMap; /* Original -> Duplicate */
        public MyDuplicator(MoverTypeChecker moverTypeChecker, int phaseNum)
        {
            this.moverTypeChecker = moverTypeChecker;
            this.phaseNum = phaseNum;
            this.enclosingProcPhaseNum = int.MaxValue;
            this.procMap = new Dictionary<Procedure, Procedure>();
            this.absyMap = new Dictionary<Absy, Absy>();
            this.blockMap = new Dictionary<Block, Block>();
        }

        private void ProcessCallCmd(CallCmd originalCallCmd, CallCmd callCmd, List<Cmd> newCmds)
        {
            Procedure originalProc = originalCallCmd.Proc;
            if (phaseNum == enclosingProcPhaseNum && moverTypeChecker.procToActionInfo.ContainsKey(originalProc))
            {
                ActionInfo actionInfo = moverTypeChecker.procToActionInfo[originalProc];
                List<AssertCmd> gate = actionInfo.thisGate;
                if (actionInfo.phaseNum < phaseNum && gate.Count > 0)
                {
                    newCmds.Add(new HavocCmd(Token.NoToken, new List<IdentifierExpr>(new IdentifierExpr[] { Expr.Ident(dummyLocalVar) } )));
                    Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                    for (int i = 0; i < originalProc.InParams.Count; i++)
                    {
                        map[originalProc.InParams[i]] = callCmd.Ins[i];
                    }
                    Substitution subst = Substituter.SubstitutionFromHashtable(map);
                    foreach (AssertCmd assertCmd in gate)
                    {
                        newCmds.Add(Substituter.Apply(subst, assertCmd));
                    }
                }
            }
            newCmds.Add(callCmd);
        }

        private void ProcessParCallCmd(ParCallCmd originalParCallCmd, ParCallCmd parCallCmd, List<Cmd> newCmds)
        {
            int maxCalleePhaseNum = 0;
            foreach (CallCmd iter in originalParCallCmd.CallCmds)
            {
                int calleePhaseNum = moverTypeChecker.FindPhaseNumber(iter.Proc);
                if (calleePhaseNum > maxCalleePhaseNum)
                    maxCalleePhaseNum = calleePhaseNum;
            }
            if (phaseNum > maxCalleePhaseNum)
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
            blockMap[node] = block;
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
            if (!QKeyValue.FindBoolAttribute(node.Attributes, "yields"))
                return node;
            if (!procMap.ContainsKey(node))
            {
                Procedure proc = (Procedure)node.Clone();
                proc.Name = string.Format("{0}_{1}", node.Name, phaseNum);
                proc.InParams = this.VisitVariableSeq(node.InParams);
                proc.Modifies = this.VisitIdentifierExprSeq(node.Modifies);
                proc.OutParams = this.VisitVariableSeq(node.OutParams);
                if (moverTypeChecker.procToActionInfo.ContainsKey(node) && moverTypeChecker.procToActionInfo[node].phaseNum < phaseNum)
                {
                    proc.Requires = new List<Requires>();
                    proc.Ensures = new List<Ensures>();
                }
                else
                {
                    proc.Requires = this.VisitRequiresSeq(node.Requires);
                    proc.Ensures = this.VisitEnsuresSeq(node.Ensures);
                }
                procMap[node] = proc;
            }
            return procMap[node];
        }

        private Variable dummyLocalVar;
        public override Implementation VisitImplementation(Implementation node)
        {
            enclosingProcPhaseNum = moverTypeChecker.FindPhaseNumber(node.Proc);
            if (enclosingProcPhaseNum == int.MaxValue)
            {
                enclosingProcPhaseNum = moverTypeChecker.allPhaseNums.Max();
            }
            dummyLocalVar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_dummy", Type.Bool));
            Implementation impl = base.VisitImplementation(node);
            impl.LocVars.Add(dummyLocalVar);
            impl.Name = impl.Proc.Name;
            foreach (Block block in impl.Blocks)
            {
                GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                if (gotoCmd == null) continue;
                List<Block> labelTargets = new List<Block>();
                List<string> labelNames = new List<string>();
                foreach (Block x in gotoCmd.labelTargets)
                {
                    Block y = (Block)blockMap[x];
                    labelTargets.Add(y);
                    labelNames.Add(y.Label);
                }
                gotoCmd.labelTargets = labelTargets;
                gotoCmd.labelNames = labelNames;
            }
            return impl;
        }

        public override Requires VisitRequires(Requires node)
        {
            Requires requires = base.VisitRequires(node);
            if (node.Free)
                return requires;
            if (!OwickiGries.FindPhaseNums(requires.Attributes).Contains(phaseNum))
                requires.Condition = Expr.True;
            return requires;
        }

        public override Ensures VisitEnsures(Ensures node)
        {
            Ensures ensures = base.VisitEnsures(node);
            if (node.Free)
                return ensures;
            if (ensures.IsAtomicSpecification || !OwickiGries.FindPhaseNums(ensures.Attributes).Contains(phaseNum))
            {
                ensures.Condition = Expr.True;
                ensures.Attributes = OwickiGries.RemoveMoverAttribute(ensures.Attributes);
            }
            return ensures;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            AssertCmd assertCmd = (AssertCmd) base.VisitAssertCmd(node);
            if (!OwickiGries.FindPhaseNums(assertCmd.Attributes).Contains(phaseNum))
                assertCmd.Expr = Expr.True;
            return assertCmd;
        }
    }

    public class OwickiGries
    {
        LinearTypeChecker linearTypeChecker;
        MoverTypeChecker moverTypeChecker;
        Dictionary<Absy, Absy> absyMap;
        Dictionary<Procedure, Procedure> reverseProcMap;
        int phaseNum;
        List<Declaration> decls;
        List<IdentifierExpr> globalMods;
        Dictionary<string, Procedure> asyncAndParallelCallDesugarings;
        List<Procedure> yieldCheckerProcs;
        List<Implementation> yieldCheckerImpls;
        Procedure yieldProc;

        public OwickiGries(LinearTypeChecker linearTypeChecker, MoverTypeChecker moverTypeChecker, MyDuplicator duplicator, List<Declaration> decls)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.moverTypeChecker = moverTypeChecker;
            this.absyMap = duplicator.absyMap;
            this.phaseNum = duplicator.phaseNum;
            this.reverseProcMap = new Dictionary<Procedure, Procedure>();
            foreach (Procedure proc in duplicator.procMap.Keys)
            {
                this.reverseProcMap[duplicator.procMap[proc]] = proc;
            }
            this.decls = decls;
            Program program = linearTypeChecker.program;
            globalMods = new List<IdentifierExpr>();
            foreach (Variable g in program.GlobalVariables())
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
            return linearTypeChecker.AvailableLinearVars(absyMap[absy]);
        }

        private void AddCallToYieldProc(IToken tok, List<Cmd> newCmds, Dictionary<Variable, Variable> ogOldGlobalMap, Dictionary<string, Variable> domainNameToLocalVar)
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
                yieldProc = new Procedure(Token.NoToken, string.Format("og_yield_{0}", phaseNum), new List<TypeVariable>(), inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
                yieldProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            }
            CallCmd yieldCallCmd = new CallCmd(Token.NoToken, yieldProc.Name, exprSeq, new List<IdentifierExpr>());
            yieldCallCmd.Proc = yieldProc;
            newCmds.Add(yieldCallCmd);

            if (pc != null)
            {
                Expr bb = OldEqualityExpr(ogOldGlobalMap);

                // assert (o_old == o && g_old == g) || beta(i, g_old, o, g);
                AssertCmd skipOrBetaAssertCmd = new AssertCmd(tok, Expr.Or(bb, beta));
                skipOrBetaAssertCmd.ErrorData = "Transition invariant in initial state violated";
                newCmds.Add(skipOrBetaAssertCmd);

                // assert pc ==> o_old == o && g_old == g;
                AssertCmd skipAssertCmd = new AssertCmd(tok, Expr.Imp(Expr.Ident(pc), bb));
                skipAssertCmd.ErrorData = "Transition invariant in final state violated"; ;
                newCmds.Add(skipAssertCmd);

                // pc, ok := ite(o_old == o && g_old == g, pc, true), ok || beta(i, g_old, o, g);
                List<Expr> iteArgs = new List<Expr>(new Expr[] { bb, Expr.Ident(pc), Expr.True });
                List<AssignLhs> pcUpdateLHS = new List<AssignLhs>(
                    new AssignLhs[] { 
                        new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)), 
                        new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok))
                    });
                List<Expr> pcUpdateRHS = new List<Expr>(
                    new Expr[] { 
                        new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), iteArgs),
                        Expr.Or(Expr.Ident(ok), beta)
                    });
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

        Variable pc;
        Variable ok;
        Expr alpha;
        Expr beta;

        private Expr OldEqualityExpr(Dictionary<Variable, Variable> ogOldGlobalMap)
        {
            Expr bb = Expr.True;
            foreach (Variable o in ogOldGlobalMap.Keys)
            {
                bb = Expr.Binary(BinaryOperator.Opcode.And, bb, Expr.Eq(Expr.Ident(o), Expr.Ident(ogOldGlobalMap[o])));
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
                    newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Or(Expr.Ident(pc), alpha)));
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
            foreach (CallCmd callCmd in parCallCmd.CallCmds)
            {
                parallelCalleeNames.Add(callCmd.Proc.Name);
                ins.AddRange(callCmd.Ins);
                outs.AddRange(callCmd.Outs);
            }
            parallelCalleeNames.Sort();
            string procName = "og";
            foreach (string calleeName in parallelCalleeNames)
            {
                procName = procName + "_" + calleeName;
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
                        requiresSeq.Add(new Requires(req.Free, Substituter.Apply(subst, req.Condition)));
                    }
                    foreach (Ensures ens in callCmd.Proc.Ensures)
                    {
                        ensuresSeq.Add(new Ensures(ens.Free, Substituter.Apply(subst, ens.Condition)));
                    }
                    count++;
                }
                proc = new Procedure(Token.NoToken, procName, new List<TypeVariable>(), inParams, outParams, requiresSeq, new List<IdentifierExpr>(), ensuresSeq);
                proc.AddAttribute("yields");
                asyncAndParallelCallDesugarings[procName] = proc;
            }
            CallCmd dummyCallCmd = new CallCmd(Token.NoToken, proc.Name, ins, outs);
            dummyCallCmd.Proc = proc;
            newCmds.Add(dummyCallCmd);
        }

        private void CreateYieldCheckerImplForOldStableEnsures(Procedure proc)
        {
            Program program = linearTypeChecker.program;
            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> oldGlobalMap = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> identityGlobalMap = new Dictionary<Variable, Expr>();
            List<Variable> locals = new List<Variable>();
            List<Variable> inputs = new List<Variable>();
            for (int i = 0; i < proc.InParams.Count - linearTypeChecker.linearDomains.Count; i++)
            {
                Variable inParam = proc.InParams[i];
                Variable copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name, inParam.TypedIdent.Type));
                locals.Add(copy);
                map[proc.InParams[i]] = Expr.Ident(copy);
            }
            {
                int i = proc.InParams.Count - linearTypeChecker.linearDomains.Count;
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable inParam = proc.InParams[i];
                    Variable copy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name, inParam.TypedIdent.Type), true);
                    inputs.Add(copy);
                    map[proc.InParams[i]] = Expr.Ident(copy);
                    i++;
                }
            }
            Dictionary<Variable, Expr> requiresMap = new Dictionary<Variable, Expr>(map);
            for (int i = 0; i < proc.OutParams.Count; i++)
            {
                Variable outParam = proc.OutParams[i];
                var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, outParam.Name, outParam.TypedIdent.Type));
                locals.Add(copy);
                map[proc.OutParams[i]] = Expr.Ident(copy);
            }
            foreach (IdentifierExpr ie in globalMods)
            {
                Variable g = ie.Decl;
                identityGlobalMap[g] = Expr.Ident(g);
                var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_local_post_{0}", g.Name), g.TypedIdent.Type));
                locals.Add(copy);
                map[g] = Expr.Ident(copy);
                Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", g.Name), g.TypedIdent.Type), true);
                inputs.Add(f);
                oldGlobalMap[g] = Expr.Ident(f);
                requiresMap[g] = Expr.Ident(f);
            }
            
            Substitution requiresSubst = Substituter.SubstitutionFromHashtable(requiresMap);
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            Substitution identityGlobalSubst = Substituter.SubstitutionFromHashtable(identityGlobalMap);
            Substitution oldGlobalSubst = Substituter.SubstitutionFromHashtable(oldGlobalMap);
            List<Block> yieldCheckerBlocks = new List<Block>();
            List<String> labels = new List<String>();
            List<Block> labelTargets = new List<Block>();
            Block yieldCheckerBlock = new Block(Token.NoToken, "exit", new List<Cmd>(), new ReturnCmd(Token.NoToken));
            labels.Add(yieldCheckerBlock.Label);
            labelTargets.Add(yieldCheckerBlock);
            yieldCheckerBlocks.Add(yieldCheckerBlock);
            List<Cmd> newCmds = new List<Cmd>();
            foreach (Requires requires in proc.Requires)
            {
                AssumeCmd assumeCmd = new AssumeCmd(Token.NoToken, Substituter.Apply(requiresSubst, requires.Condition));
                newCmds.Add(assumeCmd);
            }
            foreach (Ensures ensures in proc.Ensures)
            {
                AssumeCmd assumeCmd = new AssumeCmd(Token.NoToken, Substituter.ApplyReplacingOldExprs(subst, identityGlobalSubst, ensures.Condition)); ;
                newCmds.Add(assumeCmd);
            }
            foreach (Ensures ensures in proc.Ensures)
            {
                var newExpr = Substituter.ApplyReplacingOldExprs(subst, oldGlobalSubst, ensures.Condition);
                if (ensures.Free)
                {
                    newCmds.Add(new AssumeCmd(Token.NoToken, newExpr));
                }
                else
                {
                    AssertCmd assertCmd = new AssertCmd(ensures.tok, newExpr);
                    assertCmd.ErrorData = "Backwards non-interference check failed";
                    newCmds.Add(assertCmd);
                }
            }
            newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
            yieldCheckerBlock = new Block(Token.NoToken, "L", newCmds, new ReturnCmd(Token.NoToken));
            labels.Add(yieldCheckerBlock.Label);
            labelTargets.Add(yieldCheckerBlock);
            yieldCheckerBlocks.Add(yieldCheckerBlock);
            yieldCheckerBlocks.Insert(0, new Block(Token.NoToken, "enter", new List<Cmd>(), new GotoCmd(Token.NoToken, labels, labelTargets)));

            // Create the yield checker procedure
            var yieldCheckerName = string.Format("Proc_OldStableEnsuresChecker_{0}", proc.Name);
            var yieldCheckerProc = new Procedure(Token.NoToken, yieldCheckerName, proc.TypeParameters, inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            yieldCheckerProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            yieldCheckerProcs.Add(yieldCheckerProc);

            // Create the yield checker implementation
            var yieldCheckerImpl = new Implementation(Token.NoToken, yieldCheckerName, proc.TypeParameters, inputs, new List<Variable>(), locals, yieldCheckerBlocks);
            yieldCheckerImpl.Proc = yieldCheckerProc;
            yieldCheckerImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            yieldCheckerImpls.Add(yieldCheckerImpl);
        }

        private void CreateYieldCheckerImpl(DeclWithFormals decl, List<List<Cmd>> yields, Dictionary<Variable, Expr> map)
        {
            if (yields.Count == 0) return;

            Program program = linearTypeChecker.program;
            List<Variable> locals = new List<Variable>();
            List<Variable> inputs = new List<Variable>();
            foreach (IdentifierExpr ie in map.Values)
            {
                locals.Add(ie.Decl);
            }
            for (int i = 0; i < decl.InParams.Count - linearTypeChecker.linearDomains.Count; i++)
            {
                Variable inParam = decl.InParams[i];
                Variable copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name, inParam.TypedIdent.Type));
                locals.Add(copy);
                map[decl.InParams[i]] = Expr.Ident(copy);
            }
            {
                int i = decl.InParams.Count - linearTypeChecker.linearDomains.Count;
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable inParam = decl.InParams[i];
                    Variable copy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name, inParam.TypedIdent.Type), true);
                    inputs.Add(copy);
                    map[decl.InParams[i]] = Expr.Ident(copy);
                    i++;
                }
            }
            for (int i = 0; i < decl.OutParams.Count; i++)
            {
                Variable outParam = decl.OutParams[i];
                var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, outParam.Name, outParam.TypedIdent.Type));
                locals.Add(copy);
                map[decl.OutParams[i]] = Expr.Ident(copy);
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
            var yieldCheckerName = string.Format("{0}_YieldChecker_{1}", decl is Procedure ? "Proc" : "Impl", decl.Name);
            var yieldCheckerProc = new Procedure(Token.NoToken, yieldCheckerName, decl.TypeParameters, inputs, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            yieldCheckerProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            yieldCheckerProcs.Add(yieldCheckerProc);

            // Create the yield checker implementation
            var yieldCheckerImpl = new Implementation(Token.NoToken, yieldCheckerName, decl.TypeParameters, inputs, new List<Variable>(), locals, yieldCheckerBlocks);
            yieldCheckerImpl.Proc = yieldCheckerProc;
            yieldCheckerImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            yieldCheckerImpls.Add(yieldCheckerImpl);
        }

        private bool IsYieldingHeader(GraphUtil.Graph<Block> graph, Block header)
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
                        if (callCmd.IsAsync || QKeyValue.FindBoolAttribute(callCmd.Proc.Attributes, "yields"))
                            return true;
                    }
                }
            }
            return false;
        }

        private void TransformImpl(Implementation impl)
        {
            if (!QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "yields")) return;

            // Find the yielding loop headers
            impl.PruneUnreachableBlocks();
            impl.ComputePredecessorsForBlocks();
            GraphUtil.Graph<Block> graph = Program.GraphFromImpl(impl);
            graph.ComputeLoops();
            if (!graph.Reducible)
            {
                throw new Exception("Irreducible flow graphs are unsupported.");
            }
            HashSet<Block> yieldingHeaders = new HashSet<Block>();
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

            Program program = linearTypeChecker.program;
            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            foreach (Variable local in impl.LocVars)
            {
                var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, local.Name, local.TypedIdent.Type));
                map[local] = Expr.Ident(copy);
            }
            Dictionary<Variable, Variable> ogOldGlobalMap = new Dictionary<Variable, Variable>();
            foreach (IdentifierExpr ie in globalMods)
            {
                Variable g = ie.Decl;
                LocalVariable l = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_global_old_{0}", g.Name), g.TypedIdent.Type));
                ogOldGlobalMap[g] = l;
                impl.LocVars.Add(l);
            }

            Procedure originalProc = reverseProcMap[impl.Proc];
            if (moverTypeChecker.procToActionInfo.ContainsKey(originalProc))
            {
                ActionInfo actionInfo = moverTypeChecker.procToActionInfo[originalProc];
                if (actionInfo.phaseNum == this.phaseNum)
                {
                    pc = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_pc", Type.Bool));
                    impl.LocVars.Add(pc);
                    ok = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_ok", Type.Bool));
                    impl.LocVars.Add(ok);
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
                    Expr betaExpr = (new MoverCheck.TransitionRelationComputation(moverTypeChecker.program, actionInfo)).TransitionRelationCompute();
                    beta = Substituter.ApplyReplacingOldExprs(always, forold, betaExpr);
                    Expr alphaExpr = Expr.True;
                    foreach (AssertCmd assertCmd in actionInfo.thisGate)
                    {
                        alphaExpr = Expr.And(alphaExpr, assertCmd.Expr);
                    }
                    alpha = Substituter.Apply(always, alphaExpr);
                    foreach (Variable f in impl.OutParams)
                    {
                        LocalVariable copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og_old_{0}", f.Name), f.TypedIdent.Type));
                        impl.LocVars.Add(copy);
                        ogOldGlobalMap[f] = copy;
                    }
                }
            }

            Dictionary<string, Variable> domainNameToInputVar = new Dictionary<string, Variable>();
            Dictionary<string, Variable> domainNameToLocalVar = new Dictionary<string, Variable>();
            {
                int i = impl.InParams.Count - linearTypeChecker.linearDomains.Count;
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable inParam = impl.InParams[i];
                    domainNameToInputVar[domainName] = inParam;
                    Variable l = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name + "_local", inParam.TypedIdent.Type));
                    domainNameToLocalVar[domainName] = l;
                    impl.LocVars.Add(l);
                    i++;
                }
            }

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
                        if (callCmd.IsAsync || QKeyValue.FindBoolAttribute(callCmd.Proc.Attributes, "yields"))
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
                            CallCmd dummyCallCmd = new CallCmd(Token.NoToken, dummyAsyncTargetProc.Name, callCmd.Ins, callCmd.Outs);
                            dummyCallCmd.Proc = dummyAsyncTargetProc;
                            newCmds.Add(dummyCallCmd);
                        }
                        else
                        {
                            newCmds.Add(callCmd);
                        }
                        if (callCmd.IsAsync || QKeyValue.FindBoolAttribute(callCmd.Proc.Attributes, "yields"))
                        {
                            HashSet<Variable> availableLinearVars = new HashSet<Variable>(AvailableLinearVars(callCmd));
                            linearTypeChecker.AddAvailableVars(callCmd, availableLinearVars);
                            Dictionary<string, Expr> domainNameToExpr = ComputeAvailableExprs(availableLinearVars, domainNameToInputVar);
                            AddUpdatesToOldGlobalVars(newCmds, ogOldGlobalMap, domainNameToLocalVar, domainNameToExpr);
                        }
                    }
                    else if (cmd is ParCallCmd)
                    {
                        ParCallCmd parCallCmd = cmd as ParCallCmd;
                        AddCallToYieldProc(parCallCmd.tok, newCmds, ogOldGlobalMap, domainNameToLocalVar);
                        DesugarParallelCallCmd(newCmds, parCallCmd);
                        if (globalMods.Count > 0 && pc != null)
                        {
                            // assume pc || alpha(i, g);
                            newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Or(Expr.Ident(pc), alpha)));
                        }
                        HashSet<Variable> availableLinearVars = new HashSet<Variable>(AvailableLinearVars(parCallCmd));
                        linearTypeChecker.AddAvailableVars(parCallCmd, availableLinearVars);
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
                if (b.TransferCmd is ReturnCmd && QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "yields"))
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

            List<Variable> oldPcs = new List<Variable>();
            List<Variable> oldOks = new List<Variable>();
            foreach (Block header in yieldingHeaders)
            {
                LocalVariable oldPc = null;
                LocalVariable oldOk = null;
                if (pc != null)
                {
                    oldPc = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("{0}_{1}", pc.Name, header.Label), Type.Bool));
                    oldPcs.Add(oldPc);
                    impl.LocVars.Add(oldPc);
                    oldOk = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("{0}_{1}", ok.Name, header.Label), Type.Bool));
                    oldOks.Add(oldOk);
                    impl.LocVars.Add(oldOk);
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
                    newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Binary(BinaryOperator.Opcode.Eq, Expr.Ident(domainNameToLocalVar[domainName]), domainNameToExpr[domainName])));
                }
                foreach (Variable v in ogOldGlobalMap.Keys)
                {
                    newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Binary(BinaryOperator.Opcode.Eq, Expr.Ident(v), Expr.Ident(ogOldGlobalMap[v]))));
                }
                newCmds.AddRange(header.Cmds);
                header.Cmds = newCmds;
            }

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

            CreateYieldCheckerImpl(impl, yields, map);
        }

        public void TransformProc(Procedure proc)
        {
            if (!QKeyValue.FindBoolAttribute(proc.Attributes, "stable")) return;

            Program program = linearTypeChecker.program;
            Dictionary<string, Variable> domainNameToInputVar = new Dictionary<string, Variable>();
            {
                int i = proc.InParams.Count - linearTypeChecker.linearDomains.Count;
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    Variable inParam = proc.InParams[i];
                    domainNameToInputVar[domainName] = inParam;
                    i++;
                }
            }

            // Collect the yield predicates and desugar yields
            List<List<Cmd>> yields = new List<List<Cmd>>();
            List<Cmd> cmds = new List<Cmd>();
            if (proc.Requires.Count > 0)
            {
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
                for (int i = 0; i < proc.InParams.Count - linearTypeChecker.linearDomains.Count; i++)
                {
                    Variable v = proc.InParams[i];
                    var domainName = linearTypeChecker.FindDomainName(v);
                    if (domainName == null) continue;
                    if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                    domainNameToScope[domainName].Add(v);
                }
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    cmds.Add(new AssumeCmd(Token.NoToken, linearTypeChecker.DisjointnessExpr(domainName, domainNameToInputVar[domainName], domainNameToScope[domainName])));
                }
                foreach (Requires r in proc.Requires)
                {
                    if (r.Free)
                    {
                        cmds.Add(new AssumeCmd(r.tok, r.Condition));
                    }
                    else
                    {
                        AssertCmd assertCmd = new AssertCmd(r.tok, r.Condition, r.Attributes);
                        assertCmd.ErrorData = "Non-interference check failed";
                        cmds.Add(assertCmd);
                    }
                }
                yields.Add(cmds);
                cmds = new List<Cmd>();
            }
            if (proc.Ensures.Count > 0)
            {
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
                for (int i = 0; i < proc.OutParams.Count; i++)
                {
                    Variable v = proc.OutParams[i];
                    var domainName = linearTypeChecker.FindDomainName(v);
                    if (domainName == null) continue;
                    if (!linearTypeChecker.linearDomains.ContainsKey(domainName)) continue;
                    domainNameToScope[domainName].Add(v);
                }
                foreach (string domainName in linearTypeChecker.linearDomains.Keys)
                {
                    cmds.Add(new AssumeCmd(Token.NoToken, linearTypeChecker.DisjointnessExpr(domainName, domainNameToInputVar[domainName], domainNameToScope[domainName])));
                }
                foreach (Ensures e in proc.Ensures)
                {
                    if (e.Free)
                    {
                        cmds.Add(new AssumeCmd(e.tok, e.Condition));
                    }
                    else
                    {
                        AssertCmd assertCmd = new AssertCmd(e.tok, e.Condition, e.Attributes);
                        assertCmd.ErrorData = "Non-interference check failed";
                        cmds.Add(assertCmd);
                    }
                }
                yields.Add(cmds);
                cmds = new List<Cmd>();
            }
            CreateYieldCheckerImpl(proc, yields, new Dictionary<Variable, Expr>());
            CreateYieldCheckerImplForOldStableEnsures(proc);
        }

        private void AddYieldProcAndImpl() 
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

        public static HashSet<int> FindPhaseNums(QKeyValue kv)
        {
            HashSet<int> attrs = QKeyValue.FindIntAttributes(kv, "phase");
            if (attrs.Count == 0)
            {
                attrs.Add(int.MaxValue);
            }
            return attrs;
        }

        public static QKeyValue RemoveYieldsAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveYieldsAttribute(iter.Next);
            return (QKeyValue.FindBoolAttribute(iter, "yields")) ? iter.Next : iter;
        }

        public static QKeyValue RemoveStableAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveStableAttribute(iter.Next);
            return (QKeyValue.FindBoolAttribute(iter, "stable")) ? iter.Next : iter;
        }

        public static QKeyValue RemoveQedAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveQedAttribute(iter.Next);
            return QKeyValue.FindBoolAttribute(iter, "qed") ? iter.Next : iter;
        }

        public static QKeyValue RemoveMoverAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveMoverAttribute(iter.Next);
            if (QKeyValue.FindIntAttribute(iter, "atomic", int.MaxValue) != int.MaxValue ||
                QKeyValue.FindIntAttribute(iter, "right", int.MaxValue) != int.MaxValue ||
                QKeyValue.FindIntAttribute(iter, "left", int.MaxValue) != int.MaxValue ||
                QKeyValue.FindIntAttribute(iter, "both", int.MaxValue) != int.MaxValue) 
                return iter.Next;
            else 
                return iter;
        }

        private void Transform(List<Implementation> impls, List<Procedure> procs)
        {
            foreach (var impl in impls)
            {
                pc = null;
                alpha = null;
                beta = null;
                TransformImpl(impl);
            }
            foreach (var proc in procs)
            {
                TransformProc(proc);
            }
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
            AddYieldProcAndImpl();
        }

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, MoverTypeChecker moverTypeChecker, List<Declaration> decls)
        {
            Program program = linearTypeChecker.program;
            foreach (int phaseNum in moverTypeChecker.allPhaseNums)
            {
                MyDuplicator duplicator = new MyDuplicator(moverTypeChecker, phaseNum);
                List<Implementation> impls = new List<Implementation>();
                List<Procedure> procs = new List<Procedure>();
                foreach (var decl in program.TopLevelDeclarations)
                {
                    Procedure proc = decl as Procedure;
                    if (proc == null || !QKeyValue.FindBoolAttribute(proc.Attributes, "yields")) continue;
                    Procedure duplicateProc = duplicator.VisitProcedure(proc);
                    procs.Add(duplicateProc);
                    if (moverTypeChecker.procToActionInfo.ContainsKey(proc) && moverTypeChecker.procToActionInfo[proc].phaseNum < phaseNum)
                    {
                        duplicateProc.Attributes = null;
                        duplicateProc.Modifies = new List<IdentifierExpr>();
                        program.GlobalVariables().Iter(x => duplicateProc.Modifies.Add(Expr.Ident(x)));
                        CodeExpr action = (CodeExpr)duplicator.VisitCodeExpr(moverTypeChecker.procToActionInfo[proc].thisAction);
                        Implementation impl = new Implementation(Token.NoToken, duplicateProc.Name, proc.TypeParameters, proc.InParams, proc.OutParams, new List<Variable>(), action.Blocks);
                        impl.Proc = duplicateProc;
                        impl.Proc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                        impl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                        impls.Add(impl);
                    }
                }
                foreach (var decl in program.TopLevelDeclarations)
                {
                    Implementation impl = decl as Implementation;
                    if (impl == null || 
                        !QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "yields") ||
                        (moverTypeChecker.procToActionInfo.ContainsKey(impl.Proc) && moverTypeChecker.procToActionInfo[impl.Proc].phaseNum < phaseNum)) 
                        continue;
                    Implementation duplicateImpl = duplicator.VisitImplementation(impl);
                    impls.Add(duplicateImpl);
                }
                OwickiGries ogTransform = new OwickiGries(linearTypeChecker, moverTypeChecker, duplicator, decls);
                ogTransform.Transform(impls, procs);
                foreach (var proc in procs)
                {
                    decls.Add(proc);
                }
                foreach (var impl in impls)
                {
                    decls.Add(impl);
                }
            }
        }
    }
}
