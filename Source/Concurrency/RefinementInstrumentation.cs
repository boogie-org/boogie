using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    interface RefinementInstrumentation
    {
        List<Variable> NewLocalVars { get; }
        List<Cmd> CreateAssumeCmds();
        List<Cmd> CreateFinalAssertCmds();
        List<Cmd> CreateAssertCmds();
        List<Cmd> CreateUpdateCmds();
        List<Cmd> CreateUpdatesToOldOutputVars();
        List<Cmd> CreateInitCmds();
        List<Cmd> CreateYieldingLoopHeaderInitCmds(Block header);
        List<Cmd> CreateYieldingLoopHeaderAssertCmds(Block header);
    }
    
    class NoneRefinementInstrumentation : RefinementInstrumentation
    {
        public List<Variable> NewLocalVars => new List<Variable>();

        public List<Cmd> CreateAssumeCmds()
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateFinalAssertCmds()
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateAssertCmds()
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateUpdateCmds()
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateUpdatesToOldOutputVars()
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateInitCmds()
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateYieldingLoopHeaderInitCmds(Block header)
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateYieldingLoopHeaderAssertCmds(Block header)
        {
            return new List<Cmd>();
        }
    }
    
    class SomeRefinementInstrumentation : RefinementInstrumentation
    {
        private Dictionary<Variable, Variable> oldGlobalMap;
        private Dictionary<Variable, Variable> oldOutputMap;
        private List<Variable> newLocalVars;
        private Variable pc;
        private Variable ok;
        private Expr alpha;
        private Expr beta;
        private Dictionary<Block, Variable> pcsForYieldingLoopsHeaders;
        private Dictionary<Block, Variable> oksForYieldingLoopHeaders;

        private Dictionary<AtomicAction, Expr> transitionRelationCache;

        public SomeRefinementInstrumentation(
            CivlTypeChecker civlTypeChecker,
            Implementation impl,
            Implementation originalImpl,
            Dictionary<Variable, Variable> oldGlobalMap,
            HashSet<Block> yieldingLoopHeaders)
        {
            newLocalVars = new List<Variable>();
            YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[originalImpl.Proc];
            int layerNum = yieldingProc.upperLayer;
            pc = Pc();
            newLocalVars.Add(pc);
            ok = Ok();
            newLocalVars.Add(ok);

            this.transitionRelationCache = new Dictionary<AtomicAction, Expr>();

            this.oldGlobalMap = new Dictionary<Variable, Variable>();
            foreach (Variable v in civlTypeChecker.sharedVariables)
            {
                var layerRange = civlTypeChecker.GlobalVariableLayerRange(v);
                if (layerRange.lowerLayerNum <= yieldingProc.upperLayer && yieldingProc.upperLayer < layerRange.upperLayerNum)
                {
                    this.oldGlobalMap[v] = oldGlobalMap[v];
                }
            }

            oldOutputMap = new Dictionary<Variable, Variable>();
            foreach (Variable f in impl.OutParams)
            {
                LocalVariable copy = Old(f);
                newLocalVars.Add(copy);
                oldOutputMap[f] = copy;
            }

            Dictionary<Variable, Expr> foroldMap = new Dictionary<Variable, Expr>();
            foreach (Variable g in civlTypeChecker.sharedVariables)
            {
                foroldMap[g] = Expr.Ident(oldGlobalMap[g]);
            }
            if (yieldingProc is ActionProc actionProc)
            {
                // The parameters of an atomic action come from the implementation that denotes the atomic action specification.
                // To use the transition relation computed below in the context of the yielding procedure of the refinement check,
                // we need to substitute the parameters.
                AtomicAction atomicAction = actionProc.refinedAction;
                Implementation atomicActionImpl = atomicAction.impl;
                Dictionary<Variable, Expr> alwaysMap = new Dictionary<Variable, Expr>();
                for (int i = 0; i < impl.InParams.Count; i++)
                {
                    alwaysMap[atomicActionImpl.InParams[i]] = Expr.Ident(impl.InParams[i]);
                }

                for (int i = 0; i < impl.OutParams.Count; i++)
                {
                    alwaysMap[atomicActionImpl.OutParams[i]] = Expr.Ident(impl.OutParams[i]);
                }
                if (atomicAction.HasPendingAsyncs)
                {
                    Variable collectedPAs = civlTypeChecker.implToPendingAsyncCollector[originalImpl];
                    alwaysMap[atomicActionImpl.OutParams.Last()] = Expr.Ident(collectedPAs);
                    LocalVariable copy = Old(collectedPAs);
                    newLocalVars.Add(copy);
                    oldOutputMap[collectedPAs] = copy;
                }

                Substitution always = Substituter.SubstitutionFromHashtable(alwaysMap);
                Substitution forold = Substituter.SubstitutionFromHashtable(foroldMap);
                Expr betaExpr = GetTransitionRelation(atomicAction);
                beta = Substituter.ApplyReplacingOldExprs(always, forold, betaExpr);
                Expr alphaExpr = Expr.And(atomicAction.gate.Select(g => g.Expr));
                alphaExpr.Type = Type.Bool;
                alpha = Substituter.Apply(always, alphaExpr);
            }
            else
            {
                beta = OldEqualityExprForGlobals();
                alpha = Expr.True;
            }

            pcsForYieldingLoopsHeaders = new Dictionary<Block, Variable>();
            oksForYieldingLoopHeaders = new Dictionary<Block, Variable>();
            foreach (Block header in yieldingLoopHeaders)
            {
                var pcForYieldingLoopHeader = PcForYieldingLoopHeader(header);
                newLocalVars.Add(pcForYieldingLoopHeader);
                pcsForYieldingLoopsHeaders[header] = pcForYieldingLoopHeader;
                var okForYieldingLoopHeader = OkForYieldingLoopHeader(header);
                newLocalVars.Add(okForYieldingLoopHeader);
                oksForYieldingLoopHeaders[header] = okForYieldingLoopHeader;
            }
        }

        private Expr GetTransitionRelation(AtomicAction atomicAction)
        {
            if (!transitionRelationCache.ContainsKey(atomicAction))
            {
                transitionRelationCache[atomicAction] =
                    TransitionRelationComputation.
                        Refinement(atomicAction, new HashSet<Variable>(this.oldGlobalMap.Keys));
            }
            return transitionRelationCache[atomicAction];
        }

        public List<Variable> NewLocalVars => newLocalVars;

        public List<Cmd> CreateAssumeCmds()
        {
            var cmds = new List<Cmd>();
            // assume pc || alpha(i, g);
            Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
            assumeExpr.Type = Type.Bool;
            cmds.Add(new AssumeCmd(Token.NoToken, assumeExpr));
            return cmds;
        }

        public List<Cmd> CreateFinalAssertCmds()
        {
            var cmds = CreateAssertCmds();
            AssertCmd assertCmd = new AssertCmd(Token.NoToken, Expr.Ident(ok));
            assertCmd.ErrorData = "Failed to execute atomic action before procedure return";
            cmds.Add(assertCmd);
            return cmds;
        }

        public List<Cmd> CreateAssertCmds()
        {
            var cmds = new List<Cmd>();
            cmds.Add(CreateSkipOrBetaAssertCmd());
            cmds.Add(CreateSkipAssertCmd());
            return cmds;
        }

        public List<Cmd> CreateInitCmds()
        {
            var cmds = new List<Cmd>();
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)));
            rhss.Add(Expr.False);
            lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok)));
            rhss.Add(Expr.False);
            cmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            cmds.AddRange(CreateUpdatesToOldOutputVars());
            return cmds;
        }
        
        public List<Cmd> CreateUpdateCmds()
        {
            // pc, ok := g_old == g ==> pc, ok || beta(i, g_old, o, g);
            Expr aa = OldEqualityExprForGlobals();
            List<AssignLhs> pcUpdateLHS = new List<AssignLhs>
            {
                new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)),
                new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok))
            };
            List<Expr> pcUpdateRHS = new List<Expr>(
                new Expr[]
                {
                    Expr.Imp(aa, Expr.Ident(pc)),
                    Expr.Or(Expr.Ident(ok), beta)
                });
            foreach (Expr e in pcUpdateRHS)
            {
                e.Typecheck(new TypecheckingContext(null));
            }
            return new List<Cmd> {new AssignCmd(Token.NoToken, pcUpdateLHS, pcUpdateRHS)};
        }

        public List<Cmd> CreateUpdatesToOldOutputVars()
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (Variable o in oldOutputMap.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldOutputMap[o])));
                rhss.Add(Expr.Ident(o));
            }
            var cmds = new List<Cmd>();
            if (lhss.Count > 0)
            {
                cmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }
            return cmds;
        }

        public List<Cmd> CreateYieldingLoopHeaderInitCmds(Block header)
        {
            var newCmds = new List<Cmd>();
            var pcForYieldingLoopHeader = pcsForYieldingLoopsHeaders[header];
            var okForYieldingLoopHeader = oksForYieldingLoopHeaders[header];
            var assignCmd =  new AssignCmd(Token.NoToken,
                new List<AssignLhs>
                {
                    new SimpleAssignLhs(Token.NoToken, Expr.Ident(pcForYieldingLoopHeader)),
                    new SimpleAssignLhs(Token.NoToken, Expr.Ident(okForYieldingLoopHeader))
                },
                new List<Expr> {Expr.Ident(pc), Expr.Ident(ok)});
            newCmds.Add(assignCmd);
            return newCmds;
        }

        public List<Cmd> CreateYieldingLoopHeaderAssertCmds(Block header)
        {
            var newCmds = new List<Cmd>();
            var pcForYieldingLoopHeader = pcsForYieldingLoopsHeaders[header];
            var pcAssertCmd = new AssertCmd(header.tok, Expr.Eq(Expr.Ident(pcForYieldingLoopHeader), Expr.Ident(pc)));
            pcAssertCmd.ErrorData = "Specification state must not change for transitions ending in loop headers";
            newCmds.Add(pcAssertCmd);
            var okForYieldingLoopHeader = oksForYieldingLoopHeaders[header];
            var okAssertCmd = new AssertCmd(header.tok, Expr.Imp(Expr.Ident(okForYieldingLoopHeader), Expr.Ident(ok)));
            okAssertCmd.ErrorData = "Specification state must not change for transitions ending in loop headers";
            newCmds.Add(okAssertCmd);
            return newCmds;
        }

        private AssertCmd CreateSkipOrBetaAssertCmd()
        {
            // assert pc || g_old == g || beta(i, g_old, o, g);
            var aa = OldEqualityExprForGlobals();
            var assertExpr = Expr.Or(Expr.Ident(pc), Expr.Or(aa, beta));
            assertExpr.Typecheck(new TypecheckingContext(null));
            var skipOrBetaAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
            skipOrBetaAssertCmd.ErrorData = "Transition invariant violated in initial state";
            return skipOrBetaAssertCmd;
        }

        private AssertCmd CreateSkipAssertCmd()
        {
            // assert pc ==> o_old == o && g_old == g;
            Expr bb = OldEqualityExpr();
            var assertExpr = Expr.Imp(Expr.Ident(pc), bb);
            assertExpr.Typecheck(new TypecheckingContext(null));
            AssertCmd skipAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
            skipAssertCmd.ErrorData = "Transition invariant violated in final state";
            return skipAssertCmd;
        }

        private Expr OldEqualityExpr()
        {
            return Expr.And(OldEqualityExprForGlobals(), OldEqualityExprForOutputs());
        }

        private Expr OldEqualityExprForGlobals()
        {
            return Expr.And(this.oldGlobalMap.Select(kvPair => Expr.Eq(Expr.Ident(kvPair.Key), Expr.Ident(kvPair.Value))));
        }

        private Expr OldEqualityExprForOutputs()
        {
            return Expr.And(this.oldOutputMap.Select(kvPair => Expr.Eq(Expr.Ident(kvPair.Key), Expr.Ident(kvPair.Value))));
        }

        private LocalVariable Old(Variable v)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, $"og_old_{v.Name}", v.TypedIdent.Type));
        }

        private LocalVariable Pc()
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_pc", Type.Bool));
        }

        private LocalVariable Ok()
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_ok", Type.Bool));
        }
        
        private LocalVariable PcForYieldingLoopHeader(Block header)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, $"og_pc_{header.Label}", Type.Bool));
        }

        private LocalVariable OkForYieldingLoopHeader(Block header)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, $"og_ok_{header.Label}", Type.Bool));
        }
    }
}
