using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    class RefinementInstrumentation
    {
        public virtual List<Variable> NewLocalVars => new List<Variable>();

        public virtual List<Cmd> CreateInitCmds()
        {
            return new List<Cmd>();
        }

        public virtual List<Cmd> CreateAssumeCmds()
        {
            return new List<Cmd>();
        }

        public virtual List<Cmd> CreateAssertCmds()
        {
            return new List<Cmd>();
        }

        public virtual List<Cmd> CreateReturnAssertCmds()
        {
            return new List<Cmd>();
        }

        public virtual List<Cmd> CreateUnchangedGlobalsAssertCmds()
        {
            return new List<Cmd>();
        }

        public virtual List<Cmd> CreateUnchangedOutputsAssertCmds()
        {
            return new List<Cmd>();
        }

        public virtual List<Cmd> CreateUpdatesToRefinementVars()
        {
            return new List<Cmd>();
        }

        public virtual List<Cmd> CreateUpdatesToOldOutputVars()
        {
            return new List<Cmd>();
        }
    }

    class SkipRefinementInstrumentation : RefinementInstrumentation
    {
        protected Dictionary<Variable, Variable> oldGlobalMap;

        public SkipRefinementInstrumentation(
            CivlTypeChecker civlTypeChecker,
            YieldingProc yieldingProc,
            Dictionary<Variable, Variable> oldGlobalMap)
        {
            this.oldGlobalMap = new Dictionary<Variable, Variable>();
            foreach (Variable v in civlTypeChecker.sharedVariables)
            {
                var layerRange = civlTypeChecker.GlobalVariableLayerRange(v);
                if (layerRange.lowerLayerNum <= yieldingProc.upperLayer && yieldingProc.upperLayer < layerRange.upperLayerNum)
                {
                    this.oldGlobalMap[v] = oldGlobalMap[v];
                }
            }
        }

        public override List<Cmd> CreateAssertCmds()
        {
            return CreateUnchangedGlobalsAssertCmds();
        }

        public override List<Cmd> CreateUnchangedGlobalsAssertCmds()
        {
            var cmds = new List<Cmd>();
            var assertExpr = Expr.And(this.oldGlobalMap.Select(kvPair => Expr.Eq(Expr.Ident(kvPair.Key), Expr.Ident(kvPair.Value)))); 
            assertExpr.Typecheck(new TypecheckingContext(null));
            AssertCmd skipAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
            skipAssertCmd.ErrorData = "Globals must not be modified";
            cmds.Add(skipAssertCmd);
            return cmds;
        }
    }

    class ActionRefinementInstrumentation : SkipRefinementInstrumentation
    {
        private Dictionary<Variable, Variable> oldOutputMap;
        private List<Variable> newLocalVars;
        private Variable pc;
        private Variable ok;
        private Expr alpha;
        private Expr beta;

        private Dictionary<AtomicAction, Expr> transitionRelationCache;

        public ActionRefinementInstrumentation(
            CivlTypeChecker civlTypeChecker,
            Implementation impl,
            Implementation originalImpl,
            Dictionary<Variable, Variable> oldGlobalMap):
            base (civlTypeChecker, civlTypeChecker.procToYieldingProc[originalImpl.Proc] as ActionProc, oldGlobalMap)
        {
            newLocalVars = new List<Variable>();
            ActionProc actionProc = civlTypeChecker.procToYieldingProc[originalImpl.Proc] as ActionProc;
            int layerNum = actionProc.upperLayer;
            pc = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_pc", Type.Bool));
            newLocalVars.Add(pc);
            ok = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "og_ok", Type.Bool));
            newLocalVars.Add(ok);

            this.transitionRelationCache = new Dictionary<AtomicAction, Expr>();

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

        public override List<Variable> NewLocalVars => newLocalVars;

        public override List<Cmd> CreateInitCmds()
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

        public override List<Cmd> CreateAssumeCmds()
        {
            var cmds = new List<Cmd>();
            // assume pc || alpha(i, g);
            Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
            assumeExpr.Type = Type.Bool;
            cmds.Add(new AssumeCmd(Token.NoToken, assumeExpr));
            return cmds;
        }

        public override List<Cmd> CreateAssertCmds()
        {
            Expr assertExpr;
            var cmds = new List<Cmd>();

            // assert pc || g_old == g || beta(i, g_old, o, g);
            assertExpr = Expr.Or(Expr.Ident(pc), Expr.Or(OldEqualityExprForGlobals(), beta));
            assertExpr.Typecheck(new TypecheckingContext(null));
            var skipOrBetaAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
            skipOrBetaAssertCmd.ErrorData = "Transition invariant violated in initial state";
            cmds.Add(skipOrBetaAssertCmd);

            // assert pc ==> o_old == o && g_old == g;
            assertExpr = Expr.Imp(Expr.Ident(pc), OldEqualityExpr());
            assertExpr.Typecheck(new TypecheckingContext(null));
            AssertCmd skipAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
            skipAssertCmd.ErrorData = "Transition invariant violated in final state";
            cmds.Add(skipAssertCmd);
            return cmds;
        }

        public override List<Cmd> CreateReturnAssertCmds()
        {
            var cmds = CreateUnchangedOutputsAssertCmds();
            AssertCmd assertCmd = new AssertCmd(Token.NoToken, Expr.Ident(ok));
            assertCmd.ErrorData = "Failed to execute atomic action before procedure return";
            cmds.Add(assertCmd);
            return cmds;
        }

        public override List<Cmd> CreateUnchangedOutputsAssertCmds()
        {
            // assert pc ==> o_old == o;
            var cmds = new List<Cmd>();
            Expr bb = OldEqualityExprForOutputs();
            var assertExpr = Expr.Imp(Expr.Ident(pc), bb);
            assertExpr.Typecheck(new TypecheckingContext(null));
            AssertCmd skipAssertCmd = new AssertCmd(Token.NoToken, assertExpr);
            skipAssertCmd.ErrorData = "Outputs must not be modified";
            cmds.Add(skipAssertCmd);
            return cmds;
        }

        public override List<Cmd> CreateUpdatesToRefinementVars()
        {
            // pc, ok := g_old == g ==> pc, beta(i, g_old, o, g) || o_old == o && ok;
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
                    Expr.Or(beta, Expr.And(OldEqualityExprForOutputs(), Expr.Ident(ok))),
                });
            foreach (Expr e in pcUpdateRHS)
            {
                e.Typecheck(new TypecheckingContext(null));
            }
            return new List<Cmd> {new AssignCmd(Token.NoToken, pcUpdateLHS, pcUpdateRHS)};
        }

        public override List<Cmd> CreateUpdatesToOldOutputVars()
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
    }
}
