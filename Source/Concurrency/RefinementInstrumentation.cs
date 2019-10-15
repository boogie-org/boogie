using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
    class RefinementInstrumentation
    {
        private Dictionary<Variable, Variable> ogOldGlobalMap;
        private Variable pc;
        private Variable ok;
        private Expr alpha;
        private Expr beta;
        private HashSet<Variable> frame;

        public RefinementInstrumentation(Dictionary<Variable, Variable> ogOldGlobalMap, Variable pc, Variable ok, Expr alpha,
            Expr beta, HashSet<Variable> frame)
        {
            this.ogOldGlobalMap = ogOldGlobalMap;
            this.pc = pc;
            this.ok = ok;
            this.alpha = alpha;
            this.beta = beta;
            this.frame = frame;
        }

        public AssumeCmd CreateAssumeCmd()
        {
            // assume pc || alpha(i, g);
            Expr assumeExpr = Expr.Or(Expr.Ident(pc), alpha);
            assumeExpr.Type = Type.Bool;
            return new AssumeCmd(Token.NoToken, assumeExpr);
        }

        public AssertCmd CreateFinalAssertCmd(IToken tok)
        {
            AssertCmd assertCmd = new AssertCmd(tok, Expr.Ident(ok));
            assertCmd.ErrorData = "Failed to execute atomic action before procedure return";
            return assertCmd;
        }

        public AssertCmd CreateSkipOrBetaAssertCmd(IToken tok)
        {
            // assert pc || g_old == g || beta(i, g_old, o, g);
            var aa = OldEqualityExprForGlobals();
            var assertExpr = Expr.Or(Expr.Ident(pc), Expr.Or(aa, beta));
            assertExpr.Typecheck(new TypecheckingContext(null));
            var skipOrBetaAssertCmd = new AssertCmd(tok, assertExpr);
            skipOrBetaAssertCmd.ErrorData = "Transition invariant in initial state violated";
            return skipOrBetaAssertCmd;
        }

        public AssertCmd CreateSkipAssertCmd(IToken tok)
        {
            // assert pc ==> o_old == o && g_old == g;
            Expr bb = OldEqualityExpr();
            var assertExpr = Expr.Imp(Expr.Ident(pc), bb);
            assertExpr.Typecheck(new TypecheckingContext(null));
            AssertCmd skipAssertCmd = new AssertCmd(tok, assertExpr);
            skipAssertCmd.ErrorData = "Transition invariant in final state violated";
            return skipAssertCmd;
        }

        public AssignCmd CreatePcOkUpdateCmd()
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

            return new AssignCmd(Token.NoToken, pcUpdateLHS, pcUpdateRHS);
        }

        public AssignCmd CreateInitCmd()
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(pc)));
            rhss.Add(Expr.False);
            lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(ok)));
            rhss.Add(Expr.False);
            return new AssignCmd(Token.NoToken, lhss, rhss);
        }

        public List<Variable> ProcessLoopHeaders(
            Graph<Block> graph,
            HashSet<Block> yieldingHeaders)
        {
            var newLocalVars = new List<Variable>();
            foreach (Block header in yieldingHeaders)
            {
                LocalVariable oldPc = OgPcLabelLocal(header.Label);
                LocalVariable oldOk = OgOkLabelLocal(header.Label);
                newLocalVars.Add(oldPc);
                newLocalVars.Add(oldOk);

                foreach (Block pred in header.Predecessors)
                {
                    if (!graph.BackEdgeNodes(header).Contains(pred))
                    {
                        pred.Cmds.Add(new AssignCmd(Token.NoToken,
                            new List<AssignLhs>
                            {
                                new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldPc)),
                                new SimpleAssignLhs(Token.NoToken, Expr.Ident(oldOk))
                            },
                            new List<Expr> {Expr.Ident(pc), Expr.Ident(ok)}));
                    }
                }

                var pcAssertCmd = new AssertCmd(header.tok, Expr.Eq(Expr.Ident(oldPc), Expr.Ident(pc)));
                pcAssertCmd.ErrorData = "Specification state must not change for transitions ending in loop headers";
                header.cmds.Insert(0, pcAssertCmd);
                var okAssertCmd = new AssertCmd(header.tok, Expr.Imp(Expr.Ident(oldOk), Expr.Ident(ok)));
                okAssertCmd.ErrorData = "Specification state must not change for transitions ending in loop headers";
                header.cmds.Insert(1, okAssertCmd);
            }
            return newLocalVars;
        }

        // Versions of PC and OK for desugaring loops
        private LocalVariable OgPcLabelLocal(string label)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format("og_pc_{0}", label), Type.Bool));
        }

        private LocalVariable OgOkLabelLocal(string label)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format("og_ok_{0}", label), Type.Bool));
        }

        private Expr OldEqualityExpr()
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

        private Expr OldEqualityExprForGlobals()
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
    }
}