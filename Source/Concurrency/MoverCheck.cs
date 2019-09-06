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
        LinearTypeChecker linearTypeChecker;
        CivlTypeChecker civlTypeChecker;
        List<Declaration> decls;

        HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>> commutativityCheckerCache;
        HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>> gatePreservationCheckerCache;
        HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>> failurePreservationCheckerCache;

        private MoverCheck(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.civlTypeChecker = civlTypeChecker;
            this.decls = decls;
            this.commutativityCheckerCache = new HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>>();
            this.gatePreservationCheckerCache = new HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>>();
            this.failurePreservationCheckerCache = new HashSet<Tuple<AtomicActionCopy, AtomicActionCopy>>();
        }

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            if (civlTypeChecker.procToAtomicAction.Count == 0)
                return;

            MoverCheck moverChecking = new MoverCheck(linearTypeChecker, civlTypeChecker, decls);

            foreach (int layer in civlTypeChecker.allAtomicActionLayers)
            {
                var pool = civlTypeChecker.procToAtomicAction.Values.Where(a => a.layerRange.Contains(layer));

                var moverChecks =
                    from first in pool
                    from second in pool
                    where first.moverType != MoverType.Atomic
                    select new { First = first, Second = second };

                foreach (var moverCheck in moverChecks)
                {
                    var first = moverCheck.First.layerToActionCopy[layer];
                    var second = moverCheck.Second.layerToActionCopy[layer];

                    if (moverCheck.First.IsRightMover)
                    {
                        moverChecking.CreateCommutativityChecker(first, second);
                        moverChecking.CreateGatePreservationChecker(second, first);
                    }
                    if (moverCheck.First.IsLeftMover)
                    {
                        moverChecking.CreateCommutativityChecker(second, first);
                        moverChecking.CreateGatePreservationChecker(first, second);
                        moverChecking.CreateFailurePreservationChecker(second, first);
                    }
                }
                foreach (AtomicAction atomicAction in pool.Where(a => a.IsLeftMover))
                {
                    moverChecking.CreateNonBlockingChecker(atomicAction.layerToActionCopy[layer]);
                }
            }
        }

        private IEnumerable<Expr> DisjointnessExpr(IEnumerable<Variable> paramVars, HashSet<Variable> frame)
        {
            Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                domainNameToScope[domainName] = new HashSet<Variable>();
            }
            foreach (Variable v in paramVars.Union(frame))
            {
                var domainName = linearTypeChecker.FindDomainName(v);
                if (domainName == null) continue;
                domainNameToScope[domainName].Add(v);
            }
            foreach (string domainName in domainNameToScope.Keys)
            {
                yield return linearTypeChecker.DisjointnessExpr(domainName, domainNameToScope[domainName]);
            }
        }

        private Requires DisjointnessRequires(IEnumerable<Variable> paramVars, HashSet<Variable> frame)
        {
            return new Requires(false, Expr.And(DisjointnessExpr(paramVars, frame)));
        }

        private void AddChecker(string checkerName, List<Variable> inputs, List<Variable> outputs, List<Variable> locals, List<Requires> requires, List<Ensures> ensures, List<Block> blocks)
        {
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, civlTypeChecker.sharedVariableIdentifiers, ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateCommutativityChecker(AtomicActionCopy first, AtomicActionCopy second)
        {
            if (first == second && first.firstInParams.Count == 0 && first.firstOutParams.Count == 0)
                return;
            if (first.TriviallyCommutesWith(second))
                return;
            if (!commutativityCheckerCache.Add(Tuple.Create(first, second)))
                return;

            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(first.actionUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires> {
                DisjointnessRequires(
                    first.firstInParams.
                        Union(second.secondInParams).
                        Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT),
                    frame)
            };
            foreach (AssertCmd assertCmd in Enumerable.Union(first.firstGate, second.secondGate))
                requires.Add(new Requires(false, assertCmd.Expr));

            civlTypeChecker.atomicActionPairToWitnessFunctions.TryGetValue(
                Tuple.Create(first, second), out List<WitnessFunction> witnesses);
            var transitionRelation = NewTransitionRelationComputation.
                ComputeTransitionRelation(second, first, frame, witnesses);

            List<Cmd> cmds = new List<Cmd>
            {
                new CallCmd(Token.NoToken,
                        first.proc.Name,
                        first.firstInParams.Select(Expr.Ident).ToList<Expr>(),
                        first.firstOutParams.Select(Expr.Ident).ToList()
                    ) { Proc = first.proc },
                new CallCmd(Token.NoToken,
                        second.proc.Name,
                        second.secondInParams.Select(Expr.Ident).ToList<Expr>(),
                        second.secondOutParams.Select(Expr.Ident).ToList()
                    ) { Proc = second.proc }
            };
            var block = new Block(Token.NoToken, "init", cmds, new ReturnCmd(Token.NoToken));

            var secondInParamsFiltered = second.secondInParams.Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_IN);
            IEnumerable<Expr> linearityAssumes = Enumerable.Union(
                DisjointnessExpr(first.firstOutParams.Union(secondInParamsFiltered), frame),
                DisjointnessExpr(first.firstOutParams.Union(second.secondOutParams), frame));
            // TODO: add further disjointness expressions?
            Ensures ensureCheck = new Ensures(first.proc.tok, false, Expr.Imp(Expr.And(linearityAssumes), transitionRelation), null)
            {
                ErrorData = string.Format("Commutativity check between {0} and {1} failed", first.proc.Name, second.proc.Name)
            };
            List<Ensures> ensures = new List<Ensures> { ensureCheck };

            string checkerName = string.Format("CommutativityChecker_{0}_{1}", first.proc.Name, second.proc.Name);
            List<Variable> inputs = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();

            AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, ensures, new List<Block> { block });
        }

        private void CreateGatePreservationChecker(AtomicActionCopy first, AtomicActionCopy second)
        {
            if (!first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Any())
                return;
            if (!gatePreservationCheckerCache.Add(Tuple.Create(first, second)))
                return;

            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>
            {
                DisjointnessRequires(first.firstInParams.Union(second.secondInParams).Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame)
            };
            List<Ensures> ensures = new List<Ensures>();
            foreach (AssertCmd assertCmd in second.secondGate)
                requires.Add(new Requires(false, assertCmd.Expr));

            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(first.firstInParams.Union(second.secondOutParams), frame);
            foreach (AssertCmd assertCmd in first.firstGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
                Ensures ensureCheck = new Ensures(assertCmd.tok, false, Expr.Imp(Expr.And(linearityAssumes), assertCmd.Expr), null)
                {
                    ErrorData = string.Format("Gate of {0} not preserved by {1}", first.proc.Name, second.proc.Name)
                };
                ensures.Add(ensureCheck);
            }
            string checkerName = string.Format("GatePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);

            List<Variable> inputs = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();
            var block = new Block(Token.NoToken, "init",
                new List<Cmd>
                {
                    new CallCmd(Token.NoToken,
                            second.proc.Name,
                            second.secondInParams.Select(Expr.Ident).ToList<Expr>(),
                            second.secondOutParams.Select(Expr.Ident).ToList()
                        ) { Proc = second.proc }
                },
                new ReturnCmd(Token.NoToken));

            AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, ensures, new List<Block> { block });
        }

        private void CreateFailurePreservationChecker(AtomicActionCopy first, AtomicActionCopy second)
        {
            if (!first.gateUsedGlobalVars.Intersect(second.modifiedGlobalVars).Any())
                return;
            if (!failurePreservationCheckerCache.Add(Tuple.Create(first, second)))
                return;

            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>
            {
                DisjointnessRequires(first.firstInParams.Union(second.secondInParams).Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame)
            };
            Expr firstNegatedGate = Expr.Not(Expr.And(first.firstGate.Select(a => a.Expr)));
            firstNegatedGate.Type = Type.Bool; // necessary?
            requires.Add(new Requires(false, firstNegatedGate));
            foreach (AssertCmd assertCmd in second.secondGate)
                requires.Add(new Requires(false, assertCmd.Expr));

            IEnumerable<Expr> linearityAssumes = DisjointnessExpr(first.firstInParams.Union(second.secondOutParams), frame);
            Ensures ensureCheck = new Ensures(first.proc.tok, false, Expr.Imp(Expr.And(linearityAssumes), firstNegatedGate), null)
            {
                ErrorData = string.Format("Gate failure of {0} not preserved by {1}", first.proc.Name, second.proc.Name)
            };
            List<Ensures> ensures = new List<Ensures> { ensureCheck };
            
            string checkerName = string.Format("FailurePreservationChecker_{0}_{1}", first.proc.Name, second.proc.Name);

            List<Variable> inputs = Enumerable.Union(first.firstInParams, second.secondInParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstOutParams, second.secondOutParams).ToList();
            var block = new Block(Token.NoToken, "init",
                new List<Cmd>
                {
                    new CallCmd(Token.NoToken,
                            second.proc.Name,
                            second.secondInParams.Select(Expr.Ident).ToList<Expr>(),
                            second.secondOutParams.Select(Expr.Ident).ToList()
                        ) { Proc = second.proc }
                },
                new ReturnCmd(Token.NoToken));

            AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, ensures, new List<Block> { block });
        }

        private void CreateNonBlockingChecker(AtomicActionCopy action)
        {
            if (!action.HasAssumeCmd) return;

            Implementation impl = action.impl;
            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(action.gateUsedGlobalVars);
            frame.UnionWith(action.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires>
            {
                DisjointnessRequires(impl.InParams.
                    Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame)
            };
            foreach (AssertCmd assertCmd in action.gate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
            }

            Expr nonBlockingExpr = NewTransitionRelationComputation.
                ComputeTransitionRelation(action, frame, true);
            AssertCmd nonBlockingAssert = new AssertCmd(action.proc.tok, nonBlockingExpr)
            {
                ErrorData = string.Format("Non-blocking check for {0} failed", action.proc.Name)
            };

            Block block = new Block(action.proc.tok, "L", new List<Cmd> { nonBlockingAssert },
                new ReturnCmd(Token.NoToken));

            string checkerName = string.Format("NonBlockingChecker_{0}", action.proc.Name);
            AddChecker(checkerName, new List<Variable>(impl.InParams), new List<Variable>(),
                new List<Variable>(), requires, new List<Ensures>(), new List<Block> { block });
        }
    }
}