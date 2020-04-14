using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    public class MoverCheck
    {
        LinearTypeChecker linearTypeChecker;
        CivlTypeChecker civlTypeChecker;
        List<Declaration> decls;

        HashSet<Tuple<AtomicAction, AtomicAction>> commutativityCheckerCache;
        HashSet<Tuple<AtomicAction, AtomicAction>> gatePreservationCheckerCache;
        HashSet<Tuple<AtomicAction, AtomicAction>> failurePreservationCheckerCache;

        private MoverCheck(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.civlTypeChecker = civlTypeChecker;
            this.decls = decls;
            this.commutativityCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
            this.gatePreservationCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
            this.failurePreservationCheckerCache = new HashSet<Tuple<AtomicAction, AtomicAction>>();
        }

        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            MoverCheck moverChecking = new MoverCheck(linearTypeChecker, civlTypeChecker, decls);

            // TODO: make enumeration of mover checks more efficient / elegant

            var regularMoverChecks =
                from first in civlTypeChecker.procToAtomicAction.Values
                from second in civlTypeChecker.procToAtomicAction.Values
                where first.layerRange.OverlapsWith(second.layerRange)
                where first.IsRightMover || second.IsLeftMover
                select new { first, second };

            foreach (var moverCheck in regularMoverChecks)
            {
                if (moverCheck.first.IsRightMover)
                    moverChecking.CreateRightMoverCheckers(moverCheck.first, moverCheck.second);
                if (moverCheck.second.IsLeftMover)
                    moverChecking.CreateLeftMoverCheckers(moverCheck.first, moverCheck.second);
            }

            var inductiveSequentializationMoverChecks =
                from IS in civlTypeChecker.inductiveSequentializations
                from leftMover in IS.elim.Values
                from action in civlTypeChecker.procToAtomicAction.Values
                where action.layerRange.Contains(IS.inputAction.layerRange.upperLayerNum)
                select new { action, leftMover };

            foreach (var moverCheck in inductiveSequentializationMoverChecks)
            {
                moverChecking.CreateLeftMoverCheckers(moverCheck.action, moverCheck.leftMover);
            }

            // Here we include IS abstractions
            foreach (var atomicAction in civlTypeChecker.AllActions.Where(a => a.IsLeftMover))
            {
                moverChecking.CreateNonBlockingChecker(atomicAction);
            }

            // IS abstractions are marked left movers, so here we select regular atomic actions
            // that are not marked left mover but used as abstraction in IS.
            foreach (var atomicAction in civlTypeChecker.inductiveSequentializations.SelectMany(IS => IS.elim.Values).Where(a => !a.IsLeftMover).Distinct())
            {
                moverChecking.CreateNonBlockingChecker(atomicAction);
            }

            foreach (var introductionAction in civlTypeChecker.procToIntroductionAction.Values)
            {
                moverChecking.CreateNonBlockingChecker(introductionAction);
            }
        }

        private Requires DisjointnessRequires(IEnumerable<Variable> paramVars, HashSet<Variable> frame)
        {
            return new Requires(false, Expr.And(linearTypeChecker.DisjointnessExprForEachDomain(paramVars.Union(frame))));
        }

        private void AddChecker(string checkerName, List<Variable> inputs, List<Variable> outputs, List<Variable> locals, List<Requires> requires, List<Ensures> ensures, List<Block> blocks)
        {
            Procedure proc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, requires, civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList(), ensures);
            Implementation impl = new Implementation(Token.NoToken, checkerName, new List<TypeVariable>(), inputs, outputs, locals, blocks);
            impl.Proc = proc;
            this.decls.Add(impl);
            this.decls.Add(proc);
        }

        private void CreateRightMoverCheckers(AtomicAction rightMover, AtomicAction action)
        {
            CreateCommutativityChecker(rightMover, action);
            CreateGatePreservationChecker(action, rightMover);
        }

        private void CreateLeftMoverCheckers(AtomicAction action, AtomicAction leftMover)
        {
            CreateCommutativityChecker(action, leftMover);
            CreateGatePreservationChecker(leftMover, action);
            CreateFailurePreservationChecker(action, leftMover);
        }

        private void CreateCommutativityChecker(AtomicAction first, AtomicAction second)
        {
            if (first == second && first.firstImpl.InParams.Count == 0 && first.firstImpl.OutParams.Count == 0)
                return;
            if (first.TriviallyCommutesWith(second))
                return;
            if (!commutativityCheckerCache.Add(Tuple.Create(first, second)))
                return;

            string checkerName = $"CommutativityChecker_{first.proc.Name}_{second.proc.Name}";

            HashSet<Variable> frame = new HashSet<Variable>();
            frame.UnionWith(first.gateUsedGlobalVars);
            frame.UnionWith(first.actionUsedGlobalVars);
            frame.UnionWith(second.gateUsedGlobalVars);
            frame.UnionWith(second.actionUsedGlobalVars);

            List<Requires> requires = new List<Requires> {
                DisjointnessRequires(
                    first.firstImpl.InParams.
                        Union(second.secondImpl.InParams).
                        Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT),
                    frame)
            };
            foreach (AssertCmd assertCmd in Enumerable.Union(first.firstGate, second.secondGate))
                requires.Add(new Requires(false, assertCmd.Expr));

            var witnesses = civlTypeChecker.commutativityHints.GetWitnesses(first, second);
            var transitionRelation = TransitionRelationComputation.
                Commutativity(second, first, frame, witnesses);

            List<Cmd> cmds = new List<Cmd>
            {
                new CallCmd(Token.NoToken,
                        first.proc.Name,
                        first.firstImpl.InParams.Select(Expr.Ident).ToList<Expr>(),
                        first.firstImpl.OutParams.Select(Expr.Ident).ToList()
                    ) { Proc = first.proc },
                new CallCmd(Token.NoToken,
                        second.proc.Name,
                        second.secondImpl.InParams.Select(Expr.Ident).ToList<Expr>(),
                        second.secondImpl.OutParams.Select(Expr.Ident).ToList()
                    ) { Proc = second.proc }
            };
            foreach (var lemma in civlTypeChecker.commutativityHints.GetLemmas(first,second))
            {
                cmds.Add(CmdHelper.AssumeCmd(ExprHelper.FunctionCall(lemma.function, lemma.args.ToArray())));
            }
            var block = new Block(Token.NoToken, "init", cmds, new ReturnCmd(Token.NoToken));

            var secondInParamsFiltered = second.secondImpl.InParams.Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_IN);
            IEnumerable<Expr> linearityAssumes = Enumerable.Union(
                linearTypeChecker.DisjointnessExprForEachDomain(first.firstImpl.OutParams.Union(secondInParamsFiltered).Union(frame)),
                linearTypeChecker.DisjointnessExprForEachDomain(first.firstImpl.OutParams.Union(second.secondImpl.OutParams).Union(frame)));
            // TODO: add further disjointness expressions?
            Ensures ensureCheck = new Ensures(first.proc.tok, false, Expr.Imp(Expr.And(linearityAssumes), transitionRelation), null)
            {
                ErrorData = $"Commutativity check between {first.proc.Name} and {second.proc.Name} failed"
            };
            List<Ensures> ensures = new List<Ensures> { ensureCheck };

            List<Variable> inputs = Enumerable.Union(first.firstImpl.InParams, second.secondImpl.InParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstImpl.OutParams, second.secondImpl.OutParams).ToList();

            AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, ensures, new List<Block> { block });
        }

        private void CreateGatePreservationChecker(AtomicAction first, AtomicAction second)
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
                DisjointnessRequires(first.firstImpl.InParams.Union(second.secondImpl.InParams).Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame)
            };
            List<Ensures> ensures = new List<Ensures>();
            foreach (AssertCmd assertCmd in second.secondGate)
                requires.Add(new Requires(false, assertCmd.Expr));

            IEnumerable<Expr> linearityAssumes = linearTypeChecker.DisjointnessExprForEachDomain(first.firstImpl.InParams.Union(second.secondImpl.OutParams).Union(frame));
            foreach (AssertCmd assertCmd in first.firstGate)
            {
                requires.Add(new Requires(false, assertCmd.Expr));
                Ensures ensureCheck = new Ensures(assertCmd.tok, false, Expr.Imp(Expr.And(linearityAssumes), assertCmd.Expr), null)
                {
                    ErrorData = $"Gate of {first.proc.Name} not preserved by {second.proc.Name}"
                };
                ensures.Add(ensureCheck);
            }
            string checkerName = $"GatePreservationChecker_{first.proc.Name}_{second.proc.Name}";

            List<Variable> inputs = Enumerable.Union(first.firstImpl.InParams, second.secondImpl.InParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstImpl.OutParams, second.secondImpl.OutParams).ToList();
            var block = new Block(Token.NoToken, "init",
                new List<Cmd>
                {
                    new CallCmd(Token.NoToken,
                            second.proc.Name,
                            second.secondImpl.InParams.Select(Expr.Ident).ToList<Expr>(),
                            second.secondImpl.OutParams.Select(Expr.Ident).ToList()
                        ) { Proc = second.proc }
                },
                new ReturnCmd(Token.NoToken));

            AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, ensures, new List<Block> { block });
        }

        private void CreateFailurePreservationChecker(AtomicAction first, AtomicAction second)
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
                DisjointnessRequires(first.firstImpl.InParams.Union(second.secondImpl.InParams).Where(v => linearTypeChecker.FindLinearKind(v) != LinearKind.LINEAR_OUT), frame)
            };
            Expr firstNegatedGate = Expr.Not(Expr.And(first.firstGate.Select(a => a.Expr)));
            firstNegatedGate.Type = Type.Bool; // necessary?
            requires.Add(new Requires(false, firstNegatedGate));
            foreach (AssertCmd assertCmd in second.secondGate)
                requires.Add(new Requires(false, assertCmd.Expr));

            IEnumerable<Expr> linearityAssumes = linearTypeChecker.DisjointnessExprForEachDomain(first.firstImpl.InParams.Union(second.secondImpl.OutParams).Union(frame));
            Ensures ensureCheck = new Ensures(first.proc.tok, false, Expr.Imp(Expr.And(linearityAssumes), firstNegatedGate), null)
            {
                ErrorData = $"Gate failure of {first.proc.Name} not preserved by {second.proc.Name}"
            };
            List<Ensures> ensures = new List<Ensures> { ensureCheck };
            
            string checkerName = $"FailurePreservationChecker_{first.proc.Name}_{second.proc.Name}";

            List<Variable> inputs = Enumerable.Union(first.firstImpl.InParams, second.secondImpl.InParams).ToList();
            List<Variable> outputs = Enumerable.Union(first.firstImpl.OutParams, second.secondImpl.OutParams).ToList();
            var block = new Block(Token.NoToken, "init",
                new List<Cmd>
                {
                    new CallCmd(Token.NoToken,
                            second.proc.Name,
                            second.secondImpl.InParams.Select(Expr.Ident).ToList<Expr>(),
                            second.secondImpl.OutParams.Select(Expr.Ident).ToList()
                        ) { Proc = second.proc }
                },
                new ReturnCmd(Token.NoToken));

            AddChecker(checkerName, inputs, outputs, new List<Variable>(), requires, ensures, new List<Block> { block });
        }

        private void CreateNonBlockingChecker(Action action)
        {
            if (!action.HasAssumeCmd) return;

            string checkerName = $"NonBlockingChecker_{action.proc.Name}";

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

            Expr nonBlockingExpr = TransitionRelationComputation.
                Nonblocking(action, frame);
            AssertCmd nonBlockingAssert = new AssertCmd(action.proc.tok, nonBlockingExpr)
            {
                ErrorData = $"Non-blocking check for {action.proc.Name} failed"
            };

            Block block = new Block(action.proc.tok, "L", new List<Cmd> { nonBlockingAssert },
                new ReturnCmd(Token.NoToken));

            AddChecker(checkerName, new List<Variable>(impl.InParams), new List<Variable>(),
                new List<Variable>(), requires, new List<Ensures>(), new List<Block> { block });
        }
    }
}
