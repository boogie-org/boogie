using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using System.ComponentModel;
using System;

namespace Microsoft.Boogie
{
    public class TransitionRelationComputation
    {
        public readonly Implementation first, second;
        public readonly HashSet<Variable> frame;
        public readonly HashSet<Variable> allInParams, allOutParams, allLocVars;
        public readonly Dictionary<Variable, List<WitnessFunction>> globalVarToWitnesses;
        public readonly bool ignorePostState;

        private readonly string messagePrefix;
        private readonly CheckingContext checkingContext;

        private List<Cmd> path;
        private int transferIndex; // from first to second action

        private List<Expr> pathTranslations;

        public bool IsJoint => second != null;

        public IEnumerable<Variable> AllVariables =>
            frame.Union(allInParams).Union(allOutParams).Union(allLocVars).Distinct();

        public IEnumerable<Variable> PostStateVars => frame.Union(allOutParams).Distinct();

        public IEnumerable<Variable> PreStateVars => frame.Union(allInParams).Distinct();

        public IEnumerable<Variable> FrameWithWitnesses => frame.Intersect(globalVarToWitnesses.Keys);

        private TransitionRelationComputation(
            Implementation first, Implementation second,
            IEnumerable<Variable> frame, List<WitnessFunction> witnesses, bool ignorePostState,
            string messagePrefix)
        {
            this.first = first;
            this.second = second;
            this.frame = new HashSet<Variable>(frame);
            this.ignorePostState = ignorePostState;

            allInParams = new HashSet<Variable>(first.InParams);
            allOutParams = new HashSet<Variable>(first.OutParams);
            allLocVars = new HashSet<Variable>(first.LocVars);
            if (IsJoint)
            {
                allInParams.UnionWith(second.InParams);
                allOutParams.UnionWith(second.OutParams);
                allLocVars.UnionWith(second.LocVars);
            }

            this.messagePrefix = messagePrefix;
            this.checkingContext = new CheckingContext(null);

            this.pathTranslations = new List<Expr>();
            this.globalVarToWitnesses = new Dictionary<Variable, List<WitnessFunction>>();
            if (witnesses != null)
            {
                foreach (var witness in witnesses)
                {
                    var gVar = witness.witnessedVariable;
                    if (!globalVarToWitnesses.ContainsKey(gVar))
                    {
                        globalVarToWitnesses[gVar] = new List<WitnessFunction>();
                    }
                    globalVarToWitnesses[gVar].Add(witness);
                }
            }
        }

        private static Expr ComputeTransitionRelation(
            Implementation first, Implementation second,
            IEnumerable<Variable> frame, List<WitnessFunction> witnesses, bool ignorePostState,
            string messagePrefix)
        {
            var trc = new TransitionRelationComputation(first, second, frame, witnesses, ignorePostState, messagePrefix);
            trc.EnumeratePaths();
            var transitionRelation = Expr.Or(trc.pathTranslations);

            ResolutionContext rc = new ResolutionContext(null)
            {
                StateMode = ResolutionContext.State.Two
            };
            transitionRelation.Resolve(rc);
            transitionRelation.Typecheck(new TypecheckingContext(null));

            return transitionRelation;
        }

        public static Expr Commutativity(AtomicAction first, AtomicAction second,
            HashSet<Variable> frame, List<WitnessFunction> witnesses)
        {
            return ComputeTransitionRelation(
                first.secondImpl,
                second.firstImpl,
                frame, witnesses, false,
                string.Format("Transition relation of {0} ∘ {1}", first.proc.Name, second.proc.Name));
        }

        public static Expr Refinement(AtomicAction action, HashSet<Variable> frame)
        {
            return ComputeTransitionRelation(
                action.impl,
                null, frame, null, false,
                string.Format("Transition relation of {0}", action.proc.Name));
        }

        public static Expr Nonblocking(AtomicAction action, HashSet<Variable> frame)
        {
            return ComputeTransitionRelation(
                action.impl,
                null, frame, null, true,
                string.Format("Nonblocking expression of {0}", action.proc.Name));
        }

        private void EnumeratePaths()
        {
            path = new List<Cmd>();
            Debug.Assert(path.Count == 0);
            EnumeratePathsRec(first.Blocks[0], true);
            Debug.Assert(path.Count == 0);
        }

        private void EnumeratePathsRec(Block b, bool inFirst)
        {
            int pathSizeAtEntry = path.Count;

            foreach (Cmd cmd in b.Cmds)
            {
                path.Add(cmd);
            }
            if (b.TransferCmd is ReturnCmd)
            {
                if (inFirst && IsJoint)
                {
                    transferIndex = path.Count;
                    EnumeratePathsRec(second.Blocks[0], false);
                }
                else
                {
                    AddPath();
                }
            }
            else
            {
                GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    EnumeratePathsRec(target, inFirst);
                }
            }

            Debug.Assert(path.Count >= pathSizeAtEntry);
            path.RemoveRange(pathSizeAtEntry, path.Count - pathSizeAtEntry);
        }

        private void AddPath()
        {
            var pathTranslation = new PathTranslation(this, new List<Cmd>(path), transferIndex);
            pathTranslations.Add(pathTranslation.TransitionRelationExpr);

            if (CommandLineOptions.Clo.WarnNotEliminatedVars)
            {
                var quantifiedVars = pathTranslation.GetQuantifiedOriginalVariables();
                if (quantifiedVars.Any())
                {
                    checkingContext.Warning(Token.NoToken,
                        string.Format("{0}: could not eliminate variables {{{1}}} on some path",
                            messagePrefix, string.Join(", ", quantifiedVars)));
                }
            }
        }
    }

    class PathTranslation
    {
        private readonly TransitionRelationComputation trc;
        private List<Cmd> path;
        private readonly int transferIndex;

        private Dictionary<Variable, List<Variable>> varCopies;
        private Dictionary<Variable, Variable> copyToOriginalVar;
        private HashSet<Variable> definedVariables;
        private Dictionary<Variable, Expr> varToExpr;
        private List<Expr> pathExprs;
        private List<Expr> witnessedTransitionRelations;

        private Dictionary<Variable, Variable> frameIntermediateCopy;

        private Dictionary<Variable, Variable> existsVarMap;

        public Expr TransitionRelationExpr;

        private const string copierFormat = "{0}#{1}";

        private IEnumerable<Variable> IntermediateFrameWithWitnesses =>
            trc.FrameWithWitnesses.Select(v => frameIntermediateCopy[v]);

        public PathTranslation(TransitionRelationComputation trc, List<Cmd> path, int transferIndex)
        {
            this.trc = trc;
            this.path = path;
            this.transferIndex = transferIndex;

            SetupVarCopies();
            IntroduceIntermediateVars();
            SetDefinedVariables();
            EliminateIntermediateVariables();
            ComputeTransitionRelationExpr();
        }

        private void SetupVarCopies()
        {
            varCopies = new Dictionary<Variable, List<Variable>>();
            copyToOriginalVar = new Dictionary<Variable, Variable>();

            foreach (var v in trc.AllVariables)
            {
                varCopies[v] = new List<Variable>();
                MakeNewCopy(v);
            }
        }

        private void MakeNewCopy(Variable v)
        {
            int id = varCopies[v].Count;
            var copyVar = new Formal(
                Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format(copierFormat, v.Name, id), v.TypedIdent.Type),
                false, null);
            varCopies[v].Add(copyVar);
            copyToOriginalVar[copyVar] = v;
        }

        private IEnumerable<Variable> AllIntroducedVariables =>
            varCopies.SelectMany(x => x.Value);

        private Dictionary<Variable, Variable> LatestCopies(IEnumerable<Variable> vars)
        {
            return vars.ToDictionary(v => v, v => varCopies[v].Last());
        }

        private Dictionary<Variable, Variable> LatestCopies()
        {
            return LatestCopies(trc.AllVariables);
        }

        private void PopulateIntermediateFrameCopy()
        {
            frameIntermediateCopy = LatestCopies(trc.frame);
        }

        private void IntroduceIntermediateVars()
        {
            var oldSub = SubstitutionHelper.FromVariableMap(LatestCopies(trc.PreStateVars));
            var newPath = new List<Cmd>();
            for (int k = 0; k < path.Count; k++)
            {
                if (trc.IsJoint && k == transferIndex)
                {
                    PopulateIntermediateFrameCopy();
                    oldSub = SubstitutionHelper.FromVariableMap(LatestCopies(trc.PreStateVars));
                }
                Cmd cmd = path[k];
                if (cmd is AssignCmd)
                {
                    AssignCmd assignCmd = ((AssignCmd)cmd).AsSimpleAssignCmd;
                    var preState = LatestCopies();
                    foreach (var v in assignCmd.Lhss)
                    {
                        MakeNewCopy(v.DeepAssignedVariable);
                    }
                    var postState = LatestCopies();

                    if (QKeyValue.FindBoolAttribute(assignCmd.Attributes, CivlAttributes.BACKWARD))
                    {
                        var tmp = preState;
                        preState = postState;
                        postState = tmp;
                    }

                    var rhsSub = SubstitutionHelper.FromVariableMap(preState);

                    List<AssignLhs> lhss = assignCmd.Lhss.Select(x => (AssignLhs)new SimpleAssignLhs(Token.NoToken,
                        Expr.Ident(postState[x.DeepAssignedVariable]))).ToList();
                    List<Expr> rhss = assignCmd.Rhss.Select(x =>
                        Substituter.ApplyReplacingOldExprs(rhsSub, oldSub, x)).ToList();

                    newPath.Add(new AssignCmd(Token.NoToken, lhss, rhss, assignCmd.Attributes));
                }
                else if (cmd is AssumeCmd)
                {
                    var sub = SubstitutionHelper.FromVariableMap(LatestCopies());
                    newPath.Add(new AssumeCmd(cmd.tok,
                        Substituter.ApplyReplacingOldExprs(sub, oldSub, ((AssumeCmd)cmd).Expr)));
                }
                else if (cmd is HavocCmd havocCmd)
                {
                    foreach (var v in havocCmd.Vars)
                    {
                        MakeNewCopy(v.Decl);
                    }
                }
                else
                {
                    Debug.Assert(false);
                }
            }
            // In case there were no commands from the second action
            if (trc.IsJoint && path.Count == transferIndex)
                PopulateIntermediateFrameCopy();
            path = newPath;
        }

        private void SetDefinedVariables()
        {
            definedVariables = new HashSet<Variable>();
            foreach (var v in trc.PreStateVars)
            {
                definedVariables.Add(varCopies[v][0]);
            }
            if (!trc.ignorePostState)
            {
                foreach (var v in trc.PostStateVars)
                {
                    definedVariables.Add(varCopies[v].Last());
                }
            }
        }

        private void EliminateIntermediateVariables()
        {
            varToExpr = new Dictionary<Variable, Expr>();
            foreach (var v in definedVariables)
            {
                varToExpr[v] = Expr.Ident(v);
            }

            TryElimination(Enumerable.Empty<Variable>());
            TryElimination(trc.allLocVars.Select(v => varCopies[v][0]));

            if (trc.ignorePostState)
            {
                TryElimination(trc.PostStateVars);
            }
            else if (trc.IsJoint)
            {
                var remainingIntermediateFrame = frameIntermediateCopy.Values.Except(varToExpr.Keys);
                TryElimination(remainingIntermediateFrame);
                TryElimination(remainingIntermediateFrame.Intersect(IntermediateFrameWithWitnesses));
                // TODO: Generate warning for variables without any witness functions
            }
        }

        private void TryElimination(IEnumerable<Variable> extraDefinedVariables)
        {
            bool changed;
            do
            {
                changed = false;
                var remainingCmds = new List<Cmd>();
                foreach (var cmd in path)
                {
                    if (cmd is AssignCmd assignCmd)
                    {
                        var lhss = new List<AssignLhs>();
                        var rhss = new List<Expr>();
                        for (int k = 0; k < assignCmd.Lhss.Count; k++)
                        {
                            var lhs = assignCmd.Lhss[k];
                            var rhs = assignCmd.Rhss[k];
                            Variable assignedVar = lhs.DeepAssignedVariable;

                            var allDefinedVars = varToExpr.Keys.Union(extraDefinedVariables);
                            if (!allDefinedVars.Contains(assignedVar) &&
                                !VariableCollector.Collect(rhs).Intersect(AllIntroducedVariables).
                                    Except(allDefinedVars).Any())
                            {
                                varToExpr[assignedVar] = rhs;
                                changed = true;
                            }
                            else
                            {
                                lhss.Add(lhs);
                                rhss.Add(rhs);
                            }
                        }
                        if (lhss.Any())
                        {
                            remainingCmds.Add(new AssignCmd(cmd.tok, lhss, rhss, assignCmd.Attributes));
                        }
                    }
                    else if (cmd is AssumeCmd)
                    {
                        remainingCmds.Add(cmd);
                    }
                }
                Substitution sub = Substituter.SubstitutionFromHashtable(varToExpr);
                path = remainingCmds.Select(cmd => ApplyOnRhss(sub, cmd)).ToList();
            } while (changed);
        }

        private static Cmd ApplyOnRhss(Substitution sub, Cmd cmd)
        {
            if (cmd is AssignCmd assignCmd)
            {
                return new AssignCmd(cmd.tok,
                    assignCmd.Lhss,
                    assignCmd.Rhss.Select(x => Substituter.Apply(sub, x)).ToList(),
                    assignCmd.Attributes);
            }
            else { return Substituter.Apply(sub, cmd); }
        }

        private void ComputeTransitionRelationExpr()
        {
            CalculatePathExpression();
            AddBoundVariablesForRemainingVars();
            ReplacePreOrPostStateVars();
            TransitionRelationExpr = Expr.And(pathExprs);
            if (trc.IsJoint)
            {
                ComputeWitnessedTransitionRelationExprs();
                if (witnessedTransitionRelations.Count > 0)
                {
                    TransitionRelationExpr = Expr.Or(witnessedTransitionRelations);
                }
            }
            if (existsVarMap.Any())
            {
                TransitionRelationExpr = new ExistsExpr(Token.NoToken,
                    existsVarMap.Values.ToList<Variable>(), TransitionRelationExpr);
            }
        }

        private void CalculatePathExpression()
        {
            pathExprs = new List<Expr>();
            foreach (var cmd in path.OfType<AssumeCmd>())
            {
                ExprHelper.FlattenAnd(cmd.Expr, pathExprs);
            }
            foreach (AssignCmd cmd in path.OfType<AssignCmd>())
            {
                for (int k = 0; k < cmd.Lhss.Count; k++)
                {
                    pathExprs.Add(Expr.Eq(Expr.Ident(cmd.Lhss[k].DeepAssignedVariable), cmd.Rhss[k]));
                }
            }

            var varSubst = Substituter.SubstitutionFromHashtable(varToExpr);
            pathExprs = pathExprs.Select(x => Substituter.Apply(varSubst, x)).ToList();
        }

        private IEnumerable<Variable> NotEliminatedVars =>
            path.
                SelectMany(cmd => VariableCollector.Collect(cmd)).
                Intersect(AllIntroducedVariables).
                Except(varToExpr.Keys);

        private void AddBoundVariablesForRemainingVars()
        {
            var remainingVars = NotEliminatedVars.Except(IntermediateFrameWithWitnesses);
            existsVarMap = remainingVars.ToDictionary(v => (Variable)VarHelper.BoundVariable(v.Name, v.TypedIdent.Type));
            var varSubst = SubstitutionHelper.FromVariableMap(existsVarMap);
            pathExprs = pathExprs.Select(x => Substituter.Apply(varSubst, x)).ToList();
        }

        private void ReplacePreOrPostStateVars()
        {
            var preStateSub = trc.PreStateVars.
                ToDictionary<Variable, Variable, Expr>(v => varCopies[v][0],
                    v => new OldExpr(Token.NoToken, Expr.Ident(v)));

            var frameCopiesSub = preStateSub;
            if (!trc.ignorePostState)
            {
                var postStateSub = trc.PostStateVars.
                   ToDictionary<Variable, Variable, Expr>(v => varCopies[v].Last(), v => Expr.Ident(v));

                var notModifiedVars = new HashSet<Variable>(preStateSub.Keys.Intersect(postStateSub.Keys));
                foreach (var v in notModifiedVars)
                {
                    pathExprs.Add(Expr.Eq(preStateSub[v], postStateSub[v]));
                    postStateSub.Remove(v);
                }

                frameCopiesSub = frameCopiesSub.Union(postStateSub).ToDictionary(k => k.Key, v => v.Value);
            }

            var finalSub = Substituter.SubstitutionFromHashtable(frameCopiesSub);
            pathExprs = pathExprs.Select(x => Substituter.Apply(finalSub, x)).ToList();
        }

        private void ComputeWitnessedTransitionRelationExprs()
        {
            witnessedTransitionRelations = new List<Expr>();
            Dictionary<Variable, List<WitnessFunction>> varToWitnesses = trc.FrameWithWitnesses.
                Where(x => NotEliminatedVars.Contains(frameIntermediateCopy[x])).
                ToDictionary(
                    x => frameIntermediateCopy[x],
                    x => trc.globalVarToWitnesses[(GlobalVariable)x]);
            foreach (var witnessSet in varToWitnesses.Values.CartesianProduct())
            {
                Dictionary<Variable, Expr> witnessSubst = new Dictionary<Variable, Expr>();
                foreach (Tuple<Variable, WitnessFunction> pair in
                    Enumerable.Zip(varToWitnesses.Keys, witnessSet, Tuple.Create))
                {
                    WitnessFunction witnessFunction = pair.Item2;
                    witnessSubst[pair.Item1] = ExprHelper.FunctionCall(
                            witnessFunction.function, witnessFunction.args.ToArray()
                        );
                }
                var subst = Substituter.SubstitutionFromHashtable(witnessSubst);
                witnessedTransitionRelations.Add(
                    Substituter.Apply(subst, TransitionRelationExpr));
            }
        }

        public IEnumerable<Variable> GetQuantifiedOriginalVariables()
        {
            return existsVarMap.Keys.Select(x => copyToOriginalVar[x]).Distinct();
        }
    }

    public static class BackwardAssignmentSubstituter
    {
        public static void SubstituteBackwardAssignments(IEnumerable<AtomicAction> actions)
        {
            foreach (var action in actions)
            {
                SubstituteBackwardAssignments(action);
            }
        }

        private static void SubstituteBackwardAssignments(AtomicAction action)
        {
            foreach (Block block in action.impl.Blocks)
            {
                List<Cmd> cmds = new List<Cmd>();
                foreach (Cmd cmd in block.cmds)
                {
                    if (cmd is AssignCmd _assignCmd &&
                        QKeyValue.FindBoolAttribute(_assignCmd.Attributes, CivlAttributes.BACKWARD))
                    {
                        AssignCmd assignCmd = _assignCmd.AsSimpleAssignCmd;
                        var lhss = assignCmd.Lhss;
                        var rhss = assignCmd.Rhss;
                        var rhssVars = rhss.SelectMany(x => VariableCollector.Collect(x));
                        var lhssVars = lhss.SelectMany(x => VariableCollector.Collect(x));
                        if (rhssVars.Intersect(lhssVars).Any())
                        {
                            // TODO
                            throw new NotImplementedException("Substitution of backward assignment where lhs appears on rhs");
                        }
                        else
                        {
                            List<Expr> assumeExprs = new List<Expr>();
                            for (int k = 0; k < lhss.Count; k++)
                            {
                                assumeExprs.Add(Expr.Eq(lhss[k].AsExpr, rhss[k]));
                            }
                            cmds.Add(new AssumeCmd(Token.NoToken, Expr.And(assumeExprs)));
                            cmds.Add(new HavocCmd(Token.NoToken, lhss.Select(x => x.DeepAssignedIdentifier).ToList()));
                        }
                    }
                    else
                    {
                        cmds.Add(cmd);
                    }
                }
                block.cmds = cmds;
            }
        }
    }
}
