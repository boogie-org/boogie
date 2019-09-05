using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public enum AtomicActionCopyKind
    {
        FIRST, SECOND, NORMAL
    }

    public class AtomicActionCopyAdapter
    {
        public readonly AtomicActionCopy action;
        public readonly AtomicActionCopyKind copyType;

        public AtomicActionCopyAdapter(AtomicActionCopy action, AtomicActionCopyKind copyType)
        {
            this.action = action;
            this.copyType = copyType;
        }

        private T PassByKind<T>(T normalValue, T firstValue, T secondValue)
        {
            switch (copyType)
            {
                case AtomicActionCopyKind.FIRST:
                    return firstValue;
                case AtomicActionCopyKind.SECOND:
                    return secondValue;
                case AtomicActionCopyKind.NORMAL:
                    return normalValue;
                default:
                    throw new Exception();
            }
        }

        public List<AssertCmd> Gate
        {
            get
            {
                return PassByKind(action.gate, action.firstGate, action.secondGate);
            }
        }

        public List<Block> Blocks
        {
            get
            {
                return PassByKind(action.impl.Blocks, action.firstAction.Blocks,
                    action.secondAction.Blocks);
            }
        }

        public List<Variable> InParams
        {
            get
            {
                return PassByKind(action.impl.InParams, action.firstInParams,
                    action.secondInParams);
            }
        }

        public List<Variable> OutParams
        {
            get
            {
                return PassByKind(action.impl.OutParams, action.firstOutParams,
                    action.secondOutParams);
            }
        }

        public List<Variable> LocVars
        {
            get
            {
                return PassByKind(action.impl.LocVars, action.firstAction.LocVars,
                    action.secondAction.LocVars);
            }
        }

        public IEnumerable<Variable> Params
        {
            get
            {
                return InParams.Union(OutParams);
            }
        }

        public string Prefix
        {
            get
            {
                return PassByKind("", "first_", "second_");
            }
        }
    }

    public class NewTransitionRelationComputation
    {
        internal readonly AtomicActionCopyAdapter first, second;
        internal readonly HashSet<Variable> frame;
        internal readonly Dictionary<GlobalVariable, List<WitnessFunction>> globalVarToWitnesses;
        internal readonly bool ignorePostState;
        private Stack<Cmd> cmdStack;
        private List<PathTranslation> pathTranslations;

        private int transferStackIndex;

        private NewTransitionRelationComputation(AtomicActionCopyAdapter first,
            AtomicActionCopyAdapter second, IEnumerable<Variable> frame,
            List<WitnessFunction> witnesses, bool ignorePostState)
        {
            this.first = first;
            this.second = second;
            this.frame = new HashSet<Variable>(frame);
            this.ignorePostState = ignorePostState;

            this.globalVarToWitnesses = new Dictionary<GlobalVariable, List<WitnessFunction>>();
            if (witnesses != null)
            {
                foreach (var witness in witnesses)
                {
                    var gVar = witness.globalVar;
                    if (!globalVarToWitnesses.ContainsKey(gVar))
                    {
                        globalVarToWitnesses[gVar] = new List<WitnessFunction>();
                    }
                    globalVarToWitnesses[gVar].Add(witness);
                }
            }

            EnumeratePaths();
        }

        private static Expr ComputeTransitionRelation(AtomicActionCopyAdapter first,
            AtomicActionCopyAdapter second, IEnumerable<Variable> frame,
            List<WitnessFunction> witnesses, bool ignorePostState = false)
        {
            var transitionRelationComputation = new NewTransitionRelationComputation(first, second, frame, witnesses, ignorePostState);
            var transitionRelation = Expr.Or(transitionRelationComputation.pathTranslations.Select(x => x.TransitionRelationExpr));

            ResolutionContext rc = new ResolutionContext(null)
            {
                StateMode = ResolutionContext.State.Two
            };
            transitionRelation.Resolve(rc);
            transitionRelation.Typecheck(new TypecheckingContext(null));

            return transitionRelation;
        }

        public static Expr ComputeTransitionRelation(AtomicActionCopy first, AtomicActionCopy second,
            HashSet<Variable> frame, List<WitnessFunction> witnesses,
            AtomicActionCopyKind firstKind = AtomicActionCopyKind.SECOND,
            AtomicActionCopyKind secondKind = AtomicActionCopyKind.FIRST)
        {
            return ComputeTransitionRelation(
                new AtomicActionCopyAdapter(first, firstKind),
                new AtomicActionCopyAdapter(second, secondKind),
                frame, witnesses);
        }


        public static Expr ComputeTransitionRelation(AtomicActionCopy action, HashSet<Variable> frame,
            bool ignorePostState = true, AtomicActionCopyKind kind = AtomicActionCopyKind.NORMAL)
        {
            return ComputeTransitionRelation(new AtomicActionCopyAdapter(action, kind),
                null, frame, null, ignorePostState);
        }

        private void EnumeratePaths()
        {
            cmdStack = new Stack<Cmd>();
            this.pathTranslations = new List<PathTranslation>();
            Debug.Assert(cmdStack.Count == 0);
            EnumeratePathsRec(first.Blocks[0], true);
            Debug.Assert(cmdStack.Count == 0);
        }

        private void EnumeratePathsRec(Block b, bool inFirst)
        {
            int pathSizeAtEntry = cmdStack.Count;

            foreach (Cmd cmd in b.Cmds)
            {
                cmdStack.Push(cmd);
            }
            if (b.TransferCmd is ReturnCmd)
            {
                if (inFirst && second != null)
                {
                    transferStackIndex = cmdStack.Count;
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

            Debug.Assert(cmdStack.Count >= pathSizeAtEntry);
            while (cmdStack.Count > pathSizeAtEntry)
            {
                cmdStack.Pop();
            }
        }

        private void AddPath()
        {
            List<Cmd> cmds = new List<Cmd>(cmdStack);
            cmds.Reverse();
            pathTranslations.Add(new PathTranslation(this, cmds));
        }

        internal class PathTranslation
        {
            private readonly List<Cmd> cmds;
            private readonly NewTransitionRelationComputation transitionRelationComputer;
            private readonly HashSet<Variable> allInParams, allOutParams, allLocVars, frame;
            private readonly AtomicActionCopyAdapter first, second;

            // Used when second != null
            // TODO: Add some comments
            private Dictionary<Variable, Variable> frameIntermediateCopy;

            private List<Cmd> newCmds;
            private Dictionary<Variable, Variable>[] varCopies;
            private Dictionary<Variable, int> varLastCopyId;
            private HashSet<Variable> definedVariables;
            private Dictionary<Variable, Expr> varToExpr;
            private List<Expr> pathExprs;
            private List<Expr> witnessedTransitionRelations;

            internal Expr TransitionRelationExpr;

            private const string copierFormat = "{0}#{1}";

            internal PathTranslation(NewTransitionRelationComputation transitionRelationComputer,
                List<Cmd> cmds)
            {
                this.cmds = cmds;
                this.transitionRelationComputer = transitionRelationComputer;
                this.frame = transitionRelationComputer.frame;
                this.first = transitionRelationComputer.first;
                this.second = transitionRelationComputer.second;

                allInParams = new HashSet<Variable>(first.InParams);
                allOutParams = new HashSet<Variable>(first.OutParams);
                allLocVars = new HashSet<Variable>(first.LocVars);
                frameIntermediateCopy = new Dictionary<Variable, Variable>();
                if (IsJoint())
                {
                    allInParams.UnionWith(second.InParams);
                    allOutParams.UnionWith(second.OutParams);
                    allLocVars.UnionWith(second.LocVars);
                }

                SetupVarCopies();
                IntroduceIntermediateVars();
                EliminateIntermediateVariables();
                if (IsJoint())
                {
                    EliminateWithIntermediateState();
                }
                if (IgnorePostState)
                {
                    while (TryElimination(GetPostStateVars())) { }
                }
                // TODO: Generate warning for not eliminated variables
                ComputeTransitionRelationExpr();
            }

            private void EliminateWithIntermediateState()
            {
                Debug.Assert(IsJoint());

                var remainingIntermediateFrame = frameIntermediateCopy.
                    Where(kvp => !varToExpr.ContainsKey(kvp.Value)).
                    Select(kvp => kvp.Value);
                while (TryElimination(remainingIntermediateFrame)) { }

                while (TryElimination(remainingIntermediateFrame.
                    Intersect(IntermediateFrameWithWitnesses))) { }
                // TODO: Generate warning for variables without any witness functions
            }

            private bool IsJoint()
            {
                return second != null;
            }

            private IEnumerable<Variable> UsedVariables
            {
                get
                {
                    return allInParams.
                        Union(allOutParams).
                        Union(allLocVars).
                        Union(frame).Distinct();
                }
            }

            private IEnumerable<Variable> FrameWithWitnesses
            {
                get {
                    return frame.Intersect(
                        transitionRelationComputer.globalVarToWitnesses.Keys);
                }
            }

            private IEnumerable<Variable> IntermediateFrameWithWitnesses
            {
                get
                {
                    return FrameWithWitnesses.
                        Select(v => frameIntermediateCopy[v]);
                }
            }

            private void SetupVarCopies()
            {
                varCopies = new Dictionary<Variable, Variable>[cmds.Count + 1];
                foreach (int i in Enumerable.Range(0, cmds.Count + 1))
                    varCopies[i] = new Dictionary<Variable, Variable>();

                varLastCopyId = new Dictionary<Variable, int>();
                foreach (var v in UsedVariables)
                {
                    MakeNewCopy(v);
                }
            }

            private Dictionary<Variable, Variable> GetVarCopiesFromIds(Dictionary<Variable, int> varCopyId)
            {
                return varCopyId.ToDictionary(kvp => kvp.Key, kvp => varCopies[kvp.Value][kvp.Key]);
            }

            private void PopulateIntermediateFrameCopy()
            {
                frameIntermediateCopy = GetVarCopiesFromIds(varLastCopyId).
                    Where(kvp => frame.Contains(kvp.Key)).
                    ToDictionary(kvp => kvp.Key, kvp => kvp.Value);
            }

            private void IntroduceIntermediateVars()
            {
                newCmds = new List<Cmd>();
                for (int k = 0; k < cmds.Count; k++)
                {
                    if (IsJoint() && k == transitionRelationComputer.transferStackIndex)
                    {
                        PopulateIntermediateFrameCopy();
                    }
                    Cmd cmd = cmds[k];
                    if (cmd is AssignCmd)
                    {
                        AssignCmd assignCmd = ((AssignCmd)cmd).AsSimpleAssignCmd;
                        var preState = GetVarCopiesFromIds(varLastCopyId);
                        foreach (var v in assignCmd.Lhss)
                        {
                            MakeNewCopy(v.DeepAssignedVariable);
                        }
                        var postState = GetVarCopiesFromIds(varLastCopyId);

                        Dictionary<Variable, Variable> lhsMap = postState, rhsMap = preState;
                        // TODO: clean up "backward" usages
                        if (QKeyValue.FindBoolAttribute(assignCmd.Attributes, CivlAttributes.BACKWARD))
                        {
                            lhsMap = preState;
                            rhsMap = postState;
                        }

                        var rhsSub = Substituter.SubstitutionFromHashtable(
                            rhsMap.ToDictionary(
                                kvp => kvp.Key, kvp => Expr.Ident(kvp.Value) as Expr
                            ));

                        List<AssignLhs> lhss = assignCmd.Lhss.Select(x => (AssignLhs)new SimpleAssignLhs(Token.NoToken,
                            new IdentifierExpr(Token.NoToken, lhsMap[x.DeepAssignedVariable]))).ToList();
                        List<Expr> rhss = assignCmd.Rhss.Select(x => Substituter.Apply(rhsSub, x)).ToList();
                        newCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss, assignCmd.Attributes));
                    }
                    else if (cmd is AssumeCmd)
                    {
                        var sub = Substituter.SubstitutionFromHashtable(
                            GetVarCopiesFromIds(varLastCopyId).ToDictionary(
                                kvp => kvp.Key, kvp => Expr.Ident(kvp.Value) as Expr
                            ));
                        newCmds.Add(new AssumeCmd(cmd.tok,
                            Substituter.Apply(sub, ((AssumeCmd)cmd).Expr)));
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
                // TODO: Add note on this
                if (!IsJoint() || cmds.Count == transitionRelationComputer.transferStackIndex)
                    PopulateIntermediateFrameCopy();
            }

            private void MakeNewCopy(Variable v)
            {
                varLastCopyId[v] = varLastCopyId.ContainsKey(v) ? varLastCopyId[v] + 1 : 0;
                int id = varLastCopyId[v];
                varCopies[id][v] = new Formal(
                    Token.NoToken,
                    new TypedIdent(Token.NoToken, string.Format(copierFormat, v.Name, id), v.TypedIdent.Type),
                    false, null);
            }

            private void SetDefinedVariables()
            {
                definedVariables = new HashSet<Variable>();
                foreach (var v in GetPreStateVars())
                {
                    definedVariables.Add(varCopies[0][v]);
                }
                if (!IgnorePostState)
                {
                    foreach (var v in GetPostStateVars())
                    {
                        definedVariables.Add(varCopies[varLastCopyId[v]][v]);
                    }
                }
            }

            private IEnumerable<Variable> GetPostStateVars()
            {
                return frame.Union(allOutParams).Distinct();
            }

            private IEnumerable<Variable> GetPreStateVars()
            {
                return frame.Union(allInParams).Distinct();
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

            private void EliminateIntermediateVariables()
            {
                SetDefinedVariables();
                varToExpr = new Dictionary<Variable, Expr>();
                foreach (var v in definedVariables)
                {
                    varToExpr[v] = Expr.Ident(v);
                }

                while (TryElimination(new HashSet<Variable>())) { }
            }

            private bool TryElimination(IEnumerable<Variable> extraDefinedVariables)
            {
                bool changed = false;
                var remainingCmds = new List<Cmd>();
                foreach (var cmd in newCmds)
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
                                !VariableCollector.Collect(rhs).Where(x => !(x is BoundVariable)).
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
                newCmds = remainingCmds.Select(cmd => ApplyOnRhss(sub, cmd)).ToList();
                return changed;
            }

            private void ComputeTransitionRelationExpr()
            {
                CalculatePathExpression();
                AddBoundVariablesForRemainingVars(out Dictionary<Variable, Variable> existsVarMap);
                ReplacePreOrPostStateVars();
                TransitionRelationExpr = Expr.And(pathExprs);
                if (IsJoint())
                {
                    ComputeWitnessedTransitionRelationExprs();
                    if (witnessedTransitionRelations.Count > 0)
                    {
                        TransitionRelationExpr = Expr.Or(witnessedTransitionRelations);
                    }
                }
                if (existsVarMap.Any())
                {
                    TransitionRelationExpr = new ExistsExpr(Token.NoToken, existsVarMap.Values.ToList(), TransitionRelationExpr);
                }
            }

            private void ComputeWitnessedTransitionRelationExprs()
            {
                witnessedTransitionRelations = new List<Expr>();
                Dictionary<Variable, List<WitnessFunction>> varToWitnesses = FrameWithWitnesses.
                    Where(x => NotEliminatedVars.Contains(frameIntermediateCopy[x])).
                    ToDictionary(
                        x => frameIntermediateCopy[x],
                        x => transitionRelationComputer.globalVarToWitnesses[(GlobalVariable)x]);
                foreach (var witnessSet in Extensions.CartesianProduct(varToWitnesses.Values))
                {
                    Dictionary<Variable, Expr> witnessSubst = new Dictionary<Variable, Expr>();
                    foreach (Tuple<Variable, WitnessFunction> pair in
                        Enumerable.Zip(varToWitnesses.Keys, witnessSet, Tuple.Create))
                    {
                        WitnessFunction witnessFunction = pair.Item2;
                        List<Expr> args = new List<Expr>();
                        foreach (var arg in witnessFunction.InputArgs)
                        {
                            Expr expr = null;
                            switch (arg.Kind)
                            {
                                case WitnessFunction.InputArgumentKind.FIRST_ARG:
                                    // TODO: Add note on the reason of using second
                                    expr = Expr.Ident(second.Params.
                                        First(x => x.Name == second.Prefix + arg.Name));
                                    break;
                                case WitnessFunction.InputArgumentKind.SECOND_ARG:
                                    expr = Expr.Ident(first.Params.
                                        First(x => x.Name == first.Prefix + arg.Name));
                                    break;
                                case WitnessFunction.InputArgumentKind.PRE_STATE:
                                    expr = ExprHelper.Old(Expr.Ident(
                                        frame.First(x => x.Name == arg.Name)));
                                    break;
                                case WitnessFunction.InputArgumentKind.POST_STATE:
                                    expr = Expr.Ident(frame.First(x => x.Name == arg.Name));
                                    break;
                                default:
                                    Debug.Assert(false);
                                    break;
                            }
                            args.Add(expr);
                        }
                        witnessSubst[pair.Item1] = ExprHelper.FunctionCall(
                                witnessFunction.function, args.ToArray()
                            );
                    }
                    var subst = Substituter.SubstitutionFromHashtable(witnessSubst);
                    witnessedTransitionRelations.Add(
                        Substituter.Apply(subst, TransitionRelationExpr));
                }
            }

            private void ReplacePreOrPostStateVars()
            {
                var preStateSub = GetPreStateVars().
                    ToDictionary<Variable, Variable, Expr>(v => varCopies[0][v],
                        v => new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));

                var frameCopiesSub = preStateSub;
                if (!IgnorePostState)
                {
                    var postStateSub = GetPostStateVars().
                       ToDictionary<Variable, Variable, Expr>(v => varCopies[varLastCopyId[v]][v], v => Expr.Ident(v));

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

            private bool IgnorePostState
            {
                get
                {
                    return transitionRelationComputer.ignorePostState;
                }
            }

            private IEnumerable<Variable> NotEliminatedVars
            {
                get
                {
                    return newCmds.
                    // TODO: Add note about bound variables in here
                        SelectMany(cmd => VariableCollector.Collect(cmd).Where(x => !(x is BoundVariable))).
                        Except(varToExpr.Keys);
                }
            }

            private void AddBoundVariablesForRemainingVars(out Dictionary<Variable, Variable> existsVars)
            {
                var remainingVars = NotEliminatedVars.Except(IntermediateFrameWithWitnesses);
                existsVars = new Dictionary<Variable, Variable>();
                foreach (var v in remainingVars)
                {
                    existsVars[v] = new BoundVariable(Token.NoToken,
                        new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type));
                }
                var varMap = existsVars.ToDictionary(kvp => kvp.Key, kvp => Expr.Ident(kvp.Value) as Expr);
                var varSubst = Substituter.SubstitutionFromHashtable(varMap);
                pathExprs = pathExprs.Select(x => Substituter.Apply(varSubst, x)).ToList();
            }

            private void CalculatePathExpression()
            {
                pathExprs = new List<Expr>();
                foreach (var cmd in newCmds.Where(x => x is AssumeCmd).Cast<AssumeCmd>())
                {
                    FlattenAnd(cmd.Expr, pathExprs);
                }
                foreach (AssignCmd cmd in newCmds.Where(x => x is AssignCmd).Cast<AssignCmd>())
                {
                    for (int k = 0; k < cmd.Lhss.Count; k++)
                    {
                        pathExprs.Add(Expr.Eq(Expr.Ident(cmd.Lhss[k].DeepAssignedVariable), cmd.Rhss[k]));
                    }
                }

                var varMap = varToExpr.ToDictionary(kvp => kvp.Key, kvp => kvp.Value);
                var varSubst = Substituter.SubstitutionFromHashtable(varMap);
                pathExprs = pathExprs.Select(x => Substituter.Apply(varSubst, x)).ToList();
            }

            private static void FlattenAnd(Expr x, List<Expr> xs)
            {
                if (x is NAryExpr naryExpr && naryExpr.Fun.FunctionName == "&&")
                {
                    FlattenAnd(naryExpr.Args[0], xs);
                    FlattenAnd(naryExpr.Args[1], xs);
                }
                else { xs.Add(x); }
            }
        }
    }

    // TODO: Remove or use this visitor
    public class FooCollector : ReadOnlyVisitor
    {
        HashSet<Variable> usedVars;
        HashSet<Variable> boundVars;

        public FooCollector()
        {
            usedVars = new HashSet<Variable>();
            boundVars = new HashSet<Variable>();
        }

        public override BinderExpr VisitBinderExpr(BinderExpr node)
        {
            boundVars.UnionWith(node.Dummies);
            var ret = base.VisitBinderExpr(node);
            boundVars.ExceptWith(node.Dummies);
            return ret;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            usedVars.Add(node.Decl);
            return base.VisitIdentifierExpr(node);
        }
    }

    // TODO: Move this to a proper place
    public static class Extensions
    {
        public static IEnumerable<IEnumerable<T>> CartesianProduct<T>(this IEnumerable<IEnumerable<T>> sequences)
        {
            IEnumerable<IEnumerable<T>> emptyProduct = new[] { Enumerable.Empty<T>() };
            return sequences.Aggregate(
                emptyProduct,
                (accumulator, sequence) =>
                from acc in accumulator
                from item in sequence
                select acc.Concat(new[] { item }));
        }
    }
}
