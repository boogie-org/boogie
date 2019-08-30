using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public class NewTransitionRelationComputation
    {
        private readonly ProgramData programData;
        private Stack<Cmd> cmdStack;
        private List<PathTranslation> pathTranslations;

        private NewTransitionRelationComputation(List<Block> blocks, IEnumerable<Variable> inVars,
            IEnumerable<Variable> outVars, IEnumerable<Variable> localVars, IEnumerable<Variable> frame)
            : this(new ProgramData(blocks, inVars, outVars, localVars, frame)) { }

        private NewTransitionRelationComputation(ProgramData programData)
        {
            this.programData = programData;
            EnumeratePaths();
        }

        public static Expr ComputeTransitionRelation(List<Block> blocks, IEnumerable<Variable> inVars,
            IEnumerable<Variable> outVars, IEnumerable<Variable> localVars, IEnumerable<Variable> frame)
        {
            var transitionRelationComputation = new NewTransitionRelationComputation(blocks, inVars, outVars, localVars, frame);
            var transitionRelation = Expr.Or(transitionRelationComputation.pathTranslations.Select(x => x.TransitionRelationExpr));

            ResolutionContext rc = new ResolutionContext(null);
            rc.StateMode = ResolutionContext.State.Two;
            transitionRelation.Resolve(rc);
            transitionRelation.Typecheck(new TypecheckingContext(null));

            return transitionRelation;
        }

        public static Expr ComputeTransitionRelation(Implementation impl, HashSet<Variable> frame)
        {
            return ComputeTransitionRelation(impl.Blocks,
                impl.InParams, impl.OutParams, impl.LocVars, frame);
        }

        private void EnumeratePaths()
        {
            cmdStack = new Stack<Cmd>();
            this.pathTranslations = new List<PathTranslation>();
            Debug.Assert(cmdStack.Count == 0);
            EnumeratePathsRec(programData.Blocks[0]);
            Debug.Assert(cmdStack.Count == 0);
        }

        private void EnumeratePathsRec(Block b)
        {
            int pathSizeAtEntry = cmdStack.Count;

            foreach (Cmd cmd in b.Cmds)
            {
                cmdStack.Push(cmd);
            }
            if (b.TransferCmd is ReturnCmd)
            {
                AddPath();
            }
            else
            {
                GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    EnumeratePathsRec(target);
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
            pathTranslations.Add(new PathTranslation(cmds, programData));
        }

        internal class ProgramData
        {
            internal readonly List<Block> Blocks;
            internal HashSet<Variable> InVars, OutVars, LocalVars, Frame;

            internal ProgramData(List<Block> blocks, IEnumerable<Variable> inVars, IEnumerable<Variable> outVars,
                IEnumerable<Variable> localVars, IEnumerable<Variable> frame)
            {
                this.Blocks = blocks;
                this.InVars = new HashSet<Variable>(inVars);
                this.OutVars = new HashSet<Variable>(outVars);
                this.LocalVars = new HashSet<Variable>(localVars);
                this.Frame = new HashSet<Variable>(frame);
            }
        }

        internal class PathTranslation
        {
            private readonly List<Cmd> cmds;
            private readonly ProgramData programData;
            private List<Cmd> newCmds;
            private Dictionary<Variable, Variable>[] varCopies;
            private Dictionary<Variable, int> varLastCopyId;
            private HashSet<Variable> definedVariables;
            private Dictionary<Variable, Expr> varToExpr;
            private List<Expr> pathExprs;
            internal Expr TransitionRelationExpr;

            private const string copierFormat = "{0}#{1}";

            private IEnumerable<Variable> UsedVariables
            {
                get
                {
                    return programData.InVars.
                        Union(programData.OutVars).
                        Union(programData.LocalVars).
                        Union(programData.Frame).Distinct();
                }
            }

            internal PathTranslation(List<Cmd> cmds, ProgramData programData)
            {
                this.cmds = cmds;
                this.programData = programData;
                this.varCopies = new Dictionary<Variable, Variable>[cmds.Count + 1];
                foreach (int i in Enumerable.Range(0, cmds.Count + 1))
                    this.varCopies[i] = new Dictionary<Variable, Variable>();

                this.varLastCopyId = new Dictionary<Variable, int>();
                foreach (var v in UsedVariables)
                {
                    MakeNewCopy(v);
                }
                IntroduceIntermediateVars();
                EliminateIntermediateVariables();
                ComputeTransitionRelationExpr();
            }

            private Dictionary<Variable, Variable> GetVarCopiesFromIds(Dictionary<Variable, int> varCopyId)
            {
                return varCopyId.ToDictionary(kvp => kvp.Key, kvp => varCopies[kvp.Value][kvp.Key]);
            }

            private void IntroduceIntermediateVars()
            {
                newCmds = new List<Cmd>();
                foreach (var cmd in cmds)
                {
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
                        if (QKeyValue.FindBoolAttribute(assignCmd.Attributes, "backward"))
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
                    else
                    {
                        Debug.Assert(false);
                    }
                }
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
                foreach (var v in GetPostStateVars())
                {
                    definedVariables.Add(varCopies[varLastCopyId[v]][v]);
                }
            }

            private IEnumerable<Variable> GetPostStateVars()
            {
                return programData.Frame.Union(programData.OutVars).Distinct();
            }

            private IEnumerable<Variable> GetPreStateVars()
            {
                return programData.Frame.Union(programData.InVars).Distinct();
            }

            private static Cmd ApplyOnRhss(Substitution sub, Cmd cmd)
            {
                if (cmd is AssignCmd)
                {
                    var assignCmd = (AssignCmd)cmd;
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

                bool done = false;
                while (!done)
                {
                    done = true;
                    var remainingCmds = new List<Cmd>();
                    foreach (var cmd in newCmds)
                    {
                        if (cmd is AssignCmd)
                        {
                            AssignCmd assignCmd = (AssignCmd)cmd;

                            var lhss = new List<AssignLhs>();
                            var rhss = new List<Expr>();
                            for (int k = 0; k < assignCmd.Lhss.Count; k++)
                            {
                                var lhs = assignCmd.Lhss[k];
                                var rhs = assignCmd.Rhss[k];
                                Variable assignedVar = lhs.DeepAssignedVariable;
                                if (!varToExpr.ContainsKey(assignedVar) &&
                                    !VariableCollector.Collect(rhs).Where(x => !(x is BoundVariable)).
                                        Except(varToExpr.Keys).Any())
                                {
                                    varToExpr[assignedVar] = rhs;
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
                }
            }

            private void ComputeTransitionRelationExpr()
            {
                CalculatePathExpression();
                Dictionary<Variable, Variable> existsVarMap;
                AddBoundVariablesForRemainingVars(out existsVarMap);
                ReplacePreOrPostStateVars();
                TransitionRelationExpr = Expr.And(pathExprs);
                if (existsVarMap.Any())
                {
                    TransitionRelationExpr = new ExistsExpr(Token.NoToken, existsVarMap.Values.ToList(), TransitionRelationExpr);
                }
            }

            private void ReplacePreOrPostStateVars()
            {
                var preStateSub = GetPreStateVars().
                    ToDictionary<Variable, Variable, Expr>(v => varCopies[0][v],
                        v => new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                var postStateSub = GetPostStateVars().
                    ToDictionary<Variable, Variable, Expr>(v => varCopies[varLastCopyId[v]][v], v => Expr.Ident(v));

                var notModifiedVars = new HashSet<Variable>(preStateSub.Keys.Intersect(postStateSub.Keys));
                foreach (var v in notModifiedVars)
                {
                    pathExprs.Add(Expr.Eq(preStateSub[v], postStateSub[v]));
                    postStateSub.Remove(v);
                }

                var finalSub = Substituter.SubstitutionFromHashtable(
                    Enumerable.Union(postStateSub, preStateSub).ToDictionary(k => k.Key, v => v.Value));
                pathExprs = pathExprs.Select(x => Substituter.Apply(finalSub, x)).ToList();
            }

            private void AddBoundVariablesForRemainingVars(out Dictionary<Variable, Variable> existsVars)
            {
                var remainingVars = newCmds.SelectMany(cmd => VariableCollector.Collect(cmd).Where(x => !(x is BoundVariable))).Except(varToExpr.Keys);
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
}
