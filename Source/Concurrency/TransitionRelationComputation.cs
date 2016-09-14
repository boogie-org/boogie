using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

namespace Microsoft.Boogie
{

    public class TransitionRelationComputation
    {
        private Program program;
        private AtomicActionInfo first;  // corresponds to that*
        private AtomicActionInfo second; // corresponds to this*
        private Stack<Cmd> cmdStack;
        private List<PathInfo> paths;
        private HashSet<Variable> frame;
        private HashSet<Variable> postExistVars;

        private Dictionary<Variable, Variable> existsVars;
        private HashSet<Variable> firstExistsVars;
        private HashSet<Variable> secondExistsVars;

        public TransitionRelationComputation(Program program, AtomicActionInfo second, HashSet<Variable> frame, HashSet<Variable> postExistVars)
            : this(program, null, second, frame, postExistVars) { }

        public TransitionRelationComputation(Program program, AtomicActionInfo first, AtomicActionInfo second, HashSet<Variable> frame, HashSet<Variable> postExistVars)
        {
            this.program = program;
            this.first = first;
            this.second = second;
            this.postExistVars = postExistVars;
            this.frame = frame;

            this.existsVars = new Dictionary<Variable, Variable>();
            this.firstExistsVars = new HashSet<Variable>(
                first != null ? first.thatOutParams.Union(first.thatAction.LocVars)
                              : Enumerable.Empty<Variable>());
            this.secondExistsVars = new HashSet<Variable>(second.thisOutParams.Union(second.thisAction.LocVars));

            this.cmdStack = new Stack<Cmd>();
            this.paths = new List<PathInfo>();

            EnumeratePaths();
        }

        private bool IsExistsVar(Variable v)
        {
            return firstExistsVars.Concat(secondExistsVars).Contains(v);
        }

        private void PopulateExistsVars(Variable v)
        {
            if (existsVars.ContainsKey(v)) return;
            existsVars[v] = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "#tmp_" + existsVars.Count, v.TypedIdent.Type));
        }

        private Function TriggerFunction(Variable v)
        {
            PopulateExistsVars(v);
            if (firstExistsVars.Contains(v))
            {
                return first.TriggerFunction(v);
            }
            else if (secondExistsVars.Contains(v))
            {
                return second.TriggerFunction(v);
            }
            else
            {
                Debug.Assert(false);
                return null;
            }
        }

        public List<Cmd> TriggerAssumes()
        {
            return existsVars.Keys.Select(v =>
                new AssumeCmd(Token.NoToken,
                    new NAryExpr(Token.NoToken,
                        new FunctionCall(TriggerFunction(v)),
                        new Expr[] { Expr.Ident(v) })))
                .ToList<Cmd>();
        }

        private void Substitute(Dictionary<Variable, Expr> map, ref List<Expr> pathExprs, ref Dictionary<Variable, Expr> varToExpr)
        {
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            List<Expr> oldPathExprs = pathExprs;
            pathExprs = new List<Expr>();
            foreach (Expr pathExpr in oldPathExprs)
            {
                pathExprs.Add(Substituter.Apply(subst, pathExpr));
            }
            Dictionary<Variable, Expr> oldVarToExpr = varToExpr;
            varToExpr = new Dictionary<Variable, Expr>();
            foreach (Variable v in oldVarToExpr.Keys)
            {
                varToExpr[v] = Substituter.Apply(subst, oldVarToExpr[v]);
            }
        }

        private struct PathInfo
        {
            public Dictionary<Variable, Expr> varToExpr;
            public List<Expr> pathExprs;

            public PathInfo(Dictionary<Variable, Expr> varToExpr, List<Expr> pathExprs)
            {
                this.varToExpr = varToExpr;
                this.pathExprs = pathExprs;
            }
        }

        private void FlattenAnd(Expr x, List<Expr> xs)
        {
            NAryExpr naryExpr = x as NAryExpr;
            if (naryExpr != null && naryExpr.Fun.FunctionName == "&&")
            {
                FlattenAnd(naryExpr.Args[0], xs);
                FlattenAnd(naryExpr.Args[1], xs);
            }
            else
            {
                xs.Add(x);
            }
        }

        private void AddPath()
        {
            Dictionary<Variable, Expr> varToExpr =
                frame
                .Concat(first != null ? first.thatOutParams : Enumerable.Empty<Variable>())
                .Concat(second.thisOutParams)
                .ToDictionary(v => v, v => Expr.Ident(v) as Expr);

            List<Expr> pathExprs = new List<Expr>();
            foreach (Cmd cmd in cmdStack)
            {
                if (cmd is AssumeCmd)
                {
                    AssumeCmd assumeCmd = cmd as AssumeCmd;
                    FlattenAnd(assumeCmd.Expr, pathExprs);
                }
                else if (cmd is AssignCmd)
                {
                    AssignCmd assignCmd = (cmd as AssignCmd).AsSimpleAssignCmd;
                    Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                    for (int k = 0; k < assignCmd.Lhss.Count; k++)
                    {
                        map[assignCmd.Lhss[k].DeepAssignedVariable] = assignCmd.Rhss[k];
                    }
                    Substitute(map, ref pathExprs, ref varToExpr);
                }
                else
                {
                    Debug.Assert(false);
                }
            }
            paths.Add(new PathInfo(varToExpr, pathExprs));
        }

        private Expr CalculatePathCondition(PathInfo path)
        {
            HashSet<Variable> allExistsVars = new HashSet<Variable>(firstExistsVars.Union(secondExistsVars));
            HashSet<Variable> usedExistsVars = new HashSet<Variable>();
            Dictionary<Variable, Expr> existsSubstitutionMap = new Dictionary<Variable, Expr>();
            List<Expr> inferredSelectEqualities = new List<Expr>();
            foreach (Variable v in path.varToExpr.Keys.Except(postExistVars))
            {
                var expr = path.varToExpr[v];
                usedExistsVars.UnionWith(VariableCollector.Collect(expr).Intersect(allExistsVars));
                IdentifierExpr ie = expr as IdentifierExpr;
                if (ie != null && IsExistsVar(ie.Decl) && !existsSubstitutionMap.ContainsKey(ie.Decl))
                {
                    existsSubstitutionMap[ie.Decl] = Expr.Ident(v);
                }
                else if (IsMapStoreExpr(expr))
                {
                    inferredSelectEqualities.Add(GenerateEqualityWithSelect(expr as NAryExpr, Expr.Ident(v)));
                }
            }

            foreach (Expr expr in path.pathExprs)
            {
                usedExistsVars.UnionWith(VariableCollector.Collect(expr).Intersect(allExistsVars));
            }
            InferSubstitution(allExistsVars, existsSubstitutionMap, path.pathExprs, inferredSelectEqualities);

            List<Expr> triggerExprs = new List<Expr>();
            List<Variable> quantifiedVars = new List<Variable>();
            foreach (var v in usedExistsVars.Except(existsSubstitutionMap.Keys))
            {
                var triggerFun = TriggerFunction(v); // this call populates existsVars[v]
                var quantifiedVar = existsVars[v];
                triggerExprs.Add(
                    new NAryExpr(Token.NoToken, 
                        new FunctionCall(triggerFun), 
                        new Expr[] { Expr.Ident(quantifiedVar) }));
                quantifiedVars.Add(quantifiedVar);
                existsSubstitutionMap[v] = Expr.Ident(quantifiedVar);
            }

            Substitution subst = Substituter.SubstitutionFromHashtable(existsSubstitutionMap);
            List<Expr> returnExprs = new List<Expr>();

            foreach (Variable v in path.varToExpr.Keys.Except(postExistVars))
            {
                Expr withOldExpr = MyDuplicator.Duplicate(path.varToExpr[v]);
                var substExpr = Expr.Eq(Expr.Ident(v), Substituter.Apply(subst, withOldExpr));
                substExpr.Type = Type.Bool;
                returnExprs.Add(substExpr);
            }

            foreach (Expr x in path.pathExprs)
            {
                var withOldExpr = MyDuplicator.Duplicate(x);
                returnExprs.Add(Substituter.Apply(subst, withOldExpr));
            }

            var returnExpr = Expr.And(returnExprs);
            if (quantifiedVars.Count > 0)
            {
                if (first == null)
                {
                    returnExpr = new ExistsExpr(Token.NoToken, quantifiedVars, returnExpr);
                }
                else
                {
                    returnExpr = new ExistsExpr(Token.NoToken, 
                                    quantifiedVars, 
                                    new Trigger(Token.NoToken, true, triggerExprs), 
                                    returnExpr);
                }
            }
            return returnExpr;
        }

        Expr GenerateEqualityWithSelect(NAryExpr mapStoreExpr, Expr otherExpr)
        {
            List<Expr> args = new List<Expr>();
            int i = 1;
            for (; i < mapStoreExpr.Args.Count - 1; i++)
            {
                args.Add(mapStoreExpr.Args[i]);
            }
            Expr expr = Expr.Eq(mapStoreExpr.Args[i], Expr.Select(otherExpr, args));
            expr.Resolve(new ResolutionContext(null));
            return expr;
        }

        private bool IsMapStoreExpr(Expr expr)
        {
            NAryExpr naryExpr = expr as NAryExpr;
            if (naryExpr == null)
            {
                return false;
            }
            return naryExpr.Fun is MapStore;
        }

        private IEnumerable<NAryExpr> FilterEqualities(IEnumerable<Expr> exprs)
        {
            return exprs.OfType<NAryExpr>().Where(x => x.Fun.FunctionName == "==");
        }

        void InferSubstitution(HashSet<Variable> allExistsVars, Dictionary<Variable, Expr> existsSubstitutionMap, List<Expr> pathExprs, List<Expr> inferredSelectEqualities)
        {
            foreach (var eqExpr in FilterEqualities(pathExprs))
            {
                Expr arg0 = eqExpr.Args[0];
                Expr arg1 = eqExpr.Args[1];
                if (IsMapStoreExpr(arg0))
                {
                    inferredSelectEqualities.Add(GenerateEqualityWithSelect(arg0 as NAryExpr, arg1));
                }
                if (IsMapStoreExpr(arg1))
                {
                    inferredSelectEqualities.Add(GenerateEqualityWithSelect(arg1 as NAryExpr, arg0));
                }
            }
            
            Dictionary<Variable, Expr> pendingMap = new Dictionary<Variable, Expr>();
            foreach (var eqExpr in FilterEqualities(pathExprs.Union(inferredSelectEqualities)))
            {
                Variable eVar = null;
                Expr eVarSubstExpr = null;
                IdentifierExpr arg0 = eqExpr.Args[0] as IdentifierExpr;
                IdentifierExpr arg1 = eqExpr.Args[1] as IdentifierExpr;
                if (arg0 != null && IsExistsVar(arg0.Decl))
                {
                    eVar = arg0.Decl;
                    eVarSubstExpr = eqExpr.Args[1];
                }
                else if (arg1 != null && IsExistsVar(arg1.Decl))
                {
                    eVar = arg1.Decl;
                    eVarSubstExpr = eqExpr.Args[0];
                }
                if (eVar == null || existsSubstitutionMap.ContainsKey(eVar)) continue;
                PendingPropagate(allExistsVars, existsSubstitutionMap, eVar, eVarSubstExpr, pendingMap);
            }

            while (pendingMap.Count != 0)
            {
                Dictionary<Variable, Expr> newPendingMap = new Dictionary<Variable, Expr>();
                foreach (var v in pendingMap.Keys)
                {
                    PendingPropagate(allExistsVars, existsSubstitutionMap, v, pendingMap[v], newPendingMap);
                }
                if (pendingMap.Count == newPendingMap.Count) break;
                pendingMap = newPendingMap;
            }
        }

        private void PendingPropagate(HashSet<Variable> allExistsVars, Dictionary<Variable, Expr> existsSubstitutionMap, Variable eVar, Expr eVarSubstExpr, Dictionary<Variable, Expr> pendingMap)
        {
            var usedExistsVars = VariableCollector.Collect(eVarSubstExpr).Intersect(allExistsVars);
            if (usedExistsVars.Count() == 0)
            {
                existsSubstitutionMap[eVar] = eVarSubstExpr;
            }
            else if (usedExistsVars.Except(existsSubstitutionMap.Keys).Count() == 0)
            {
                Substitution subst = Substituter.SubstitutionFromHashtable(existsSubstitutionMap);
                existsSubstitutionMap[eVar] = Substituter.Apply(subst, eVarSubstExpr);
            }
            else
            {
                pendingMap[eVar] = eVarSubstExpr;
            }
        }

        public Expr TransitionRelationCompute(bool withOriginalInOutVariables = false)
        {
            Expr transitionRelation = Expr.Or(paths.Select(p => CalculatePathCondition(p)));

            ResolutionContext rc = new ResolutionContext(null);
            rc.StateMode = ResolutionContext.State.Two;
            transitionRelation.Resolve(rc);
            transitionRelation.Typecheck(new TypecheckingContext(null));

            if (withOriginalInOutVariables)
            {
                Dictionary<Variable, Expr> invertedMap = new Dictionary<Variable, Expr>();
                if (first != null)
                {
                    foreach (var x in first.thatMap)
                    {
                        invertedMap[((IdentifierExpr)x.Value).Decl] = Expr.Ident(x.Key);
                    }
                }
                if (second != null)
                {
                    foreach (var x in second.thisMap)
                    {
                        invertedMap[((IdentifierExpr)x.Value).Decl] = Expr.Ident(x.Key);
                    }
                }
                Substitution subst = Substituter.SubstitutionFromHashtable(invertedMap);
                return Substituter.Apply(subst, transitionRelation);
            }
            else
            {
                return transitionRelation;
            }
        }

        private void EnumeratePaths()
        {
            EnumeratePathsRec(this.second.thisAction.Blocks[0], false);
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
                if (first == null || inFirst)
                {
                    AddPath();
                }
                else
                {
                    EnumeratePathsRec(first.thatAction.Blocks[0], true);
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

        private sealed class MyDuplicator : Duplicator
        {
            public static Expr Duplicate(Expr expr)
            {
                return new MyDuplicator().VisitExpr(expr);
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                IdentifierExpr ret = (IdentifierExpr)base.VisitIdentifierExpr(node);
                if (ret.Decl is GlobalVariable)
                {
                    return new OldExpr(Token.NoToken, ret);
                }
                else
                {
                    return ret;
                }
            }
        }
    }
}
