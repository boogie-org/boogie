using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public class NewTransitionRelatinComputation
    {
        private AtomicActionCopy action;
        private Stack<Cmd> cmdStack;
        private List<Variable> usedVars;

        public NewTransitionRelatinComputation(AtomicActionCopy action)
        {
            this.action = action;
            this.cmdStack = new Stack<Cmd>();
            this.usedVars = action.impl.LocVars.
                Union(action.impl.InParams).
                Union(action.impl.OutParams).
                Union(action.gateUsedGlobalVars).
                Union(action.modifiedGlobalVars).
                Union(action.actionUsedGlobalVars).
                Distinct().ToList();
            EnumeratePaths();
        }

        private void EnumeratePaths()
        {
            Debug.Assert(cmdStack.Count == 0);
            EnumeratePathsRec(this.action.impl.Blocks[0]);
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
            Console.WriteLine("###################################\nNew path: ");
            Console.WriteLine("--- Initial program:");
            foreach (var cmd in cmds)
            {
                Console.Write(cmd);
            }
            Console.WriteLine("____________________");
            TranslatePath newProgram = new TranslatePath(action, cmds, usedVars);
            Console.WriteLine("###################################");
        }
    }

    public class TranslatePath
    {
        private AtomicActionCopy action;
        private List<Cmd> cmds;
        public List<Cmd> newCmds;
        private Dictionary<Variable, Variable>[] varCopies;
        private Dictionary<Variable, int> varLastCopyId;
        private List<Variable> definedVariables;
        Dictionary<Variable, Expr> varToExpr;
        public List<Expr> pathExprs;

        private const string copierFormat = "{0}#{1}";

        public TranslatePath(AtomicActionCopy action, List<Cmd> cmds, List<Variable> usedVars)
        {
            this.cmds = cmds;
            this.action = action;
            this.varCopies = new Dictionary<Variable, Variable>[cmds.Count + 1];
            foreach (int i in Enumerable.Range(0, cmds.Count + 1))
                this.varCopies[i] = new Dictionary<Variable, Variable>();

            this.varLastCopyId = new Dictionary<Variable, int>();
            foreach (var v in usedVars)
            {
                MakeNewCopy(v);
            }
            IntroduceIntermediateVars();
            Console.WriteLine("After Introducing Intermediate Vars:");
            PrintCmds();
            Console.WriteLine("____________________");
            EliminateIntermediateVariables();
            Console.WriteLine("Final program:");
            PrintCmds();
            ComputePathExprs();
            Console.WriteLine("____________________");
            Console.WriteLine("Transition relation:\n" + Expr.And(pathExprs));
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
                            kvp => kvp.Key, kvp => (Expr) Expr.Ident(kvp.Value)
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
                            kvp => kvp.Key, kvp => (Expr) Expr.Ident(kvp.Value)
                        ));
                    newCmds.Add(new AssumeCmd(cmd.tok,
                        Substituter.Apply(sub, ((AssumeCmd) cmd).Expr)));
                }
                else
                {
                    Debug.Assert(false);
                }
            }
        }

        private void MakeNewCopy(Variable v)
        {
            if (!varLastCopyId.ContainsKey(v))
            {
                varLastCopyId[v] = 0;
            }
            else
            {
                varLastCopyId[v] = varLastCopyId[v] + 1;
            }

            int id = varLastCopyId[v];
            varCopies[id][v] = new Formal(
                Token.NoToken,
                new TypedIdent(Token.NoToken, string.Format(copierFormat, v.Name, id), v.TypedIdent.Type),
                false, null);
        }

        private void SetDefinedVariables()
        {
            definedVariables = new List<Variable>();
            IEnumerable<Variable> preStateVars = GetPreStateVars();
            foreach (var v in preStateVars)
            {
                definedVariables.Add(varCopies[0][v]);
            }
            var postStateVars = GetPostStateVars();
            foreach (var v in postStateVars)
            {
                definedVariables.Add(varCopies[varLastCopyId[v]][v]);
            }
        }

        private IEnumerable<Variable> GetPostStateVars()
        {
            return action.modifiedGlobalVars.
                Union(action.impl.OutParams);
        }

        private IEnumerable<Variable> GetPreStateVars()
        {
            return action.actionUsedGlobalVars.
                Union(action.modifiedGlobalVars).
                Union(action.impl.InParams);
        }

        private static Cmd ApplyOnRhss(Substitution sub, Cmd cmd)
        {
            if (cmd is AssignCmd)
            {
                var assignCmd = (AssignCmd) cmd;
                return new AssignCmd(cmd.tok,
                    assignCmd.Lhss,
                    assignCmd.Rhss.Select(x => Substituter.Apply(sub, x)).ToList(),
                    assignCmd.Attributes);
            }
            return Substituter.Apply(sub, cmd);
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
                        AssignCmd assignCmd = (AssignCmd) cmd;

                        var lhss = new List<AssignLhs>();
                        var rhss = new List<Expr>();
                        for (int k = 0; k < assignCmd.Lhss.Count; k++)
                        {
                            var lhs = assignCmd.Lhss[k];
                            var rhs = assignCmd.Rhss[k];
                            Variable assignedVar = lhs.DeepAssignedVariable;
                            if (!varToExpr.ContainsKey(assignedVar) &&
                                !VariableCollector.Collect(rhs).Where(x => x is Variable).
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

        private void ComputePathExprs()
        {
            if (newCmds.Select(cmd => VariableCollector.Collect(cmd).Except(varToExpr.Keys).Any()).
                   Aggregate(false, (v1, v2) => v1 || v2))
            {
                Console.WriteLine("Failed to eliminate intermediate variable.");
                Debug.Assert(false);
            }

            // Add assume statements
            pathExprs = new List<Expr>();
            foreach (var cmd in newCmds.Where(x => x is AssumeCmd).Cast<AssumeCmd>())
            {
                FlattenAnd(cmd.Expr, pathExprs);
            }

            // Add equality conditions for defined lhs assignments
            foreach (AssignCmd cmd in newCmds.Where(x => x is AssignCmd).Cast<AssignCmd>())
            {
                for (int k = 0; k < cmd.Lhss.Count; k++)
                {
                    pathExprs.Add(Expr.Eq(varToExpr[cmd.Lhss[k].DeepAssignedVariable], cmd.Rhss[k]));
                }
            }

            var preStateSub = GetPreStateVars().
                ToDictionary(v => varCopies[0][v],
                    v => (Expr) new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
            var postStateSub = GetPostStateVars().
                ToDictionary(v => varCopies[varLastCopyId[v]][v], v => (Expr) Expr.Ident(v));
            var finalSub = Substituter.SubstitutionFromHashtable(
                Enumerable.Union(postStateSub, preStateSub).ToDictionary(k => k.Key, v => v.Value));
            pathExprs = pathExprs.Select(x => Substituter.Apply(finalSub, x)).ToList();
        }

        private static void FlattenAnd(Expr x, List<Expr> xs)
        {
            if (x is NAryExpr naryExpr && naryExpr.Fun.FunctionName == "&&")
            {
                FlattenAnd(naryExpr.Args[0], xs);
                FlattenAnd(naryExpr.Args[1], xs);
            }
            else
            {
                xs.Add(x);
            }
        }

        private void PrintCmds()
        {
            Console.WriteLine("```");
            foreach (var cmd in newCmds)
                Console.Write(cmd);
            Console.WriteLine("```");
        }
    }
}
