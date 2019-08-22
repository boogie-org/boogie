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
                Console.WriteLine(cmd);
            }
            IntermediateVariableIntroducer newProgram = new IntermediateVariableIntroducer(cmds, usedVars);
            Console.WriteLine("--- New program:");
            foreach (var cmd in newProgram.newCmds)
            {
                Console.WriteLine(cmd);
            }
        }
    }

    public class IntermediateVariableIntroducer
    {
        private List<Cmd> cmds;
        private Dictionary<Variable, Variable>[] varCopies;
        private Dictionary<Variable, int> varLastCopyId;
        public List<Cmd> newCmds;

        private const string copierFormat = "{0}#{1}";

        public IntermediateVariableIntroducer(List<Cmd> cmds, List<Variable> usedVars)
        {
            this.cmds = cmds;
            this.varCopies = new Dictionary<Variable, Variable>[cmds.Count + 1];
            foreach (int i in Enumerable.Range(0, cmds.Count + 1))
                this.varCopies[i] = new Dictionary<Variable, Variable>();

            this.varLastCopyId = new Dictionary<Variable, int>();
            foreach (var v in usedVars)
            {
                makeNewCopy(v);
            }
            IntroduceIntermediateVars();
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
                        makeNewCopy(v.DeepAssignedVariable);
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

                    List<AssignLhs> lhss = assignCmd.Lhss.Select(x => (AssignLhs) new SimpleAssignLhs(Token.NoToken,
                        new IdentifierExpr(Token.NoToken, lhsMap[x.DeepAssignedVariable]))).ToList();
                    List<Expr> rhss = assignCmd.Rhss.Select(x => Substituter.Apply(rhsSub, x)).ToList();
                    newCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss, assignCmd.Attributes));
                }
                else if (cmd is AssumeCmd)
                {
                    var sub = Substituter.SubstitutionFromHashtable(
                        GetVarCopiesFromIds(varLastCopyId).ToDictionary(
                            kvp => kvp.Key, kvp => (Expr)Expr.Ident(kvp.Value)
                        ));
                    newCmds.Add(new AssertCmd(cmd.tok,
                        Substituter.Apply(sub, ((AssumeCmd) cmd).Expr)));
                }
                else
                {
                    Debug.Assert(false);
                }
            }
        }

        private void makeNewCopy(Variable v)
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
    }
}
