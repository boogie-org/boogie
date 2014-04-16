using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public enum MoverType
    {
        Top,
        Atomic,
        Right,
        Left,
        Both
    }

    public class ActionInfo
    {
        public Procedure proc;
        public Ensures ensures;
        public MoverType moverType;
        public int phaseNum;
        public int availableUptoPhaseNum;
        public List<AssertCmd> thisGate;
        public CodeExpr thisAction;
        public List<Variable> thisInParams;
        public List<Variable> thisOutParams;
        public List<AssertCmd> thatGate;
        public CodeExpr thatAction;
        public List<Variable> thatInParams;
        public List<Variable> thatOutParams;
        public HashSet<Variable> usedGlobalVars;
        public HashSet<Variable> modifiedGlobalVars;
        public HashSet<Variable> gateUsedGlobalVars;
        public bool hasAssumeCmd;

        public bool CommutesWith(ActionInfo actionInfo)
        {
            if (this.modifiedGlobalVars.Intersect(actionInfo.usedGlobalVars).Count() > 0)
                return false;
            if (this.usedGlobalVars.Intersect(actionInfo.modifiedGlobalVars).Count() > 0)
                return false;
            return true;
        }

        public bool IsRightMover
        {
            get { return moverType == MoverType.Right || moverType == MoverType.Both; }
        }

        public bool IsLeftMover
        {
            get { return moverType == MoverType.Left || moverType == MoverType.Both; }
        }

        public ActionInfo(Procedure proc, Ensures ensures, MoverType moverType, int phaseNum, int availableUptoPhaseNum)
        {
            CodeExpr codeExpr = ensures.Condition as CodeExpr;
            this.proc = proc;
            this.ensures = ensures;
            this.moverType = moverType;
            this.phaseNum = phaseNum;
            this.availableUptoPhaseNum = availableUptoPhaseNum;
            this.thisGate = new List<AssertCmd>();
            this.thisAction = codeExpr;
            this.thisInParams = new List<Variable>();
            this.thisOutParams = new List<Variable>();
            this.thatGate = new List<AssertCmd>();
            this.thatInParams = new List<Variable>();
            this.thatOutParams = new List<Variable>();
            this.hasAssumeCmd = false;
            
            foreach (Block block in codeExpr.Blocks)
            {
                block.Cmds.ForEach(x => this.hasAssumeCmd = this.hasAssumeCmd || x is AssumeCmd);
            }

            var cmds = thisAction.Blocks[0].Cmds;
            for (int i = 0; i < cmds.Count; i++)
            {
                AssertCmd assertCmd = cmds[i] as AssertCmd;
                if (assertCmd == null) break;
                thisGate.Add(assertCmd);
                cmds[i] = new AssumeCmd(assertCmd.tok, assertCmd.Expr);
            }

            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            foreach (Variable x in proc.InParams)
            {
                this.thisInParams.Add(x);
                Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), true, x.Attributes);
                this.thatInParams.Add(y);
                map[x] = Expr.Ident(y);
            }
            foreach (Variable x in proc.OutParams)
            {
                this.thisOutParams.Add(x);
                Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), false, x.Attributes);
                this.thatOutParams.Add(y);
                map[x] = Expr.Ident(y);
            }
            List<Variable> thatLocVars = new List<Variable>();
            foreach (Variable x in thisAction.LocVars)
            {
                Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), false);
                map[x] = Expr.Ident(y);
                thatLocVars.Add(y);
            }
            Contract.Assume(proc.TypeParameters.Count == 0);
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            foreach (AssertCmd assertCmd in thisGate)
            {
                thatGate.Add((AssertCmd)Substituter.Apply(subst, assertCmd));
            }
            Dictionary<Block, Block> blockMap = new Dictionary<Block, Block>();
            List<Block> thatBlocks = new List<Block>();
            foreach (Block block in thisAction.Blocks)
            {
                List<Cmd> otherCmds = new List<Cmd>();
                foreach (Cmd cmd in block.Cmds)
                {
                    otherCmds.Add(Substituter.Apply(subst, cmd));
                }
                Block thatBlock = new Block();
                thatBlock.Cmds = otherCmds;
                thatBlock.Label = "that_" + block.Label;
                block.Label = "this_" + block.Label;
                thatBlocks.Add(thatBlock);
                blockMap[block] = thatBlock;
                if (block.TransferCmd is GotoCmd)
                {
                    GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                    for (int i = 0; i < gotoCmd.labelNames.Count; i++)
                    {
                        gotoCmd.labelNames[i] = "this_" + gotoCmd.labelNames[i];
                    }
                }
            }
            foreach (Block block in thisAction.Blocks)
            {
                if (block.TransferCmd is ReturnExprCmd)
                {
                    block.TransferCmd = new ReturnCmd(block.TransferCmd.tok);
                    blockMap[block].TransferCmd = new ReturnCmd(block.TransferCmd.tok);
                    continue;
                }
                List<Block> thatGotoCmdLabelTargets = new List<Block>();
                List<string> thatGotoCmdLabelNames = new List<string>();
                GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    thatGotoCmdLabelTargets.Add(blockMap[target]);
                    thatGotoCmdLabelNames.Add(blockMap[target].Label);
                }
                blockMap[block].TransferCmd = new GotoCmd(block.TransferCmd.tok, thatGotoCmdLabelNames, thatGotoCmdLabelTargets);
            }
            this.thatAction = new CodeExpr(thatLocVars, thatBlocks);

            {
                VariableCollector collector = new VariableCollector();
                collector.Visit(codeExpr);
                this.usedGlobalVars = new HashSet<Variable>(collector.usedVars.Where(x => x is GlobalVariable));
            }

            List<Variable> modifiedVars = new List<Variable>();
            foreach (Block block in codeExpr.Blocks)
            {
                block.Cmds.ForEach(cmd => cmd.AddAssignedVariables(modifiedVars));
            }
            this.modifiedGlobalVars = new HashSet<Variable>(modifiedVars.Where(x => x is GlobalVariable));

            {
                VariableCollector collector = new VariableCollector();
                this.thisGate.ForEach(assertCmd => collector.Visit(assertCmd));
                this.gateUsedGlobalVars = new HashSet<Variable>(collector.usedVars.Where(x => x is GlobalVariable));
            }
        }
    }

    public class MoverTypeChecker : ReadOnlyVisitor
    {
        public int FindPhaseNumber(Procedure proc)
        {
            if (procToActionInfo.ContainsKey(proc))
                return procToActionInfo[proc].phaseNum;
            else
                return int.MaxValue;
        }

        CheckingContext checkingContext;
        public int errorCount;
        Dictionary<Variable, int> qedGlobalVariables;
        Procedure enclosingProc;
        public Dictionary<Procedure, ActionInfo> procToActionInfo;
        public Program program;
        public HashSet<int> allPhaseNums;
        bool inAtomicSpecification;
        bool inSpecification;
        int minPhaseNum;

        public void TypeCheck()
        {
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc == null) continue;
                foreach (Ensures e in proc.Ensures)
                {
                    int phaseNum, availableUptoPhaseNum;
                    MoverType moverType = MoverCheck.GetMoverType(e, out phaseNum, out availableUptoPhaseNum);
                    if (moverType == MoverType.Top) continue;
                    CodeExpr codeExpr = e.Condition as CodeExpr;
                    if (codeExpr == null)
                    {
                        Error(e, "An atomic action must be a CodeExpr");
                        continue;
                    }
                    if (procToActionInfo.ContainsKey(proc))
                    {
                        Error(proc, "A procedure can have at most one atomic action");
                        continue;
                    }
                    if (phaseNum >= availableUptoPhaseNum)
                    {
                        Error(proc, "Available at phase number should be less than available up to phase number");
                        continue;
                    }
                    if (phaseNum != int.MaxValue)
                    {
                        allPhaseNums.Add(phaseNum);
                    }
                    procToActionInfo[proc] = new ActionInfo(proc, e, moverType, phaseNum, availableUptoPhaseNum);
                }
            }
            this.VisitProgram(program);
#if QED
            YieldTypeChecker.PerformYieldSafeCheck(this);
#endif
        }

        public MoverTypeChecker(Program program)
        {
            this.qedGlobalVariables = new Dictionary<Variable, int>();
            foreach (var g in program.GlobalVariables())
            {
                if (QKeyValue.FindBoolAttribute(g.Attributes, "qed"))
                {
                    this.qedGlobalVariables.Add(g, int.MaxValue);
                    g.Attributes = OwickiGries.RemoveQedAttribute(g.Attributes);
                }
                else
                {
                    int phaseNum = QKeyValue.FindIntAttribute(g.Attributes, "qed", int.MaxValue);
                    if (phaseNum == int.MaxValue) continue;
                    this.qedGlobalVariables.Add(g, phaseNum);
                    g.Attributes = OwickiGries.RemoveQedAttribute(g.Attributes);
                }
            }
            this.procToActionInfo = new Dictionary<Procedure, ActionInfo>();
            this.allPhaseNums = new HashSet<int>();
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.program = program;
            this.enclosingProc = null;
            this.inAtomicSpecification = false;
            this.inSpecification = false;
            this.minPhaseNum = int.MaxValue;
        }
        public override Implementation VisitImplementation(Implementation node)
        {
            this.enclosingProc = node.Proc;
            return base.VisitImplementation(node);
        }
        public override Procedure VisitProcedure(Procedure node)
        {
            this.enclosingProc = node;
            return base.VisitProcedure(node);
        }
        public override Cmd VisitCallCmd(CallCmd node)
        {
            if (!node.IsAsync)
            {
                int enclosingProcPhaseNum = FindPhaseNumber(enclosingProc);
                int calleePhaseNum = FindPhaseNumber(node.Proc);
                if (enclosingProcPhaseNum == int.MaxValue)
                {

                }
                else if (calleePhaseNum == int.MaxValue)
                {
                    Error(node, "An atomic procedure cannot call a non-atomic procedure");
                }
                else if (enclosingProcPhaseNum <= calleePhaseNum)
                {
                    Error(node, "The phase of the caller procedure must be greater than the phase of the callee");
                }
                else if (procToActionInfo[node.Proc].availableUptoPhaseNum < enclosingProcPhaseNum)
                {
                    Error(node, "The callee is not available in the phase of the caller procedure");
                }
            }
            return base.VisitCallCmd(node);
        }
        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            int maxCalleePhaseNum = 0;
            foreach (CallCmd iter in node.CallCmds)
            {
                int calleePhaseNum = FindPhaseNumber(iter.Proc);
                if (calleePhaseNum > maxCalleePhaseNum)
                    maxCalleePhaseNum = calleePhaseNum;
            }
            int enclosingProcPhaseNum = FindPhaseNumber(enclosingProc);
            if (enclosingProcPhaseNum > maxCalleePhaseNum)
            {
                bool isLeftMover = true;
                bool isRightMover = true;
                foreach (CallCmd iter in node.CallCmds)
                {
                    ActionInfo actionInfo = procToActionInfo[iter.Proc];
                    isLeftMover = isLeftMover && actionInfo.IsLeftMover;
                    isRightMover = isRightMover && actionInfo.IsRightMover;
                }
                if (!isLeftMover && !isRightMover && node.CallCmds.Count > 1)
                {
                    Error(node, "The procedures in the parallel call must be all right mover or all left mover");
                }
                return base.VisitParCallCmd(node);
            }
            else
            {
                return node;
            }
        }
        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (node.Decl is GlobalVariable)
            {
                if (qedGlobalVariables.ContainsKey(node.Decl) && qedGlobalVariables[node.Decl] < minPhaseNum)
                {
                    minPhaseNum = qedGlobalVariables[node.Decl];
                }

                if (inAtomicSpecification && !qedGlobalVariables.ContainsKey(node.Decl))
                {
                    Error(node, "Cannot access non-qed global variable in atomic action");
                }
                else if (!inSpecification && qedGlobalVariables.ContainsKey(node.Decl))
                {
                    Error(node, "Cannot access qed global variable in ordinary code");
                }
            }
            return base.VisitIdentifierExpr(node);
        }
        public override Ensures VisitEnsures(Ensures ensures)
        {
            minPhaseNum = int.MaxValue;
            inAtomicSpecification = procToActionInfo.ContainsKey(enclosingProc) && procToActionInfo[enclosingProc].ensures == ensures;
            inSpecification = true;
            Ensures ret = base.VisitEnsures(ensures);
            inSpecification = false;
            if (inAtomicSpecification)
            {
                if (procToActionInfo[enclosingProc].availableUptoPhaseNum > minPhaseNum)
                {
                    Error(ensures, "A variable being accessed is hidden before this action becomes unavailable");
                }
                inAtomicSpecification = false;
            }
            else
            {
                CheckAndAddPhases(ensures, ensures.Attributes);
            }
            return ret;
        }
        public override Requires VisitRequires(Requires requires)
        {
            minPhaseNum = int.MaxValue;
            inSpecification = true;
            Requires ret = base.VisitRequires(requires);
            inSpecification = false;
            CheckAndAddPhases(requires, requires.Attributes);
            return ret;
        }
        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            minPhaseNum = int.MaxValue;
            inSpecification = true;
            Cmd ret = base.VisitAssertCmd(node);
            inSpecification = false;
            CheckAndAddPhases(node, node.Attributes);
            return ret;
        }

        private void CheckAndAddPhases(Absy node, QKeyValue attributes)
        {
            foreach (int phaseNum in OwickiGries.FindPhaseNums(attributes))
            {
                if (phaseNum > FindPhaseNumber(enclosingProc))
                {
                    Error(node, "The phase cannot be greater than the phase of enclosing procedure");
                }
                else if (phaseNum > minPhaseNum)
                {
                    Error(node, "A variable being accessed is hidden before this specification becomes unavailable");
                }
                else
                {
                    allPhaseNums.Add(phaseNum);
                }
            }
        }

        public void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
            errorCount++;
        }
    }
}