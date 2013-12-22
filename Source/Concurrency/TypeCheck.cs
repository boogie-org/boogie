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
        public MoverType moverType;
        public int phaseNum;
        public HashSet<int> callerPhaseNums;
        public List<AssertCmd> thisGate;
        public CodeExpr thisAction;
        public List<Variable> thisInParams;
        public List<Variable> thisOutParams;
        public List<AssertCmd> thatGate;
        public CodeExpr thatAction;
        public List<Variable> thatInParams;
        public List<Variable> thatOutParams;

        public bool IsRightMover
        {
            get { return moverType == MoverType.Right || moverType == MoverType.Both; }
        }

        public bool IsLeftMover
        {
            get { return moverType == MoverType.Left || moverType == MoverType.Both; }
        }

        public ActionInfo(Procedure proc, CodeExpr codeExpr, MoverType moverType, int phaseNum)
        {
            this.proc = proc;
            this.moverType = moverType;
            this.phaseNum = phaseNum;
            this.callerPhaseNums = new HashSet<int>();
            this.thisGate = new List<AssertCmd>();
            this.thisAction = codeExpr;
            this.thisInParams = new List<Variable>();
            this.thisOutParams = new List<Variable>();
            this.thatGate = new List<AssertCmd>();
            this.thatInParams = new List<Variable>();
            this.thatOutParams = new List<Variable>();

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
                Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), true);
                this.thatInParams.Add(y);
                map[x] = new IdentifierExpr(Token.NoToken, y);
            }
            foreach (Variable x in proc.OutParams)
            {
                this.thisOutParams.Add(x);
                Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), false);
                this.thatOutParams.Add(y);
                map[x] = new IdentifierExpr(Token.NoToken, y);
            }
            List<Variable> otherLocVars = new List<Variable>();
            foreach (Variable x in thisAction.LocVars)
            {
                Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), false);
                map[x] = new IdentifierExpr(Token.NoToken, y);
                otherLocVars.Add(y);
            }
            Contract.Assume(proc.TypeParameters.Count == 0);
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            foreach (AssertCmd assertCmd in thisGate)
            {
                thatGate.Add((AssertCmd)Substituter.Apply(subst, assertCmd));
            }
            Dictionary<Block, Block> blockMap = new Dictionary<Block, Block>();
            List<Block> otherBlocks = new List<Block>();
            foreach (Block block in thisAction.Blocks)
            {
                List<Cmd> otherCmds = new List<Cmd>();
                foreach (Cmd cmd in block.Cmds)
                {
                    otherCmds.Add(Substituter.Apply(subst, cmd));
                }
                Block otherBlock = new Block();
                otherBlock.Cmds = otherCmds;
                otherBlock.Label = "that_" + block.Label;
                block.Label = "this_" + block.Label;
                otherBlocks.Add(otherBlock);
                blockMap[block] = otherBlock;
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
                List<Block> otherGotoCmdLabelTargets = new List<Block>();
                List<string> otherGotoCmdLabelNames = new List<string>();
                GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    otherGotoCmdLabelTargets.Add(blockMap[target]);
                    otherGotoCmdLabelNames.Add(blockMap[target].Label);
                }
                blockMap[block].TransferCmd = new GotoCmd(block.TransferCmd.tok, otherGotoCmdLabelNames, otherGotoCmdLabelTargets);
            }
            this.thatAction = new CodeExpr(otherLocVars, otherBlocks);
        }
    }

    public class MoverTypeChecker : StandardVisitor
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
        HashSet<Variable> qedGlobalVariables;
        int enclosingProcPhaseNum;
        public Dictionary<Procedure, ActionInfo> procToActionInfo;
        public Program program;
        public HashSet<int> assertionPhaseNums;
        bool inAtomicSpecification;

        public void TypeCheck()
        {
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc == null) continue;
                foreach (Ensures e in proc.Ensures)
                {
                    int phaseNum;
                    MoverType moverType = MoverCheck.GetMoverType(e, out phaseNum);
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
                    procToActionInfo[proc] = new ActionInfo(proc, codeExpr, moverType, phaseNum);
                }
            }
            this.VisitProgram(program);
#if QED
            YieldTypeChecker.PerformYieldTypeChecking(this);
#endif
        }

        public MoverTypeChecker(Program program)
        {
            this.qedGlobalVariables = new HashSet<Variable>();
            foreach (var g in program.GlobalVariables())
            {
                if (QKeyValue.FindBoolAttribute(g.Attributes, "qed"))
                {
                    this.qedGlobalVariables.Add(g);
                    g.Attributes = OwickiGries.RemoveQedAttribute(g.Attributes);
                }
            }
            this.procToActionInfo = new Dictionary<Procedure, ActionInfo>();
            this.assertionPhaseNums = new HashSet<int>();
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.program = program;
            this.enclosingProcPhaseNum = int.MaxValue;
            this.inAtomicSpecification = false;
        }
        public override Implementation VisitImplementation(Implementation node)
        {
            enclosingProcPhaseNum = FindPhaseNumber(node.Proc);
            return base.VisitImplementation(node);
        }
        public override Procedure VisitProcedure(Procedure node)
        {
            enclosingProcPhaseNum = FindPhaseNumber(node);
            return base.VisitProcedure(node);
        } 
        public override Cmd VisitCallCmd(CallCmd node)
        {
            if (!node.IsAsync)
            {
                int calleePhaseNum = FindPhaseNumber(node.Proc);
                if (enclosingProcPhaseNum > calleePhaseNum)
                {
                    procToActionInfo[node.Proc].callerPhaseNums.Add(enclosingProcPhaseNum);
                }
                else if (enclosingProcPhaseNum < calleePhaseNum || enclosingProcPhaseNum != int.MaxValue)
                {
                    Error(node, "The phase of the caller procedure must be greater than the phase of the callee");
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

            if (enclosingProcPhaseNum > maxCalleePhaseNum)
            {
                bool isLeftMover = true;
                bool isRightMover = true;
                foreach (CallCmd iter in node.CallCmds)
                {
                    ActionInfo actionInfo = procToActionInfo[iter.Proc];
                    isLeftMover = isLeftMover && actionInfo.IsLeftMover;
                    isRightMover = isRightMover && actionInfo.IsRightMover;
                    actionInfo.callerPhaseNums.Add(enclosingProcPhaseNum);
                }
                if (!isLeftMover && !isRightMover && node.CallCmds.Count > 1)
                {
                    Error(node, "The procedures in the parallel call must be all right mover or all left mover");
                }
            }
            return node;
        }
        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (node.Decl is GlobalVariable)
            {
                if (inAtomicSpecification && !qedGlobalVariables.Contains(node.Decl))
                {
                    Error(node, "Cannot access non-qed global variable in atomic action");
                }
                else if (!inAtomicSpecification && qedGlobalVariables.Contains(node.Decl))
                {
                    Error(node, "Cannot access qed global variable in ordinary code");
                }
            }
            return base.VisitIdentifierExpr(node);
        }
        public override Ensures VisitEnsures(Ensures ensures)
        {
            if (ensures.IsAtomicSpecification)
            {
                inAtomicSpecification = true;
                Ensures ret = base.VisitEnsures(ensures);
                inAtomicSpecification = false;
                return ret;
            }
            int phaseNum = QKeyValue.FindIntAttribute(ensures.Attributes, "phase", int.MaxValue);
            assertionPhaseNums.Add(phaseNum);
            if (phaseNum > enclosingProcPhaseNum)
            {
                Error(ensures, "The phase of ensures clause cannot be greater than the phase of enclosing procedure");
            }
            return ensures;
        }
        public override Requires VisitRequires(Requires requires)
        {
            int phaseNum = QKeyValue.FindIntAttribute(requires.Attributes, "phase", int.MaxValue);
            assertionPhaseNums.Add(phaseNum); 
            if (phaseNum > enclosingProcPhaseNum)
            {
                Error(requires, "The phase of requires clause cannot be greater than the phase of enclosing procedure");
            }
            return requires;
        }
        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            int phaseNum = QKeyValue.FindIntAttribute(node.Attributes, "phase", int.MaxValue);
            assertionPhaseNums.Add(phaseNum); 
            if (phaseNum > enclosingProcPhaseNum)
            {
                Error(node, "The phase of assert cannot be greater than the phase of enclosing procedure");
            }
            return node;
        }
        public void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
            errorCount++;
        }
    }
}