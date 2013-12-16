using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace Microsoft.Boogie
{
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
        HashSet<Variable> globalVariables;
        bool globalVarAccessAllowed;
        bool visitingAssertion;
        int enclosingProcPhaseNum;
        public Dictionary<Procedure, ActionInfo> procToActionInfo;
        public Program program;

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
            this.globalVariables = new HashSet<Variable>(program.GlobalVariables());
            this.procToActionInfo = new Dictionary<Procedure, ActionInfo>();
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.program = program;
            this.visitingAssertion = false;
            this.enclosingProcPhaseNum = int.MaxValue;
        }
        public override Block VisitBlock(Block node)
        {
            globalVarAccessAllowed = false;
            return base.VisitBlock(node);
        }
        public override Cmd VisitHavocCmd(HavocCmd node)
        {
            globalVarAccessAllowed = false;
            return base.VisitHavocCmd(node);
        }
        public override Cmd VisitAssignCmd(AssignCmd node)
        {
            globalVarAccessAllowed = false;
            return base.VisitAssignCmd(node);
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
            globalVarAccessAllowed = false;
            if (enclosingProcPhaseNum == int.MaxValue)
                return base.VisitCallCmd(node);

            if (!node.IsAsync)
            {
                int calleePhaseNum = FindPhaseNumber(node.Proc);
                if (enclosingProcPhaseNum > calleePhaseNum)
                {
                    procToActionInfo[node.Proc].callerPhaseNums.Add(enclosingProcPhaseNum);
                }
                else
                {
                    Error(node, "The phase of the caller procedure must be greater than the phase of the callee");
                }
            }
            return base.VisitCallCmd(node);
        }
        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            globalVarAccessAllowed = false;
            foreach (CallCmd callCmd in node.CallCmds)
            {
                base.VisitCallCmd(callCmd);
            }

            if (enclosingProcPhaseNum == int.MaxValue)
                return node;

            int maxCalleePhaseNum = 0;
            foreach (CallCmd iter in node.CallCmds)
            {
                int calleePhaseNum = FindPhaseNumber(iter.Proc);
                if (calleePhaseNum < maxCalleePhaseNum)
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
                if (!isLeftMover && !isRightMover)
                {
                    Error(node, "The procedures in the parallel call must be all right mover or all left mover");
                }
            }
            return node;
        }
        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            globalVarAccessAllowed = true;
            return base.VisitYieldCmd(node);
        }
        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (!visitingAssertion && !globalVarAccessAllowed && globalVariables.Contains(node.Decl))
            {
                Error(node, "Cannot access global variable");
            }
            return base.VisitIdentifierExpr(node);
        }
        public override Ensures VisitEnsures(Ensures ensures)
        {
            int phaseNum = QKeyValue.FindIntAttribute(ensures.Attributes, "phase", 0);
            if (phaseNum > enclosingProcPhaseNum)
            {
                Error(ensures, "The phase of ensures clause cannot be greater than the phase of enclosing procedure");
            }
            this.visitingAssertion = true;
            Ensures ret = base.VisitEnsures(ensures);
            this.visitingAssertion = false;
            return ret;
        }
        public override Requires VisitRequires(Requires requires)
        {
            int phaseNum = QKeyValue.FindIntAttribute(requires.Attributes, "phase", 0);
            if (phaseNum > enclosingProcPhaseNum)
            {
                Error(requires, "The phase of requires clause cannot be greater than the phase of enclosing procedure");
            }
            this.visitingAssertion = true;
            Requires ret = base.VisitRequires(requires);
            this.visitingAssertion = false;
            return ret;
        }
        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            int phaseNum = QKeyValue.FindIntAttribute(node.Attributes, "phase", 0);
            if (phaseNum > enclosingProcPhaseNum)
            {
                Error(node, "The phase of assert cannot be greater than the phase of enclosing procedure");
            }
            this.visitingAssertion = true;
            Cmd ret = base.VisitAssertCmd(node);
            this.visitingAssertion = false;
            return ret;
        }
        public override Cmd VisitAssumeCmd(AssumeCmd node)
        {
            int phaseNum = QKeyValue.FindIntAttribute(node.Attributes, "phase", 0);
            if (phaseNum > enclosingProcPhaseNum)
            {
                Error(node, "The phase of assume cannot be greater than the phase of enclosing procedure");
            }
            return base.VisitAssumeCmd(node);
        }

        public void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
            errorCount++;
        }
    }
}