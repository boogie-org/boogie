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
        int phaseNumEnclosingProc;
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
            this.phaseNumEnclosingProc = int.MaxValue;
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
            phaseNumEnclosingProc = FindPhaseNumber(node.Proc);
            return base.VisitImplementation(node);
        }
        public override Procedure VisitProcedure(Procedure node)
        {
            phaseNumEnclosingProc = FindPhaseNumber(node);
            return base.VisitProcedure(node);
        } 
        public override Cmd VisitCallCmd(CallCmd node)
        {
            globalVarAccessAllowed = false;
            if (!node.IsAsync && node.InParallelWith == null) {

                int calleePhaseNum = FindPhaseNumber(node.Proc);
                if (!(calleePhaseNum == int.MaxValue || phaseNumEnclosingProc > calleePhaseNum))
                {
                    Error(node, "The phase of the caller procedure must be greater than the phase of the callee");    
                }
            }
            return base.VisitCallCmd(node);
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
            if (phaseNum > phaseNumEnclosingProc)
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
            if (phaseNum > phaseNumEnclosingProc)
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
            if (phaseNum > phaseNumEnclosingProc)
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
            if (phaseNum > phaseNumEnclosingProc)
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