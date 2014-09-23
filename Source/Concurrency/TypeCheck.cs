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
        public int phaseNum;
        public int availableUptoPhaseNum;

        public ActionInfo(Procedure proc, int phaseNum, int availableUptoPhaseNum)
        {
            this.proc = proc;
            this.phaseNum = phaseNum;
            this.availableUptoPhaseNum = availableUptoPhaseNum;
        }

        public virtual bool IsRightMover
        {
            get { return true; }
        }

        public virtual bool IsLeftMover
        {
            get { return true; }
        }
    }

    public class AtomicActionInfo : ActionInfo
    {
        public Ensures ensures;
        public MoverType moverType;
        public List<AssertCmd> thisGate;
        public CodeExpr thisAction;
        public List<Variable> thisInParams;
        public List<Variable> thisOutParams;
        public List<AssertCmd> thatGate;
        public CodeExpr thatAction;
        public List<Variable> thatInParams;
        public List<Variable> thatOutParams;
        public HashSet<Variable> actionUsedGlobalVars;
        public HashSet<Variable> modifiedGlobalVars;
        public HashSet<Variable> gateUsedGlobalVars;
        public bool hasAssumeCmd;

        public bool CommutesWith(AtomicActionInfo actionInfo)
        {
            if (this.modifiedGlobalVars.Intersect(actionInfo.actionUsedGlobalVars).Count() > 0)
                return false;
            if (this.actionUsedGlobalVars.Intersect(actionInfo.modifiedGlobalVars).Count() > 0)
                return false;
            return true;
        }

        public override bool IsRightMover
        {
            get { return moverType == MoverType.Right || moverType == MoverType.Both; }
        }

        public override bool IsLeftMover
        {
            get { return moverType == MoverType.Left || moverType == MoverType.Both; }
        }

        public AtomicActionInfo(Procedure proc, Ensures ensures, MoverType moverType, int phaseNum, int availableUptoPhaseNum)
            : base(proc, phaseNum, availableUptoPhaseNum)
        {
            CodeExpr codeExpr = ensures.Condition as CodeExpr;
            this.ensures = ensures;
            this.moverType = moverType;
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
                cmds[i] = new AssumeCmd(assertCmd.tok, Expr.True);
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
                this.actionUsedGlobalVars = new HashSet<Variable>(collector.usedVars.Where(x => x is GlobalVariable));
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
        CheckingContext checkingContext;
        public int errorCount;
        public Dictionary<Variable, int> introducePhaseNums;
        public Dictionary<Variable, int> hidePhaseNums;
        Procedure enclosingProc;
        Implementation enclosingImpl;
        public Dictionary<Procedure, ActionInfo> procToActionInfo;
        public Program program;
        bool canAccessSharedVars;
        bool canAccessAuxVars;
        int minPhaseNum;
        int maxPhaseNum;
        public Dictionary<Absy, HashSet<int>> absyToPhaseNums;
        HashSet<Variable> auxVars;

        private static List<int> FindIntAttributes(QKeyValue kv, string name)
        {
            Contract.Requires(name != null);
            HashSet<int> attrs = new HashSet<int>();
            for (; kv != null; kv = kv.Next)
            {
                if (kv.Key != name) continue;
                foreach (var o in kv.Params)
                {
                    Expr e = o as Expr;
                    if (e == null) continue;
                    LiteralExpr l = e as LiteralExpr;
                    if (l != null && l.isBigNum)
                        attrs.Add(l.asBigNum.ToIntSafe);
                }
            }
            List<int> phases = attrs.ToList();
            phases.Sort();
            return phases;
        }

        private static MoverType GetMoverType(Ensures e)
        {
            if (QKeyValue.FindBoolAttribute(e.Attributes, "atomic"))
                return MoverType.Atomic;
            if (QKeyValue.FindBoolAttribute(e.Attributes, "right"))
                return MoverType.Right;
            if (QKeyValue.FindBoolAttribute(e.Attributes, "left"))
                return MoverType.Left;
            if (QKeyValue.FindBoolAttribute(e.Attributes, "both"))
                return MoverType.Both;
            return MoverType.Top;
        }

        private HashSet<int> allPhaseNums;
        public IEnumerable<int> AllPhaseNums
        {
            get
            {
                if (allPhaseNums == null)
                {
                    allPhaseNums = new HashSet<int>();
                    foreach (ActionInfo actionInfo in procToActionInfo.Values)
                    {
                        allPhaseNums.Add(actionInfo.phaseNum);
                    }
                }
                return allPhaseNums;
            }
        }

        public void TypeCheck()
        {
            foreach (var proc in program.Procedures)
            {
                if (!QKeyValue.FindBoolAttribute(proc.Attributes, "yields")) continue;

                int phaseNum = int.MaxValue;
                int availableUptoPhaseNum = int.MaxValue;
                List<int> attrs = FindIntAttributes(proc.Attributes, "phase");
                if (attrs.Count == 1)
                {
                    phaseNum = attrs[0];
                }
                else if (attrs.Count == 2)
                {
                    phaseNum = attrs[0];
                    availableUptoPhaseNum = attrs[1];
                }
                else
                {
                    Error(proc, "Incorrect number of phases");
                    continue;
                }
                foreach (Ensures e in proc.Ensures)
                {
                    MoverType moverType = GetMoverType(e);
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

                    minPhaseNum = int.MaxValue;
                    maxPhaseNum = -1;
                    canAccessSharedVars = true;
                    enclosingProc = proc;
                    enclosingImpl = null;
                    base.VisitEnsures(e);
                    canAccessSharedVars = false;
                    if (maxPhaseNum <= phaseNum && availableUptoPhaseNum <= minPhaseNum)
                    {
                        // ok
                    }
                    else
                    {
                        Error(e, "A variable being accessed is hidden before this action becomes unavailable");
                    }

                    procToActionInfo[proc] = new AtomicActionInfo(proc, e, moverType, phaseNum, availableUptoPhaseNum);
                }
                if (!procToActionInfo.ContainsKey(proc))
                {
                    procToActionInfo[proc] = new ActionInfo(proc, phaseNum, availableUptoPhaseNum);
                }
            }
            if (errorCount > 0) return;
            this.VisitProgram(program);
            if (errorCount > 0) return;
            YieldTypeChecker.PerformYieldSafeCheck(this);
        }

        public MoverTypeChecker(Program program)
        {
            this.auxVars = new HashSet<Variable>();
            this.absyToPhaseNums = new Dictionary<Absy, HashSet<int>>();
            this.introducePhaseNums = new Dictionary<Variable, int>();
            this.hidePhaseNums = new Dictionary<Variable, int>();
            this.procToActionInfo = new Dictionary<Procedure, ActionInfo>();
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.program = program;
            this.enclosingProc = null;
            this.enclosingImpl = null;
            this.canAccessSharedVars = false;
            this.canAccessAuxVars = false;
            this.minPhaseNum = int.MaxValue;
            this.maxPhaseNum = -1;
            foreach (var g in program.GlobalVariables())
            {
                List<int> phaseNums = FindIntAttributes(g.Attributes, "phase");
                this.introducePhaseNums[g] = 0;
                this.hidePhaseNums[g] = int.MaxValue;
                if (phaseNums.Count == 0)
                {
                    // ok
                }
                else if (phaseNums.Count == 1)
                {
                    this.hidePhaseNums[g] = phaseNums[0];
                }
                else if (phaseNums.Count == 2)
                {
                    this.introducePhaseNums[g] = phaseNums[0];
                    this.hidePhaseNums[g] = phaseNums[1];
                }
                else
                {
                    Error(g, "Too many phase numbers");
                }
            }
        }
        
        public override Implementation VisitImplementation(Implementation node)
        {
            if (!procToActionInfo.ContainsKey(node.Proc))
            {
                return node;
            }
            this.enclosingImpl = node;
            this.enclosingProc = null;
            auxVars = new HashSet<Variable>();
            foreach (Variable v in node.LocVars)
            {
                if (QKeyValue.FindBoolAttribute(v.Attributes, "aux"))
                {
                    auxVars.Add(v);
                }
            }
            return base.VisitImplementation(node);
        }
        
        public override Procedure VisitProcedure(Procedure node)
        {
            if (!procToActionInfo.ContainsKey(node))
            {
                return node;
            }
            this.enclosingProc = node;
            this.enclosingImpl = null;
            return base.VisitProcedure(node);
        }

        public override Cmd VisitCallCmd(CallCmd node)
        {
            int enclosingProcPhaseNum = procToActionInfo[enclosingImpl.Proc].phaseNum;
            if (procToActionInfo.ContainsKey(node.Proc))
            {
                ActionInfo actionInfo = procToActionInfo[node.Proc];
                if (node.IsAsync && actionInfo is AtomicActionInfo)
                {
                    Error(node, "Target of async call cannot be an atomic action");
                }
                int calleePhaseNum = procToActionInfo[node.Proc].phaseNum;
                if (enclosingProcPhaseNum < calleePhaseNum ||
                    (enclosingProcPhaseNum == calleePhaseNum && actionInfo is AtomicActionInfo))
                {
                    Error(node, "The phase of the caller procedure must be greater than the phase of the callee");
                }
                else if (enclosingProcPhaseNum == calleePhaseNum && enclosingImpl.OutParams.Count > 0)
                {
                    HashSet<Variable> outParams = new HashSet<Variable>(enclosingImpl.OutParams);
                    foreach (var x in node.Outs)
                    {
                        if (x.Decl is GlobalVariable)
                        {
                            Error(node, "A global variable cannot be used as output argument for this call");
                        }
                        else if (outParams.Contains(x.Decl))
                        {
                            Error(node, "An output variable of the enclosing implementation cannot be used as output argument for this call");
                        }
                    }
                }
                if (actionInfo.availableUptoPhaseNum < enclosingProcPhaseNum)
                {
                    Error(node, "The callee is not available in the phase of the caller procedure");
                }
            }
            return base.VisitCallCmd(node);
        }

        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            int enclosingProcPhaseNum = procToActionInfo[enclosingImpl.Proc].phaseNum;
            bool isLeftMover = true;
            bool isRightMover = true;
            int maxCalleePhaseNum = 0;
            int numAtomicActions = 0;
            foreach (CallCmd iter in node.CallCmds)
            {
                ActionInfo actionInfo = procToActionInfo[iter.Proc];
                isLeftMover = isLeftMover && actionInfo.IsLeftMover;
                isRightMover = isRightMover && actionInfo.IsRightMover;
                if (actionInfo.phaseNum > maxCalleePhaseNum)
                { 
                    maxCalleePhaseNum = actionInfo.phaseNum; 
                }
                if (actionInfo is AtomicActionInfo)
                {
                    numAtomicActions++;
                }
            }
            if (!isLeftMover && !isRightMover && node.CallCmds.Count > 1)
            {
                Error(node, "The procedures in the parallel call must be all right mover or all left mover");
            }
            if (maxCalleePhaseNum == enclosingProcPhaseNum && numAtomicActions > 0)
            {
                Error(node, "At phase {0}, either no callee is an atomic action or no callee phase equals the phase of the enclosing procedure");
            }
            return base.VisitParCallCmd(node);
        }

        public override Cmd VisitAssignCmd(AssignCmd node)
        {
            Contract.Ensures(Contract.Result<Cmd>() == node);
            for (int i = 0; i < node.Lhss.Count; ++i)
            {
                bool savedCanAccessSharedVars = canAccessSharedVars;
                bool savedCanAccessAuxVars = canAccessAuxVars;
                Variable v = node.Lhss[i].DeepAssignedVariable;
                if (v is LocalVariable && auxVars.Contains(v))
                {
                    canAccessSharedVars = true;
                    canAccessAuxVars = true;
                }
                this.Visit(node.Lhss[i]);
                this.Visit(node.Rhss[i]);
                canAccessSharedVars = savedCanAccessSharedVars;
                canAccessAuxVars = savedCanAccessAuxVars;
            }
            return node;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (node.Decl is GlobalVariable)
            {
                if (!canAccessSharedVars)
                {
                    Error(node, "Shared variable can be accessed only in atomic actions or specifications");
                }
                else
                {
                    if (hidePhaseNums[node.Decl] < minPhaseNum)
                    {
                        minPhaseNum = hidePhaseNums[node.Decl];
                    }
                    if (introducePhaseNums[node.Decl] > maxPhaseNum)
                    {
                        maxPhaseNum = introducePhaseNums[node.Decl];
                    }
                }
            }
            else if (node.Decl is LocalVariable && auxVars.Contains(node.Decl) && !canAccessAuxVars)
            {
                Error(node, "Auxiliary variable can be accessed only in assertions");
            }

            return base.VisitIdentifierExpr(node);
        }
        
        public override Ensures VisitEnsures(Ensures ensures)
        {
            minPhaseNum = int.MaxValue;
            maxPhaseNum = -1;
            canAccessSharedVars = true;
            Ensures ret = base.VisitEnsures(ensures);
            canAccessSharedVars = false;
            ActionInfo actionInfo = procToActionInfo[enclosingProc];
            AtomicActionInfo atomicActionInfo = actionInfo as AtomicActionInfo;
            if (atomicActionInfo != null && atomicActionInfo.ensures == ensures)
            {
                // This case has already been checked
            }
            else
            {
                CheckAndAddPhases(ensures, ensures.Attributes, actionInfo.phaseNum);
            }
            return ret;
        }
        
        public override Requires VisitRequires(Requires requires)
        {
            minPhaseNum = int.MaxValue;
            maxPhaseNum = -1;
            canAccessSharedVars = true;
            Requires ret = base.VisitRequires(requires);
            canAccessSharedVars = false;
            CheckAndAddPhases(requires, requires.Attributes, procToActionInfo[enclosingProc].phaseNum);
            return ret;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            if (enclosingImpl == null)
                return base.VisitAssertCmd(node);
            minPhaseNum = int.MaxValue;
            maxPhaseNum = -1;
            canAccessSharedVars = true;
            canAccessAuxVars = true;
            Cmd ret = base.VisitAssertCmd(node);
            canAccessAuxVars = false;
            canAccessSharedVars = false;
            CheckAndAddPhases(node, node.Attributes, procToActionInfo[enclosingImpl.Proc].phaseNum);
            return ret;
        }

        private void CheckAndAddPhases(Absy node, QKeyValue attributes, int enclosingProcPhaseNum)
        {
            List<int> attrs = FindIntAttributes(attributes, "phase");
            if (attrs.Count == 0)
            {
                Error(node, "phase not present");
                return;
            }
            absyToPhaseNums[node] = new HashSet<int>();
            foreach (int phaseNum in attrs)
            {
                if (phaseNum > enclosingProcPhaseNum)
                {
                    Error(node, "The phase cannot be greater than the phase of enclosing procedure");
                }
                else if (maxPhaseNum < phaseNum && phaseNum <= minPhaseNum)
                {
                    absyToPhaseNums[node].Add(phaseNum);
                }
                else
                {
                    Error(node, string.Format("A variable being accessed in this specification is unavailable at phase {0}", phaseNum));
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