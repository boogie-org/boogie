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
        public int createdAtLayerNum;
        public int availableUptoLayerNum;
        public bool hasImplementation;
        public bool isExtern;

        public ActionInfo(Procedure proc, int createdAtLayerNum, int availableUptoLayerNum)
        {
            this.proc = proc;
            this.createdAtLayerNum = createdAtLayerNum;
            this.availableUptoLayerNum = availableUptoLayerNum;
            this.hasImplementation = false;
            this.isExtern = QKeyValue.FindBoolAttribute(proc.Attributes, "extern");
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

        public AtomicActionInfo(Procedure proc, Ensures ensures, MoverType moverType, int layerNum, int availableUptoLayerNum)
            : base(proc, layerNum, availableUptoLayerNum)
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

    public class SharedVariableInfo
    {
        public int introLayerNum;
        public int hideLayerNum;

        public SharedVariableInfo(int introLayerNum, int hideLayerNum)
        {
            this.introLayerNum = introLayerNum;
            this.hideLayerNum = hideLayerNum;
        }
    }

    public class LayerEraser : ReadOnlyVisitor
    {
        private QKeyValue RemoveLayerAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveLayerAttribute(iter.Next);
            return (iter.Key == "layer") ? iter.Next : iter;
        }

        public override Variable VisitVariable(Variable node)
        {
            node.Attributes = RemoveLayerAttribute(node.Attributes);
            return base.VisitVariable(node);
        }

        public override Procedure VisitProcedure(Procedure node)
        {
            node.Attributes = RemoveLayerAttribute(node.Attributes);
            return base.VisitProcedure(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            node.Attributes = RemoveLayerAttribute(node.Attributes);
            return base.VisitImplementation(node);
        }

        public override Requires VisitRequires(Requires node)
        {
            node.Attributes = RemoveLayerAttribute(node.Attributes);
            return base.VisitRequires(node);
        }

        public override Ensures VisitEnsures(Ensures node)
        {
            node.Attributes = RemoveLayerAttribute(node.Attributes);
            return base.VisitEnsures(node);
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            node.Attributes = RemoveLayerAttribute(node.Attributes);
            return base.VisitAssertCmd(node);
        }
    }

    public class MoverTypeChecker : ReadOnlyVisitor
    {
        CheckingContext checkingContext;
        public int errorCount;
        public Dictionary<Variable, SharedVariableInfo> globalVarToSharedVarInfo;
        Procedure enclosingProc;
        Implementation enclosingImpl;
        public Dictionary<Procedure, ActionInfo> procToActionInfo;
        public Program program;
        bool canAccessSharedVars;
        bool canAccessGhostVars;
        int minLayerNum;
        int maxLayerNum;
        public Dictionary<Absy, HashSet<int>> absyToLayerNums;
        HashSet<Variable> ghostVars;
        public int leastUnimplementedLayerNum;

        private static List<int> FindLayers(QKeyValue kv)
        {
            List<int> layers = new List<int>();
            for (; kv != null; kv = kv.Next)
            {
                if (kv.Key != "layer") continue;
                foreach (var o in kv.Params)
                {
                    Expr e = o as Expr;
                    if (e == null) return null;
                    LiteralExpr l = e as LiteralExpr;
                    if (l == null) return null;
                    if (!l.isBigNum) return null;
                    layers.Add(l.asBigNum.ToIntSafe);
                }
            }
            return layers;
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

        public MoverTypeChecker(Program program)
        {
            this.ghostVars = new HashSet<Variable>();
            this.absyToLayerNums = new Dictionary<Absy, HashSet<int>>();
            this.globalVarToSharedVarInfo = new Dictionary<Variable, SharedVariableInfo>();
            this.procToActionInfo = new Dictionary<Procedure, ActionInfo>();
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.program = program;
            this.enclosingProc = null;
            this.enclosingImpl = null;
            this.canAccessSharedVars = false;
            this.canAccessGhostVars = false;
            this.minLayerNum = int.MaxValue;
            this.maxLayerNum = -1;
            this.leastUnimplementedLayerNum = int.MaxValue;
            foreach (var g in program.GlobalVariables)
            {
                List<int> layerNums = FindLayers(g.Attributes);
                if (layerNums.Count == 0)
                {
                    // Cannot access atomic actions
                }
                else if (layerNums.Count == 1)
                {
                    this.globalVarToSharedVarInfo[g] = new SharedVariableInfo(layerNums[0], int.MaxValue);
                }
                else if (layerNums.Count == 2)
                {
                    this.globalVarToSharedVarInfo[g] = new SharedVariableInfo(layerNums[0], layerNums[1]);
                }
                else
                {
                    Error(g, "Too many layer numbers");
                }
            }
        }
        
        private HashSet<int> allCreatedLayerNums;
        public IEnumerable<int> AllCreatedLayerNums
        {
            get
            {
                if (allCreatedLayerNums == null)
                {
                    allCreatedLayerNums = new HashSet<int>();
                    foreach (ActionInfo actionInfo in procToActionInfo.Values)
                    {
                        allCreatedLayerNums.Add(actionInfo.createdAtLayerNum);
                    }
                }
                return allCreatedLayerNums;
            }
        }

        public void TypeCheck()
        {
            foreach (var proc in program.Procedures)
            {
                if (!QKeyValue.FindBoolAttribute(proc.Attributes, "yields")) continue;

                int createdAtLayerNum;  // must be initialized by the following code, otherwise it is an error
                int availableUptoLayerNum = int.MaxValue;
                List<int> attrs = FindLayers(proc.Attributes);
                if (attrs.Count == 1)
                {
                    createdAtLayerNum = attrs[0];
                }
                else if (attrs.Count == 2)
                {
                    createdAtLayerNum = attrs[0];
                    availableUptoLayerNum = attrs[1];
                }
                else
                {
                    Error(proc, "Incorrect number of layers");
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
                    if (availableUptoLayerNum <= createdAtLayerNum)
                    {
                        Error(proc, "Creation layer number must be less than the available upto layer number");
                        continue;
                    }

                    minLayerNum = int.MaxValue;
                    maxLayerNum = -1;
                    canAccessSharedVars = true;
                    enclosingProc = proc;
                    enclosingImpl = null;
                    base.VisitEnsures(e);
                    canAccessSharedVars = false;
                    if (maxLayerNum > createdAtLayerNum)
                    {
                        Error(e, "A variable being accessed is introduced after this action is created");
                    }
                    else if (availableUptoLayerNum > minLayerNum)
                    {
                        Error(e, "A variable being accessed is hidden before this action becomes unavailable");
                    }
                    else
                    {
                        procToActionInfo[proc] = new AtomicActionInfo(proc, e, moverType, createdAtLayerNum, availableUptoLayerNum);
                    }
                }
                if (errorCount > 0) continue;
                if (!procToActionInfo.ContainsKey(proc))
                {
                    if (availableUptoLayerNum < createdAtLayerNum)
                    {
                        Error(proc, "Creation layer number must be no more than the available upto layer number");
                        continue;
                    }
                    else
                    {
                        procToActionInfo[proc] = new ActionInfo(proc, createdAtLayerNum, availableUptoLayerNum);
                    }
                }
            }
            if (errorCount > 0) return;
            foreach (var impl in program.Implementations)
            {
                if (!procToActionInfo.ContainsKey(impl.Proc)) continue;
                procToActionInfo[impl.Proc].hasImplementation = true;
            }
            foreach (var proc in procToActionInfo.Keys)
            {
                ActionInfo actionInfo = procToActionInfo[proc];
                if (actionInfo.isExtern && actionInfo.hasImplementation)
                {
                    Error(proc, "Extern procedure cannot have an implementation");
                    continue;
                }
                if (actionInfo.isExtern || actionInfo.hasImplementation) continue;
                if (leastUnimplementedLayerNum == int.MaxValue)
                {
                    leastUnimplementedLayerNum = actionInfo.createdAtLayerNum;
                }
                else if (leastUnimplementedLayerNum != actionInfo.createdAtLayerNum)
                {
                    Error(proc, "All unimplemented atomic actions must be created at the same layer");
                }
            }
            foreach (var g in this.globalVarToSharedVarInfo.Keys)
            {
                var info = globalVarToSharedVarInfo[g];
                if (!this.AllCreatedLayerNums.Contains(info.introLayerNum))
                {
                    Error(g, "Variable must be introduced with creation of some atomic action");
                }
                if (info.hideLayerNum != int.MaxValue && !this.AllCreatedLayerNums.Contains(info.hideLayerNum))
                {
                    Error(g, "Variable must be hidden with creation of some atomic action");
                }
            }
            if (errorCount > 0) return;
            this.VisitProgram(program);
            foreach (Procedure proc in program.Procedures)
            {
                if (procToActionInfo.ContainsKey(proc)) continue;
                foreach (var ie in proc.Modifies)
                {
                    if (!SharedVariables.Contains(ie.Decl)) continue;
                    Error(proc, "A ghost procedure must not modify a global variable with layer annotation");
                }
            }
            if (errorCount > 0) return;
            YieldTypeChecker.PerformYieldSafeCheck(this);
            new LayerEraser().VisitProgram(program);
        }

        public IEnumerable<Variable> SharedVariables
        {
            get { return this.globalVarToSharedVarInfo.Keys;  }
        }
        
        public override Implementation VisitImplementation(Implementation node)
        {
            if (!procToActionInfo.ContainsKey(node.Proc))
            {
                return node;
            }
            this.enclosingImpl = node;
            this.enclosingProc = null;
            ghostVars = new HashSet<Variable>();
            foreach (Variable v in node.LocVars)
            {
                if (QKeyValue.FindBoolAttribute(v.Attributes, "ghost"))
                {
                    ghostVars.Add(v);
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
            int enclosingProcLayerNum = procToActionInfo[enclosingImpl.Proc].createdAtLayerNum;
            if (procToActionInfo.ContainsKey(node.Proc))
            {
                ActionInfo actionInfo = procToActionInfo[node.Proc];
                if (node.IsAsync && actionInfo is AtomicActionInfo)
                {
                    Error(node, "Target of async call cannot be an atomic action");
                }
                int calleeLayerNum = procToActionInfo[node.Proc].createdAtLayerNum;
                if (enclosingProcLayerNum < calleeLayerNum ||
                    (enclosingProcLayerNum == calleeLayerNum && actionInfo is AtomicActionInfo))
                {
                    Error(node, "The layer of the caller must be greater than the layer of the callee");
                }
                else if (enclosingProcLayerNum == calleeLayerNum && enclosingImpl.OutParams.Count > 0)
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
                if (actionInfo.availableUptoLayerNum < enclosingProcLayerNum)
                {
                    Error(node, "The callee is not available in the caller procedure");
                }
                return base.VisitCallCmd(node);
            }
            else
            {
                foreach (var ie in node.Outs)
                {
                    if (ghostVars.Contains(ie.Decl)) continue;
                    Error(node, "The output of a ghost procedure must be assigned to a ghost variable");
                }
                bool savedCanAccessSharedVars = canAccessSharedVars;
                bool savedCanAccessAuxVars = canAccessGhostVars;
                canAccessSharedVars = true;
                canAccessGhostVars = true;
                var retVal = base.VisitCallCmd(node);
                canAccessSharedVars = savedCanAccessSharedVars;
                canAccessGhostVars = savedCanAccessAuxVars;
                return retVal;
            }
        }

        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            int enclosingProcLayerNum = procToActionInfo[enclosingImpl.Proc].createdAtLayerNum;
            bool isLeftMover = true;
            bool isRightMover = true;
            int maxCalleeLayerNum = 0;
            int atomicActionCalleeLayerNum = 0;
            int numAtomicActions = 0;
            foreach (CallCmd iter in node.CallCmds)
            {
                ActionInfo actionInfo = procToActionInfo[iter.Proc];
                isLeftMover = isLeftMover && actionInfo.IsLeftMover;
                isRightMover = isRightMover && actionInfo.IsRightMover;
                if (actionInfo.createdAtLayerNum > maxCalleeLayerNum)
                { 
                    maxCalleeLayerNum = actionInfo.createdAtLayerNum; 
                }
                if (actionInfo is AtomicActionInfo)
                {
                    numAtomicActions++;
                    if (atomicActionCalleeLayerNum == 0)
                    {
                        atomicActionCalleeLayerNum = actionInfo.createdAtLayerNum;
                    }
                    else if (atomicActionCalleeLayerNum != actionInfo.createdAtLayerNum)
                    {
                        Error(node, "All atomic actions must be introduced at the same layer");
                    }
                }
            }
            if (numAtomicActions > 1 && !isLeftMover && !isRightMover)
            {
                Error(node, "The atomic actions in the parallel call must be all right movers or all left movers");
            }
            if (0 < atomicActionCalleeLayerNum && atomicActionCalleeLayerNum < maxCalleeLayerNum)
            {
                Error(node, "Atomic actions must be introduced at the highest layer");
            }
            return base.VisitParCallCmd(node);
        }

        public override Cmd VisitAssignCmd(AssignCmd node)
        {
            Contract.Ensures(Contract.Result<Cmd>() == node);
            for (int i = 0; i < node.Lhss.Count; ++i)
            {
                bool savedCanAccessSharedVars = canAccessSharedVars;
                bool savedCanAccessAuxVars = canAccessGhostVars;
                Variable v = node.Lhss[i].DeepAssignedVariable;
                if (v is LocalVariable && ghostVars.Contains(v))
                {
                    canAccessSharedVars = true;
                    canAccessGhostVars = true;
                }
                this.Visit(node.Lhss[i]);
                this.Visit(node.Rhss[i]);
                canAccessSharedVars = savedCanAccessSharedVars;
                canAccessGhostVars = savedCanAccessAuxVars;
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
                else if (this.globalVarToSharedVarInfo.ContainsKey(node.Decl))
                {
                    if (this.globalVarToSharedVarInfo[node.Decl].hideLayerNum < minLayerNum)
                    {
                        minLayerNum = this.globalVarToSharedVarInfo[node.Decl].hideLayerNum;
                    }
                    if (this.globalVarToSharedVarInfo[node.Decl].introLayerNum > maxLayerNum)
                    {
                        maxLayerNum = this.globalVarToSharedVarInfo[node.Decl].introLayerNum;
                    }
                }
                else
                {
                    Error(node, "Accessed shared variable must have layer annotation");
                }
            }
            else if (node.Decl is LocalVariable && ghostVars.Contains(node.Decl) && !canAccessGhostVars)
            {
                Error(node, "Ghost variable can be accessed only in assertions");
            }

            return base.VisitIdentifierExpr(node);
        }
        
        public override Ensures VisitEnsures(Ensures ensures)
        {
            minLayerNum = int.MaxValue;
            maxLayerNum = -1;
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
                CheckAndAddLayers(ensures, ensures.Attributes, actionInfo.createdAtLayerNum);
            }
            return ret;
        }
        
        public override Requires VisitRequires(Requires requires)
        {
            minLayerNum = int.MaxValue;
            maxLayerNum = -1;
            canAccessSharedVars = true;
            Requires ret = base.VisitRequires(requires);
            canAccessSharedVars = false;
            CheckAndAddLayers(requires, requires.Attributes, procToActionInfo[enclosingProc].createdAtLayerNum);
            return ret;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            if (enclosingImpl == null)
                return base.VisitAssertCmd(node);
            minLayerNum = int.MaxValue;
            maxLayerNum = -1;
            canAccessSharedVars = true;
            canAccessGhostVars = true;
            Cmd ret = base.VisitAssertCmd(node);
            canAccessGhostVars = false;
            canAccessSharedVars = false;
            CheckAndAddLayers(node, node.Attributes, procToActionInfo[enclosingImpl.Proc].createdAtLayerNum);
            return ret;
        }

        private List<int> RemoveDuplicatesAndSort(List<int> attrs)
        {
            HashSet<int> layerSet = new HashSet<int>(attrs);
            List<int> layers = new List<int>(layerSet);
            layers.Sort();
            return layers;
        }

        private void CheckAndAddLayers(Absy node, QKeyValue attributes, int enclosingProcLayerNum)
        {
            List<int> attrs = RemoveDuplicatesAndSort(FindLayers(attributes));
            if (attrs.Count == 0)
            {
                Error(node, "layer not present");
                return;
            }
            absyToLayerNums[node] = new HashSet<int>();
            foreach (int layerNum in attrs)
            {
                if (layerNum == leastUnimplementedLayerNum || !AllCreatedLayerNums.Contains(layerNum))
                {
                    Error(node, "Illegal layer number");
                }
                else if (layerNum > enclosingProcLayerNum)
                {
                    Error(node, "The layer cannot be greater than the layer of enclosing procedure");
                }
                else if (maxLayerNum < layerNum && layerNum <= minLayerNum)
                {
                    absyToLayerNums[node].Add(layerNum);
                }
                else
                {
                    Error(node, string.Format("A variable being accessed in this specification is unavailable at layer {0}", layerNum));
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