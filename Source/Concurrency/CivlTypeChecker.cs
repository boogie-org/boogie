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
        public List<AssertCmd> gate;
        public CodeExpr action;
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
        public Dictionary<Variable, Expr> thisMap;
        public Dictionary<Variable, Expr> thatMap;

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
            this.ensures = ensures;
            this.moverType = moverType;
            this.gate = new List<AssertCmd>();
            this.action = ensures.Condition as CodeExpr;
            this.thisGate = new List<AssertCmd>();
            this.thisInParams = new List<Variable>();
            this.thisOutParams = new List<Variable>();
            this.thatGate = new List<AssertCmd>();
            this.thatInParams = new List<Variable>();
            this.thatOutParams = new List<Variable>();
            this.hasAssumeCmd = false;
            this.thisMap = new Dictionary<Variable, Expr>();
            this.thatMap = new Dictionary<Variable, Expr>();

            foreach (Block block in this.action.Blocks)
            {
                block.Cmds.ForEach(x => this.hasAssumeCmd = this.hasAssumeCmd || x is AssumeCmd);
            }

            foreach (Block block in this.action.Blocks)
            {
                if (block.TransferCmd is ReturnExprCmd)
                {
                    block.TransferCmd = new ReturnCmd(block.TransferCmd.tok);
                }
            }

            var cmds = this.action.Blocks[0].Cmds;
            for (int i = 0; i < cmds.Count; i++)
            {
                AssertCmd assertCmd = cmds[i] as AssertCmd;
                if (assertCmd == null) break;
                this.gate.Add(assertCmd);
                cmds[i] = new AssumeCmd(assertCmd.tok, Expr.True);
            }

            foreach (Variable x in proc.InParams)
            {
                Variable thisx = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "this_" + x.Name, x.TypedIdent.Type), true, x.Attributes);
                this.thisInParams.Add(thisx);
                this.thisMap[x] = Expr.Ident(thisx);
                Variable thatx = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), true, x.Attributes);
                this.thatInParams.Add(thatx);
                this.thatMap[x] = Expr.Ident(thatx);
            }
            foreach (Variable x in proc.OutParams)
            {
                Variable thisx = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "this_" + x.Name, x.TypedIdent.Type), false, x.Attributes);
                this.thisOutParams.Add(thisx);
                this.thisMap[x] = Expr.Ident(thisx);
                Variable thatx = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), false, x.Attributes);
                this.thatOutParams.Add(thatx);
                this.thatMap[x] = Expr.Ident(thatx);
            }
            List<Variable> thisLocVars = new List<Variable>();
            List<Variable> thatLocVars = new List<Variable>();
            foreach (Variable x in this.action.LocVars)
            {
                Variable thisx = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "this_" + x.Name, x.TypedIdent.Type), false);
                thisMap[x] = Expr.Ident(thisx);
                thisLocVars.Add(thisx);
                Variable thatx = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "that_" + x.Name, x.TypedIdent.Type), false);
                thatMap[x] = Expr.Ident(thatx);
                thatLocVars.Add(thatx);
            }
            Contract.Assume(proc.TypeParameters.Count == 0);
            Substitution thisSubst = Substituter.SubstitutionFromHashtable(this.thisMap);
            Substitution thatSubst = Substituter.SubstitutionFromHashtable(this.thatMap);
            foreach (AssertCmd assertCmd in this.gate)
            {
                this.thisGate.Add((AssertCmd)Substituter.Apply(thisSubst, assertCmd));
                this.thatGate.Add((AssertCmd)Substituter.Apply(thatSubst, assertCmd));
            }
            this.thisAction = new CodeExpr(thisLocVars, SubstituteBlocks(this.action.Blocks, thisSubst, "this_"));
            this.thatAction = new CodeExpr(thatLocVars, SubstituteBlocks(this.action.Blocks, thatSubst, "that_"));

            {
                VariableCollector collector = new VariableCollector();
                collector.Visit(this.action);
                this.actionUsedGlobalVars = new HashSet<Variable>(collector.usedVars.Where(x => x is GlobalVariable));
            }

            List<Variable> modifiedVars = new List<Variable>();
            foreach (Block block in this.action.Blocks)
            {
                block.Cmds.ForEach(cmd => cmd.AddAssignedVariables(modifiedVars));
            }
            this.modifiedGlobalVars = new HashSet<Variable>(modifiedVars.Where(x => x is GlobalVariable));

            {
                VariableCollector collector = new VariableCollector();
                this.gate.ForEach(assertCmd => collector.Visit(assertCmd));
                this.gateUsedGlobalVars = new HashSet<Variable>(collector.usedVars.Where(x => x is GlobalVariable));
            }
        }

        private List<Block> SubstituteBlocks(List<Block> blocks, Substitution subst, string blockLabelPrefix)
        {
            Dictionary<Block, Block> blockMap = new Dictionary<Block, Block>();
            List<Block> otherBlocks = new List<Block>();
            foreach (Block block in blocks)
            {
                List<Cmd> otherCmds = new List<Cmd>();
                foreach (Cmd cmd in block.Cmds)
                {
                    otherCmds.Add(Substituter.Apply(subst, cmd));
                }
                Block otherBlock = new Block();
                otherBlock.Cmds = otherCmds;
                otherBlock.Label = blockLabelPrefix + block.Label;
                otherBlocks.Add(otherBlock);
                blockMap[block] = otherBlock;
            }
            foreach (Block block in blocks)
            {
                if (block.TransferCmd is ReturnCmd)
                {
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
            return otherBlocks;
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

    public class LayerRange
    {
        public int lowerLayerNum;
        public int upperLayerNum;
        public LayerRange(int layer)
        {
            this.lowerLayerNum = layer;
            this.upperLayerNum = layer;
        }
        public LayerRange(int lower, int upper)
        {
            this.lowerLayerNum = lower;
            this.upperLayerNum = upper;
        }
        public LayerRange(IEnumerable<int> layerNums)
        {
            int min = int.MaxValue;
            int max = int.MinValue;
            foreach (var layerNum in layerNums)
            {
                if (layerNum < min)
                {
                    min = layerNum;
                }
                if (max < layerNum)
                {
                    max = layerNum;
                }
            }
            this.lowerLayerNum = min;
            this.upperLayerNum = max;
        }
        public bool Contains(int layerNum)
        {
            return lowerLayerNum <= layerNum && layerNum <= upperLayerNum;
        }
        public bool Subset(int lower, int upper)
        {
            return lower <= lowerLayerNum && upperLayerNum <= upper;
        }
        public bool Equal(int lower, int upper)
        {
            return lower == lowerLayerNum && upperLayerNum == upper;
        }
        public bool Subset(LayerRange info)
        {
            return info.lowerLayerNum <= lowerLayerNum && upperLayerNum <= info.upperLayerNum;
        }
    }

    public class AtomicProcedureInfo
    {
        public bool isPure;
        public LayerRange layerRange;
        public AtomicProcedureInfo()
        {
            this.isPure = true;
            this.layerRange = null;
        }
        public AtomicProcedureInfo(LayerRange layerRange)
        {
            this.isPure = false;
            this.layerRange = layerRange;
        }
    }

    public class LocalVariableInfo
    {
        public int layer;
        public LocalVariableInfo(int layer)
        {
            this.layer = layer;
        }
    }

    public class CivlTypeChecker : ReadOnlyVisitor
    {
        CheckingContext checkingContext;
        Procedure enclosingProc;
        Implementation enclosingImpl;
        HashSet<Variable> sharedVarsAccessed;
        int introducedLocalVarsUpperBound;

        public Program program;
        public int errorCount;
        public Dictionary<Variable, SharedVariableInfo> globalVarToSharedVarInfo;
        public Dictionary<Procedure, ActionInfo> procToActionInfo;
        public Dictionary<Procedure, AtomicProcedureInfo> procToAtomicProcedureInfo;
        public Dictionary<Absy, HashSet<int>> absyToLayerNums;
        public Dictionary<Variable, LocalVariableInfo> localVarToLocalVariableInfo;
        Dictionary<CallCmd, int> pureCallLayer;

        public bool CallExists(CallCmd callCmd, int enclosingProcLayerNum, int layerNum)
        {
            Debug.Assert(procToAtomicProcedureInfo.ContainsKey(callCmd.Proc));
            var atomicProcedureInfo = procToAtomicProcedureInfo[callCmd.Proc];
            if (atomicProcedureInfo.isPure)
            {
                return pureCallLayer[callCmd] <= layerNum;
            }
            else
            {
                return enclosingProcLayerNum == layerNum;
            }
        }

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

        private static int Least(IEnumerable<int> layerNums)
        {
            int least = int.MaxValue;
            foreach (var layer in layerNums)
            {
                if (layer < least)
                {
                    least = layer;
                }
            }
            return least;
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

        public CivlTypeChecker(Program program)
        {
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.program = program;
            this.enclosingProc = null;
            this.enclosingImpl = null;
            this.sharedVarsAccessed = null;
            this.introducedLocalVarsUpperBound = int.MinValue;

            this.localVarToLocalVariableInfo = new Dictionary<Variable, LocalVariableInfo>();
            this.absyToLayerNums = new Dictionary<Absy, HashSet<int>>();
            this.globalVarToSharedVarInfo = new Dictionary<Variable, SharedVariableInfo>();
            this.procToActionInfo = new Dictionary<Procedure, ActionInfo>();
            this.procToAtomicProcedureInfo = new Dictionary<Procedure, AtomicProcedureInfo>();
            this.pureCallLayer = new Dictionary<CallCmd, int>();
            
            foreach (var g in program.GlobalVariables)
            {
                List<int> layerNums = FindLayers(g.Attributes);
                if (layerNums.Count == 0)
                {
                    // Inaccessible from  yielding and atomic procedures
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

        private HashSet<int> allLayerNums;
        public IEnumerable<int> AllLayerNums
        {
            get
            {
                if (allLayerNums == null)
                {
                    allLayerNums = new HashSet<int>();
                    foreach (ActionInfo actionInfo in procToActionInfo.Values)
                    {
                        allLayerNums.Add(actionInfo.createdAtLayerNum);
                    }
                    foreach (var layerNums in absyToLayerNums.Values)
                    {
                        foreach (var layer in layerNums)
                        {
                            allLayerNums.Add(layer);
                        }
                    }
                }
                return allLayerNums;
            }
        }

        private LayerRange FindLayerRange()
        {
            int maxIntroLayerNum = int.MinValue;
            int minHideLayerNum = int.MaxValue;
            foreach (var g in sharedVarsAccessed)
            {
                if (globalVarToSharedVarInfo[g].introLayerNum > maxIntroLayerNum)
                {
                    maxIntroLayerNum = globalVarToSharedVarInfo[g].introLayerNum;
                }
                if (globalVarToSharedVarInfo[g].hideLayerNum < minHideLayerNum)
                {
                    minHideLayerNum = globalVarToSharedVarInfo[g].hideLayerNum;
                }
            }
            return new LayerRange(maxIntroLayerNum, minHideLayerNum);
        }

        public void TypeCheck()
        {
            foreach (var proc in program.Procedures)
            {
                if (!QKeyValue.FindBoolAttribute(proc.Attributes, "pure")) continue;
                if (QKeyValue.FindBoolAttribute(proc.Attributes, "yields"))
                {
                    Error(proc, "Pure procedure must not yield");
                    continue;
                }
                if (QKeyValue.FindBoolAttribute(proc.Attributes, "layer"))
                {
                    Error(proc, "Pure procedure must not have layers");
                    continue;
                }
                if (proc.Modifies.Count > 0)
                {
                    Error(proc, "Pure procedure must not modify a global variable");
                    continue;
                }
                procToAtomicProcedureInfo[proc] = new AtomicProcedureInfo();
            }
            foreach (var proc in program.Procedures)
            {
                if (QKeyValue.FindBoolAttribute(proc.Attributes, "yields")) continue;
                var procLayerNums = FindLayers(proc.Attributes);
                if (procLayerNums.Count == 0) continue;
                foreach (IdentifierExpr ie in proc.Modifies)
                {
                    if (!globalVarToSharedVarInfo.ContainsKey(ie.Decl))
                    {
                        Error(proc, "Atomic procedure cannot modify a global variable without layer numbers");
                        continue;
                    }
                }
                int lower, upper;
                if (procLayerNums.Count == 1)
                {
                    lower = procLayerNums[0];
                    upper = procLayerNums[0];
                }
                else if (procLayerNums.Count == 2)
                {
                    lower = procLayerNums[0];
                    upper = procLayerNums[1];
                    if (lower >= upper)
                    {
                        Error(proc, "Lower layer must be less than upper layer");
                        continue;
                    }
                }
                else
                {
                    Error(proc, "Atomic procedure must specify a layer range");
                    continue;
                }
                LayerRange layerRange = new LayerRange(lower, upper);
                procToAtomicProcedureInfo[proc] = new AtomicProcedureInfo(layerRange);
            }
            if (errorCount > 0) return;

            foreach (Implementation impl in program.Implementations)
            {
                if (!procToAtomicProcedureInfo.ContainsKey(impl.Proc)) continue;
                var atomicProcedureInfo = procToAtomicProcedureInfo[impl.Proc];
                if (atomicProcedureInfo.isPure)
                {
                    this.enclosingImpl = impl;
                    (new PurityChecker(this)).VisitImplementation(impl);
                }
                else 
                {
                    this.enclosingImpl = impl;
                    this.sharedVarsAccessed = new HashSet<Variable>();
                    (new PurityChecker(this)).VisitImplementation(impl);
                    LayerRange upperBound = FindLayerRange();
                    LayerRange lowerBound = atomicProcedureInfo.layerRange;
                    if (!lowerBound.Subset(upperBound))
                    {
                        Error(impl, "Atomic procedure cannot access global variable");
                    }
                    this.sharedVarsAccessed = null;
                }
            }
            if (errorCount > 0) return; 
            
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

                    sharedVarsAccessed = new HashSet<Variable>();
                    enclosingProc = proc;
                    enclosingImpl = null;
                    base.VisitEnsures(e);
                    LayerRange upperBound = FindLayerRange();
                    LayerRange lowerBound = new LayerRange(createdAtLayerNum, availableUptoLayerNum);
                    if (lowerBound.Subset(upperBound))
                    {
                        procToActionInfo[proc] = new AtomicActionInfo(proc, e, moverType, createdAtLayerNum, availableUptoLayerNum);
                    }
                    else
                    {
                        Error(e, "A variable being accessed in this action is unavailable");
                    }
                    sharedVarsAccessed = null;
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
                ActionInfo actionInfo = procToActionInfo[impl.Proc];
                procToActionInfo[impl.Proc].hasImplementation = true;
                if (actionInfo.isExtern)
                {
                    Error(impl.Proc, "Extern procedure cannot have an implementation");
                }
            }
            if (errorCount > 0) return;

            foreach (Procedure proc in procToActionInfo.Keys)
            {
                for (int i = 0; i < proc.InParams.Count; i++)
                {
                    Variable v = proc.InParams[i];
                    var layer = FindLocalVariableLayer(proc, v, procToActionInfo[proc].createdAtLayerNum);
                    if (layer == int.MinValue) continue;
                    localVarToLocalVariableInfo[v] = new LocalVariableInfo(layer);
                }
                for (int i = 0; i < proc.OutParams.Count; i++)
                {
                    Variable v = proc.OutParams[i];
                    var layer = FindLocalVariableLayer(proc, v, procToActionInfo[proc].createdAtLayerNum);
                    if (layer == int.MinValue) continue;
                    localVarToLocalVariableInfo[v] = new LocalVariableInfo(layer);
                }
            }
            foreach (Implementation node in program.Implementations)
            {
                if (!procToActionInfo.ContainsKey(node.Proc)) continue;
                foreach (Variable v in node.LocVars)
                {
                    var layer = FindLocalVariableLayer(node, v, procToActionInfo[node.Proc].createdAtLayerNum);
                    if (layer == int.MinValue) continue;
                    localVarToLocalVariableInfo[v] = new LocalVariableInfo(layer);
                }
                for (int i = 0; i < node.Proc.InParams.Count; i++)
                {
                    Variable v = node.Proc.InParams[i];
                    if (!localVarToLocalVariableInfo.ContainsKey(v)) continue;
                    var layer = localVarToLocalVariableInfo[v].layer;
                    localVarToLocalVariableInfo[node.InParams[i]] = new LocalVariableInfo(layer);
                }
                for (int i = 0; i < node.Proc.OutParams.Count; i++)
                {
                    Variable v = node.Proc.OutParams[i];
                    if (!localVarToLocalVariableInfo.ContainsKey(v)) continue;
                    var layer = localVarToLocalVariableInfo[v].layer;
                    localVarToLocalVariableInfo[node.OutParams[i]] = new LocalVariableInfo(layer);
                }
            }
            if (errorCount > 0) return; 
            
            this.VisitProgram(program);
            if (errorCount > 0) return;
            YieldTypeChecker.PerformYieldSafeCheck(this);
            new LayerEraser().VisitProgram(program);
        }

        public IEnumerable<Variable> SharedVariables
        {
            get { return this.globalVarToSharedVarInfo.Keys; }
        }

        private int FindLocalVariableLayer(Declaration decl, Variable v, int enclosingProcLayerNum)
        {
            var layers = FindLayers(v.Attributes);
            if (layers.Count == 0) return int.MinValue;
            if (layers.Count > 1)
            {
                Error(decl, "Incorrect number of layers");
                return int.MinValue;
            }
            if (layers[0] > enclosingProcLayerNum)
            {
                Error(decl, "Layer of local variable cannot be greater than the creation layer of enclosing procedure");
                return int.MinValue;
            }
            return layers[0];
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            if (!procToActionInfo.ContainsKey(node.Proc))
            {
                return node;
            }
            this.enclosingImpl = node;
            this.enclosingProc = null;
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
                for (int i = 0; i < node.Ins.Count; i++)
                {
                    Visit(node.Ins[i]);
                    if (introducedLocalVarsUpperBound != int.MinValue)
                    {
                        var formal = node.Proc.InParams[i];
                        if (!localVarToLocalVariableInfo.ContainsKey(formal) ||
                            introducedLocalVarsUpperBound > localVarToLocalVariableInfo[formal].layer)
                        {
                            Error(node, "An introduced local variable is accessed but not available");
                        }
                        introducedLocalVarsUpperBound = int.MinValue;
                    }
                }
                for (int i = 0; i < node.Outs.Count; i++)
                {
                    var formal = node.Proc.OutParams[i];
                    if (!localVarToLocalVariableInfo.ContainsKey(formal)) continue;
                    var actual = node.Outs[i].Decl;
                    if (localVarToLocalVariableInfo.ContainsKey(actual) && 
                        localVarToLocalVariableInfo[formal].layer <= localVarToLocalVariableInfo[actual].layer)
                        continue;
                    Error(node, "Formal parameter of call must be introduced no later than the actual parameter");
                }
                return node;
            }
            else if (procToAtomicProcedureInfo.ContainsKey(node.Proc))
            {
                var atomicProcedureInfo = procToAtomicProcedureInfo[node.Proc];                
                if (atomicProcedureInfo.isPure)
                {
                    if (node.Outs.Count > 0)
                    {
                        int inferredLayer = int.MinValue;
                        foreach (var ie in node.Outs)
                        {
                            if (!localVarToLocalVariableInfo.ContainsKey(ie.Decl)) continue;
                            if (inferredLayer < localVarToLocalVariableInfo[ie.Decl].layer)
                            {
                                inferredLayer = localVarToLocalVariableInfo[ie.Decl].layer;
                            }
                        }
                        pureCallLayer[node] = inferredLayer;
                        if (inferredLayer != int.MinValue)
                        {
                            foreach (var ie in node.Outs)
                            {
                                if (!localVarToLocalVariableInfo.ContainsKey(ie.Decl))
                                {
                                    Error(node, "Output variable must be introduced");
                                }
                                else if (inferredLayer != localVarToLocalVariableInfo[ie.Decl].layer)
                                {
                                    Error(node, "All output variables must be introduced at the same layer");
                                }
                            }
                        }
                        Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
                        foreach (var e in node.Ins)
                        {
                            Visit(e);
                            if (inferredLayer < introducedLocalVarsUpperBound)
                            {
                                Error(node, "An introduced local variable is not accessible");
                            }
                            introducedLocalVarsUpperBound = int.MinValue;
                        }
                    }
                    else
                    {
                        Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
                        int inferredLayer = int.MinValue;
                        foreach (var e in node.Ins)
                        {
                            Visit(e);
                            if (inferredLayer < introducedLocalVarsUpperBound)
                            {
                                inferredLayer = introducedLocalVarsUpperBound;
                            }
                            introducedLocalVarsUpperBound = int.MinValue;
                        }
                        pureCallLayer[node] = inferredLayer;
                    }
                }
                else
                {
                    if (enclosingProcLayerNum != atomicProcedureInfo.layerRange.upperLayerNum)
                    {
                        Error(node, "Creation layer of caller must be the upper bound of the layer range of callee");
                    }
                    foreach (var ie in node.Proc.Modifies)
                    {
                        if (enclosingProcLayerNum != globalVarToSharedVarInfo[ie.Decl].introLayerNum)
                        {
                            Error(node, "Creation layer of caller must be identical to the introduction layer of modified variable");
                        }
                    }
                    foreach (var ie in node.Outs)
                    {
                        if (localVarToLocalVariableInfo.ContainsKey(ie.Decl) &&
                            enclosingProcLayerNum == localVarToLocalVariableInfo[ie.Decl].layer)
                            continue;
                        Error(node, "Output variable must be introduced at the creation layer of caller");
                    }
                }
                return node;
            }
            else  
            {
                Error(node, "A yielding procedure can call only atomic or yielding procedures");
                return node;
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

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (node.Decl is GlobalVariable)
            {
                if (sharedVarsAccessed == null)
                {
                    Error(node, "Shared variable can be accessed only in atomic actions or specifications");
                }
                else if (this.globalVarToSharedVarInfo.ContainsKey(node.Decl))
                {
                    sharedVarsAccessed.Add(node.Decl);
                }
                else
                {
                    Error(node, "Accessed shared variable must have layer annotation");
                }
            }
            else if ((node.Decl is Formal || node.Decl is Variable) && localVarToLocalVariableInfo.ContainsKey(node.Decl))
            {
                var localVariableInfo = localVarToLocalVariableInfo[node.Decl];
                if (introducedLocalVarsUpperBound < localVariableInfo.layer)
                {
                    introducedLocalVarsUpperBound = localVariableInfo.layer;
                }
            } 
            return base.VisitIdentifierExpr(node);
        }

        public override Ensures VisitEnsures(Ensures ensures)
        {
            ActionInfo actionInfo = procToActionInfo[enclosingProc];
            AtomicActionInfo atomicActionInfo = actionInfo as AtomicActionInfo;
            if (atomicActionInfo != null && atomicActionInfo.ensures == ensures)
            {
                // This case has already been checked
            }
            else
            {
                sharedVarsAccessed = new HashSet<Variable>();
                Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
                base.VisitEnsures(ensures); 
                CheckAndAddLayers(ensures, ensures.Attributes, actionInfo.createdAtLayerNum);
                if (introducedLocalVarsUpperBound > Least(FindLayers(ensures.Attributes)))
                {
                    Error(ensures, "An introduced local variable is accessed but not available");
                }
                introducedLocalVarsUpperBound = int.MinValue;
                sharedVarsAccessed = null;
            }
            return ensures;
        }

        public override Requires VisitRequires(Requires requires)
        {
            sharedVarsAccessed = new HashSet<Variable>();
            Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
            base.VisitRequires(requires);
            CheckAndAddLayers(requires, requires.Attributes, procToActionInfo[enclosingProc].createdAtLayerNum);
            if (introducedLocalVarsUpperBound > Least(FindLayers(requires.Attributes)))
            {
                Error(requires, "An introduced local variable is accessed but not available");
            }
            introducedLocalVarsUpperBound = int.MinValue;
            sharedVarsAccessed = null;
            return requires;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            if (enclosingImpl == null)
            {
                // in this case, we are visiting an assert inside a CodeExpr
                return base.VisitAssertCmd(node);
            }
            sharedVarsAccessed = new HashSet<Variable>();
            Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
            base.VisitAssertCmd(node);
            CheckAndAddLayers(node, node.Attributes, procToActionInfo[enclosingImpl.Proc].createdAtLayerNum);
            if (introducedLocalVarsUpperBound > Least(FindLayers(node.Attributes)))
            {
                Error(node, "An introduced local variable is accessed but not available");
            }
            introducedLocalVarsUpperBound = int.MinValue;
            sharedVarsAccessed = null;
            return node;
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
            LayerRange upperBound = FindLayerRange();
            absyToLayerNums[node] = new HashSet<int>();
            foreach (int layerNum in attrs)
            {
                if (layerNum > enclosingProcLayerNum)
                {
                    Error(node, "The layer cannot be greater than the layer of enclosing procedure");
                }
                else if (upperBound.Contains(layerNum))
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

        private class PurityChecker : StandardVisitor
        {
            private CivlTypeChecker civlTypeChecker;

            public PurityChecker(CivlTypeChecker civlTypeChecker)
            {
                this.civlTypeChecker = civlTypeChecker;
            }
            
            public override Cmd VisitCallCmd(CallCmd node)
            {
                Procedure enclosingProc = civlTypeChecker.enclosingImpl.Proc;
                if (!civlTypeChecker.procToAtomicProcedureInfo.ContainsKey(node.Proc))
                {
                    civlTypeChecker.Error(node, "Atomic procedure can only call an atomic procedure");
                    return base.VisitCallCmd(node);
                }
                var callerInfo = civlTypeChecker.procToAtomicProcedureInfo[enclosingProc];
                var calleeInfo = civlTypeChecker.procToAtomicProcedureInfo[node.Proc];
                if (calleeInfo.isPure)
                {
                    // do nothing
                }
                else if (callerInfo.isPure)
                {
                    civlTypeChecker.Error(node, "Pure procedure can only call pure procedures");
                }
                else if (!callerInfo.layerRange.Subset(calleeInfo.layerRange))
                {
                    civlTypeChecker.Error(node, "Caller layers must be subset of callee layers");
                }
                return base.VisitCallCmd(node);
            }

            public override Cmd VisitParCallCmd(ParCallCmd node)
            {
                civlTypeChecker.Error(node, "Atomic procedures cannot make parallel calls");
                return node;
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                Procedure enclosingProc = civlTypeChecker.enclosingImpl.Proc;
                if (node.Decl is GlobalVariable)
                {
                    if (civlTypeChecker.procToAtomicProcedureInfo[enclosingProc].isPure)
                    {
                        civlTypeChecker.Error(node, "Pure procedure cannot access global variables");
                    } 
                    else if (!civlTypeChecker.globalVarToSharedVarInfo.ContainsKey(node.Decl))
                    {
                        civlTypeChecker.Error(node, "Atomic procedure cannot access a global variable without layer numbers");
                    } 
                    else 
                    {
                        civlTypeChecker.sharedVarsAccessed.Add(node.Decl);
                    }
                }
                return node;
            }
        }
    }
}
