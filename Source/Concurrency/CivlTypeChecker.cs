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

    public abstract class ActionInfo
    {
        public Procedure proc;
        public MoverType moverType;
        public int createdAtLayerNum;
        public int availableUptoLayerNum;
        public bool hasImplementation;
        public bool isExtern;

        public ActionInfo(Procedure proc, MoverType moverType, int createdAtLayerNum, int availableUptoLayerNum)
        {
            this.proc = proc;
            this.moverType = moverType;
            this.createdAtLayerNum = createdAtLayerNum;
            this.availableUptoLayerNum = availableUptoLayerNum;
            this.hasImplementation = false;
            this.isExtern = proc.IsExtern();
        }

        public bool IsRightMover
        {
            get { return moverType == MoverType.Right || moverType == MoverType.Both; }
        }

        public bool IsLeftMover
        {
            get { return moverType == MoverType.Left || moverType == MoverType.Both; }
        }
    }

    public class SkipActionInfo : ActionInfo
    {
        public SkipActionInfo(Procedure proc, int createdAtLayerNum, int availableUptoLayerNum)
            : base(proc, MoverType.Both, createdAtLayerNum, availableUptoLayerNum) { }
    }

    public class MoverActionInfo : ActionInfo
    {
        public MoverActionInfo(Procedure proc, MoverType moverType, int layerNum)
            : base(proc, moverType, layerNum, layerNum) { }
    }

    public class AtomicActionInfo : ActionInfo
    {
        public List<AssertCmd> gate;
        public CodeExpr action;
        public HashSet<Variable> actionUsedGlobalVars;
        public HashSet<Variable> modifiedGlobalVars;
        public HashSet<Variable> gateUsedGlobalVars;
        public bool hasAssumeCmd;

        public List<AssertCmd> thisGate;
        public CodeExpr thisAction;
        public List<Variable> thisInParams;
        public List<Variable> thisOutParams;

        public List<AssertCmd> thatGate;
        public CodeExpr thatAction;
        public List<Variable> thatInParams;
        public List<Variable> thatOutParams;
        
        public Dictionary<Variable, Expr> thisMap;
        public Dictionary<Variable, Expr> thatMap;

        public Dictionary<Variable, Function> triggerFuns;

        public bool TriviallyCommutesWith(AtomicActionInfo other)
        {
            return this.modifiedGlobalVars.Intersect(other.actionUsedGlobalVars).Count() == 0 &&
                   this.actionUsedGlobalVars.Intersect(other.modifiedGlobalVars).Count() == 0;
        }

        public Function TriggerFunction(Variable v)
        {
            if (!triggerFuns.ContainsKey(v))
            {
                List<Variable> args = new List<Variable> { new Formal(v.tok, new TypedIdent(v.tok, "v", v.TypedIdent.Type), true) };
                Variable result = new Formal(v.tok, new TypedIdent(v.tok, "r", Type.Bool), false);
                triggerFuns[v] = new Function(v.tok, string.Format("Trigger_{0}_{1}", proc.Name, v.Name), args, result);
            }
            return triggerFuns[v];
        }

        public AtomicActionInfo(Procedure proc, Ensures ensures, MoverType moverType, int layerNum, int availableUptoLayerNum)
            : base(proc, moverType, layerNum, availableUptoLayerNum)
        {
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
            this.triggerFuns = new Dictionary<Variable, Function>();

            this.hasAssumeCmd = this.action.Blocks.Any(b => b.Cmds.Any(c => c is AssumeCmd));

            foreach (Block block in this.action.Blocks.Where(b => b.TransferCmd is ReturnExprCmd))
            {
                block.TransferCmd = new ReturnCmd(block.TransferCmd.tok);
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

    public class LocalVariableInfo
    {
        public int layer;
        public LocalVariableInfo(int layer)
        {
            this.layer = layer;
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
            this.lowerLayerNum = layerNums.Min();
            this.upperLayerNum = layerNums.Max();
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

    public static class AttributeQueryExtensionMethods
    {
        public static bool HasAttribute(this ICarriesAttributes obj, string attribute)
        { return QKeyValue.FindBoolAttribute(obj.Attributes, attribute); }

        public static bool IsPure (this Declaration decl) { return decl.HasAttribute(CivlAttributes.PURE); }
        public static bool IsYield(this Declaration decl) { return decl.HasAttribute(CivlAttributes.YIELDS); }

        public static bool IsAtomic(this ICarriesAttributes obj) { return obj.HasAttribute(CivlAttributes.ATOMIC); }
        public static bool IsLeft(this ICarriesAttributes obj) { return obj.HasAttribute(CivlAttributes.LEFT); }
        public static bool IsRight(this ICarriesAttributes obj) { return obj.HasAttribute(CivlAttributes.RIGHT); }
        public static bool IsBoth(this ICarriesAttributes obj) { return obj.HasAttribute(CivlAttributes.BOTH); }

        public static bool IsExtern(this Declaration decl) { return decl.HasAttribute("extern"); }
    }

    public class CivlTypeChecker : ReadOnlyVisitor
    {
        public CheckingContext checkingContext;
        Procedure enclosingProc;
        Implementation enclosingImpl;
        HashSet<Variable> sharedVarsAccessed;
        int introducedLocalVarsUpperBound;

        public Program program;
        public Dictionary<Variable, SharedVariableInfo> globalVarToSharedVarInfo;
        public Dictionary<Variable, LocalVariableInfo> localVarToLocalVariableInfo;
        public Dictionary<Procedure, ActionInfo> procToActionInfo;
        public Dictionary<Procedure, AtomicProcedureInfo> procToAtomicProcedureInfo;
        public Dictionary<Absy, HashSet<int>> absyToLayerNums;
        Dictionary<CallCmd, int> pureCallToLayer;

        // This collections are for convenience in later phases and are only initialized at the end of type checking.
        public List<int> allLayerNums;
        public List<Variable> sharedVariables;
        public List<IdentifierExpr> sharedVariableIdentifiers;

        public bool CallExists(CallCmd callCmd, int enclosingProcLayerNum, int layerNum)
        {
            Debug.Assert(procToAtomicProcedureInfo.ContainsKey(callCmd.Proc));
            var atomicProcedureInfo = procToAtomicProcedureInfo[callCmd.Proc];
            if (atomicProcedureInfo.isPure)
            {
                return pureCallToLayer[callCmd] <= layerNum;
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
                if (kv.Key != CivlAttributes.LAYER) continue;
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
            return layerNums.DefaultIfEmpty(int.MaxValue).Min();
        }

        private static MoverType GetMoverType(ICarriesAttributes e)
        {
            if (e.IsAtomic())
                return MoverType.Atomic;
            if (e.IsRight())
                return MoverType.Right;
            if (e.IsLeft())
                return MoverType.Left;
            if (e.IsBoth())
                return MoverType.Both;
            return MoverType.Top;
        }

        public CivlTypeChecker(Program program)
        {
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
            this.pureCallToLayer = new Dictionary<CallCmd, int>();
        }

        // Caller has to make sure sharedVarsAccessed is set correctly for the
        // currently checked procedure.
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
            TypeCheckGlobalVariables();
            TypeCheckPureProcedures();
            TypeCheckAtomicProcedures();
            if (checkingContext.ErrorCount > 0) return;
            TypeCheckYieldingProcedures();
            if (checkingContext.ErrorCount > 0) return;
            CollectLocalVariableLayers();
            if (checkingContext.ErrorCount > 0) return;

            // After collecting all procedure declarations, we can now type check the specifications and implementations.
            this.VisitProgram(program);
            if (checkingContext.ErrorCount > 0) return;

            // Store a list of all layers
            allLayerNums = Enumerable.Union(procToActionInfo.Values.Select(a => a.createdAtLayerNum),
                                            absyToLayerNums.SelectMany(x => x.Value))
                           .OrderBy(l => l)
                           .Distinct()
                           .ToList();

            
            sharedVariables = globalVarToSharedVarInfo.Keys.ToList();
            sharedVariableIdentifiers = sharedVariables.Select(v => Expr.Ident(v)).ToList();

            new AttributeEraser().VisitProgram(program);
        }

        private void TypeCheckGlobalVariables()
        {
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

        private void TypeCheckPureProcedures()
        {
            foreach (var proc in program.Procedures.Where(proc => proc.IsPure()))
            {
                if (proc.IsYield())
                {
                    Error(proc, "Pure procedure must not yield");
                    continue;
                }
                if (FindLayers(proc.Attributes).Count != 0)
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
        }

        private void TypeCheckAtomicProcedures()
        {
            // Atomic procedures (not yielding)
            foreach (var proc in program.Procedures.Where(proc => !proc.IsYield()))
            {
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
            if (checkingContext.ErrorCount > 0) return;

            // Implementations of atomic procedures
            foreach (Implementation impl in program.Implementations.Where(impl => procToAtomicProcedureInfo.ContainsKey(impl.Proc)))
            {
                AtomicProcedureInfo atomicProcedureInfo = procToAtomicProcedureInfo[impl.Proc];

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
        }

        private void TypeCheckYieldingProcedures()
        {
            foreach (var proc in program.Procedures.Where(proc => proc.IsYield()))
            {
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

                var procMoverType = GetMoverType(proc);

                // look for an atomic action spec
                var atomicActionSpecs = proc.Ensures
                                        .Select(e => new { Ensures = e, MoverType = GetMoverType(e) })
                                        .Where(aa => aa.MoverType != MoverType.Top);

                if (atomicActionSpecs.Count() > 1)
                {
                    Error(proc, "A procedure can have at most one atomic action");
                }
                else if (atomicActionSpecs.Count() == 1) // proc is an atomic action procedure
                {
                    if (availableUptoLayerNum <= createdAtLayerNum)
                    {
                        Error(proc, "Creation layer number must be less than the available upto layer number");
                    }
                    if (procMoverType != MoverType.Top)
                    {
                        Error(proc, "A procedure with an atomic action cannot have a separate mover type");
                    }

                    var atomicEnsures = atomicActionSpecs.First();
                    proc.Ensures.Remove(atomicEnsures.Ensures);
                    if (!(atomicEnsures.Ensures.Condition is CodeExpr))
                    {
                        Error(atomicEnsures.Ensures, "An atomic action must be a CodeExpr");
                    }
                    if (checkingContext.ErrorCount > 0) continue;

                    sharedVarsAccessed = new HashSet<Variable>();
                    enclosingProc = proc;
                    enclosingImpl = null;
                    base.VisitEnsures(atomicEnsures.Ensures); // Note: we invoke the base method, not the one implemented below
                    LayerRange upperBound = FindLayerRange();
                    LayerRange lowerBound = new LayerRange(createdAtLayerNum, availableUptoLayerNum);
                    if (lowerBound.Subset(upperBound))
                    {
                        procToActionInfo[proc] = new AtomicActionInfo(proc, atomicEnsures.Ensures, atomicEnsures.MoverType, createdAtLayerNum, availableUptoLayerNum);
                    }
                    else
                    {
                        Error(atomicEnsures.Ensures, "A variable being accessed in this action is unavailable");
                    }
                    sharedVarsAccessed = null;
                }
                else if (procMoverType == MoverType.Top) // proc is a skip procedure
                {
                    if (availableUptoLayerNum < createdAtLayerNum)
                    {
                        Error(proc, "Creation layer number must be no more than the available upto layer number");
                    }
                    else
                    {
                        procToActionInfo[proc] = new SkipActionInfo(proc, createdAtLayerNum, availableUptoLayerNum);
                    }
                }
                else // proc is a mover procedure
                {
                    if (availableUptoLayerNum != int.MaxValue)
                    {
                        Error(proc, "Mover procedure must have only a single layer");
                    }
                    else
                    {
                        procToActionInfo[proc] = new MoverActionInfo(proc, procMoverType, createdAtLayerNum);
                    }
                }
            }
            if (checkingContext.ErrorCount > 0) return;

            foreach (var impl in program.Implementations.Where(impl => procToActionInfo.ContainsKey(impl.Proc)))
            {
                ActionInfo actionInfo = procToActionInfo[impl.Proc];
                actionInfo.hasImplementation = true;
                if (actionInfo.isExtern)
                {
                    Error(impl.Proc, "Extern procedure cannot have an implementation");
                }
            }
        }

        private void CollectLocalVariableLayers()
        {
            foreach (Procedure proc in procToActionInfo.Keys)
            {
                foreach (var param in Enumerable.Union(proc.InParams, proc.OutParams))
                {
                    var layer = FindLocalVariableLayer(proc, param, procToActionInfo[proc].createdAtLayerNum);
                    if (layer == int.MinValue) continue;
                    localVarToLocalVariableInfo[param] = new LocalVariableInfo(layer);
                }
            }
            foreach (Implementation impl in program.Implementations.Where(i => procToActionInfo.ContainsKey(i.Proc)))
            {
                foreach (Variable v in impl.LocVars)
                {
                    var layer = FindLocalVariableLayer(impl, v, procToActionInfo[impl.Proc].createdAtLayerNum);
                    if (layer == int.MinValue) continue;
                    localVarToLocalVariableInfo[v] = new LocalVariableInfo(layer);
                }
                for (int i = 0; i < impl.Proc.InParams.Count; i++)
                {
                    Variable v = impl.Proc.InParams[i];
                    if (!localVarToLocalVariableInfo.ContainsKey(v)) continue;
                    var layer = localVarToLocalVariableInfo[v].layer;
                    localVarToLocalVariableInfo[impl.InParams[i]] = new LocalVariableInfo(layer);
                }
                for (int i = 0; i < impl.Proc.OutParams.Count; i++)
                {
                    Variable v = impl.Proc.OutParams[i];
                    if (!localVarToLocalVariableInfo.ContainsKey(v)) continue;
                    var layer = localVarToLocalVariableInfo[v].layer;
                    localVarToLocalVariableInfo[impl.OutParams[i]] = new LocalVariableInfo(layer);
                }
            }
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

        public override Cmd VisitCallCmd(CallCmd call)
        {
            var callerAction = procToActionInfo[enclosingImpl.Proc];
            int callerLayerNum = procToActionInfo[enclosingImpl.Proc].createdAtLayerNum;

            if (procToActionInfo.ContainsKey(call.Proc))
            {
                ActionInfo calleeAction = procToActionInfo[call.Proc];
                int calleeLayerNum = calleeAction.createdAtLayerNum;

                // Check that callee layer is "lower" then caller layer
                if (calleeAction is AtomicActionInfo)
                {
                    if (callerLayerNum <= calleeLayerNum)
                    {
                        Error(call, "The layer of the caller must be greater than the layer of the callee");
                    }
                }
                else if (calleeAction is SkipActionInfo)
                {
                    if (calleeAction is MoverActionInfo)
                    {
                        Error(call, "A mover procedure cannot call a skip procedure");
                    }
                    else if (callerLayerNum < calleeLayerNum)
                    {
                        Error(call, "The layer of the caller must be greater than or equal to the layer of the callee");
                    }
                    else if (callerLayerNum == calleeLayerNum && enclosingImpl.OutParams.Count > 0)
                    {
                        HashSet<Variable> callerOutParams = new HashSet<Variable>(enclosingImpl.OutParams);
                        foreach (var x in call.Outs)
                        {
                            // For refinement checking, skip procedures are just empty procedures that immediately return.
                            // Thus, the effect on output variables is havoc, which would propagate to the callers output.
                            if (callerOutParams.Contains(x.Decl))
                            {
                                Error(call, "An output variable of the enclosing implementation cannot be used as output argument for this call");
                            }
                        }
                    }
                }
                else if (calleeAction is MoverActionInfo)
                {
                    if (callerLayerNum != calleeLayerNum)
                    {
                        Error(call, "The layer of the caller must be equal to the layer of the callee");
                    }
                }

                // check that callee is available
                if (calleeAction.availableUptoLayerNum < callerLayerNum && !(calleeAction is MoverActionInfo)) // for mover procedures we already have a tighter check above
                {
                    Error(call, "The callee is not available in the caller procedure");
                }

                if (call.IsAsync && !calleeAction.IsLeftMover)
                {
                    Error(call, "Target of async call must be a left mover");
                }

                for (int i = 0; i < call.Ins.Count; i++)
                {
                    // Visitor checks for global variable accesses and introduced local variables
                    Visit(call.Ins[i]);
                    if (introducedLocalVarsUpperBound != int.MinValue)
                    {
                        var formal = call.Proc.InParams[i];
                        if (!localVarToLocalVariableInfo.ContainsKey(formal) ||
                             localVarToLocalVariableInfo[formal].layer < introducedLocalVarsUpperBound)
                        {
                            Error(call, "An introduced local variable is accessed but not available");
                        }
                        introducedLocalVarsUpperBound = int.MinValue;
                    }
                }

                for (int i = 0; i < call.Outs.Count; i++)
                {
                    var formal = call.Proc.OutParams[i];
                    var actual = call.Outs[i].Decl;

                    // Visitor only called to check for global variable accesses
                    Visit(call.Outs[i]);
                    introducedLocalVarsUpperBound = int.MinValue;

                    if (localVarToLocalVariableInfo.ContainsKey(formal) &&
                        (!localVarToLocalVariableInfo.ContainsKey(actual) ||
                          localVarToLocalVariableInfo[actual].layer < localVarToLocalVariableInfo[formal].layer))
                    {
                        Error(call, "Formal return parameter of call must be introduced no later than the actual parameter");
                    }
                }

                return call;
            }
            else if (procToAtomicProcedureInfo.ContainsKey(call.Proc))
            {
                var atomicProcedureInfo = procToAtomicProcedureInfo[call.Proc];
                if (atomicProcedureInfo.isPure)
                { // pure procedure
                    if (call.Outs.Count > 0)
                    {
                        int inferredLayer = int.MinValue;
                        foreach (var ie in call.Outs)
                        {
                            if (!localVarToLocalVariableInfo.ContainsKey(ie.Decl)) continue;
                            if (inferredLayer < localVarToLocalVariableInfo[ie.Decl].layer)
                            {
                                inferredLayer = localVarToLocalVariableInfo[ie.Decl].layer;
                            }
                        }
                        pureCallToLayer[call] = inferredLayer;
                        if (inferredLayer != int.MinValue)
                        {
                            foreach (var ie in call.Outs)
                            {
                                if (!localVarToLocalVariableInfo.ContainsKey(ie.Decl))
                                {
                                    Error(call, "Output variable must be introduced");
                                }
                                else if (inferredLayer != localVarToLocalVariableInfo[ie.Decl].layer)
                                {
                                    Error(call, "All output variables must be introduced at the same layer");
                                }
                            }
                        }
                        Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
                        foreach (var e in call.Ins)
                        {
                            Visit(e);
                            if (inferredLayer < introducedLocalVarsUpperBound)
                            {
                                Error(call, "An introduced local variable is not accessible");
                            }
                            introducedLocalVarsUpperBound = int.MinValue;
                        }
                    }
                    else
                    {
                        Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
                        int inferredLayer = int.MinValue;
                        foreach (var e in call.Ins)
                        {
                            Visit(e);
                            if (inferredLayer < introducedLocalVarsUpperBound)
                            {
                                inferredLayer = introducedLocalVarsUpperBound;
                            }
                            introducedLocalVarsUpperBound = int.MinValue;
                        }
                        pureCallToLayer[call] = inferredLayer;
                    }
                }
                else
                { // atomic procedure
                    if (callerLayerNum != atomicProcedureInfo.layerRange.upperLayerNum)
                    {
                        Error(call, "Creation layer of caller must be the upper bound of the layer range of callee");
                    }
                    foreach (var ie in call.Proc.Modifies)
                    {
                        if (callerLayerNum != globalVarToSharedVarInfo[ie.Decl].introLayerNum)
                        {
                            Error(call, "Creation layer of caller must be identical to the introduction layer of modified variable");
                        }
                    }
                    foreach (var ie in call.Outs)
                    {
                        if (localVarToLocalVariableInfo.ContainsKey(ie.Decl) &&
                            callerLayerNum == localVarToLocalVariableInfo[ie.Decl].layer)
                            continue;
                        Error(call, "Output variable must be introduced at the creation layer of caller");
                    }
                }
                return call;
            }
            else
            {
                Error(call, "A yielding procedure can call only atomic or yielding procedures");
                return call;
            }
        }

        public override Cmd VisitParCallCmd(ParCallCmd parCall)
        {
            // TODO: rewrite to handle mover procedures!
            int enclosingProcLayerNum = procToActionInfo[enclosingImpl.Proc].createdAtLayerNum;
            bool isLeftMover = true;
            bool isRightMover = true;
            int maxCalleeLayerNum = 0;
            int atomicActionCalleeLayerNum = 0;
            int numAtomicActions = 0;
            foreach (CallCmd iter in parCall.CallCmds)
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
                        Error(parCall, "All atomic actions must be introduced at the same layer");
                    }
                }
            }
            if (numAtomicActions > 1 && !isLeftMover && !isRightMover)
            {
                Error(parCall, "The atomic actions in the parallel call must be all right movers or all left movers");
            }
            if (0 < atomicActionCalleeLayerNum && atomicActionCalleeLayerNum < maxCalleeLayerNum)
            {
                Error(parCall, "Atomic actions must be introduced at the highest layer");
            }
            return base.VisitParCallCmd(parCall);
        }

        public override Cmd VisitHavocCmd(HavocCmd node)
        {
            if (enclosingProc != null)
            {
                Error(node, "Havoc command not allowed inside an atomic actions");
            }
            return base.VisitHavocCmd(node);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (node.Decl is GlobalVariable)
            {
                if (sharedVarsAccessed == null)
                {
                    Error(node, "Shared variable can be accessed only in atomic procedures, atomic actions, and specifications");
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
            sharedVarsAccessed = new HashSet<Variable>();
            Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
            base.VisitEnsures(ensures);
            CheckAndAddLayers(ensures, ensures.Attributes, procToActionInfo[enclosingProc].createdAtLayerNum);
            if (introducedLocalVarsUpperBound > Least(FindLayers(ensures.Attributes)))
            {
                Error(ensures, "An introduced local variable is accessed but not available");
            }
            introducedLocalVarsUpperBound = int.MinValue;
            sharedVarsAccessed = null;
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

        public override Cmd VisitAssertCmd(AssertCmd assert)
        {
            if (enclosingImpl == null)
            {
                // in this case, we are visiting an assert inside a CodeExpr
                return base.VisitAssertCmd(assert);
            }
            sharedVarsAccessed = new HashSet<Variable>();
            Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
            base.VisitAssertCmd(assert);
            CheckAndAddLayers(assert, assert.Attributes, procToActionInfo[enclosingImpl.Proc].createdAtLayerNum);
            if (introducedLocalVarsUpperBound > Least(FindLayers(assert.Attributes)))
            {
                Error(assert, "An introduced local variable is accessed but not available");
            }
            introducedLocalVarsUpperBound = int.MinValue;
            sharedVarsAccessed = null;
            return assert;
        }

        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            if (procToActionInfo[enclosingImpl.Proc] is MoverActionInfo)
            {
                Error(node, "A mover procedure cannot contain explicit yield statements");
            }
            return base.VisitYieldCmd(node);
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
                Procedure caller = civlTypeChecker.enclosingImpl.Proc;
                Procedure callee = node.Proc;
                if (!civlTypeChecker.procToAtomicProcedureInfo.ContainsKey(callee))
                {
                    civlTypeChecker.Error(node, "Atomic procedure can only call an atomic procedure");
                    return base.VisitCallCmd(node);
                }
                var callerInfo = civlTypeChecker.procToAtomicProcedureInfo[caller];
                var calleeInfo = civlTypeChecker.procToAtomicProcedureInfo[callee];
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

        private class AttributeEraser : ReadOnlyVisitor
        {
            public override Procedure VisitProcedure(Procedure node)
            {
                CivlAttributes.RemoveYieldsAttribute(node);
                CivlAttributes.RemoveMoverAttribute(node);
                CivlAttributes.RemoveLayerAttribute(node);
                return base.VisitProcedure(node);
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                CivlAttributes.RemoveYieldsAttribute(node);
                CivlAttributes.RemoveMoverAttribute(node);
                CivlAttributes.RemoveLayerAttribute(node);
                return base.VisitImplementation(node);
            }

            public override Requires VisitRequires(Requires node)
            {
                CivlAttributes.RemoveLayerAttribute(node);
                return base.VisitRequires(node);
            }

            public override Ensures VisitEnsures(Ensures node)
            {
                CivlAttributes.RemoveLayerAttribute(node);
                return base.VisitEnsures(node);
            }

            public override Cmd VisitAssertCmd(AssertCmd node)
            {
                CivlAttributes.RemoveLayerAttribute(node);
                return base.VisitAssertCmd(node);
            }

            public override Variable VisitVariable(Variable node)
            {
                CivlAttributes.RemoveLayerAttribute(node);
                return base.VisitVariable(node);
            }
        }
    }
}
