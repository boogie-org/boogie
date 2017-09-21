using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
    public enum MoverType
    {
        Atomic,
        Right,
        Left,
        Both
    }

    public class AtomicAction
    {
        public Procedure proc;
        public Implementation impl;
        public MoverType moverType;
        public LayerRange layerRange;

        private List<AssertCmd> gate;

        private CodeExpr thisAction;
        private List<AssertCmd> thisGate;
        private List<Variable> thisInParams;
        private List<Variable> thisOutParams;
        private Dictionary<Variable, Expr> thisMap;

        private CodeExpr thatAction;
        private List<AssertCmd> thatGate;
        private List<Variable> thatInParams;
        private List<Variable> thatOutParams;
        private Dictionary<Variable, Expr> thatMap;

        private Dictionary<Variable, Function> triggerFuns;
        private HashSet<Variable> usedGlobalVars;
        private HashSet<Variable> modifiedGlobalVars;
        private HashSet<Variable> gateUsedGlobalVars;

        public AtomicAction(Procedure proc, Implementation impl, MoverType moverType, LayerRange layerRange)
        {
            this.proc = proc;
            this.impl = impl;
            this.moverType = moverType;
            this.layerRange = layerRange;

            this.gate = new List<AssertCmd>();

            this.thisGate = new List<AssertCmd>();
            this.thisInParams = new List<Variable>();
            this.thisOutParams = new List<Variable>();
            this.thisMap = new Dictionary<Variable, Expr>();

            this.thatGate = new List<AssertCmd>();
            this.thatInParams = new List<Variable>();
            this.thatOutParams = new List<Variable>();
            this.thatMap = new Dictionary<Variable, Expr>();

            this.triggerFuns = new Dictionary<Variable, Function>();
            
            // The gate of an atomic action is represented as asserts at the beginning of the procedure body
            // Calls to atomic actions are inlined and for most calls the gate is assumed, so we rewrite the asserts to assumes.
            // Only at specific calls the gate has to be asserted and thus we keep the asserts on the side.
            var cmds = impl.Blocks[0].Cmds;
            for (int i = 0; i < cmds.Count; i++)
            {
                AssertCmd assertCmd = cmds[i] as AssertCmd;
                if (assertCmd == null) break;
                gate.Add(assertCmd);
                cmds[i] = new AssumeCmd(assertCmd.tok, Expr.True);
            }

            SetupCopy(ref thisAction, ref thisGate, ref thisInParams, ref thisOutParams, ref thisMap, "_this");
            SetupCopy(ref thatAction, ref thatGate, ref thatInParams, ref thatOutParams, ref thatMap, "_that");

            {
                VariableCollector collector = new VariableCollector();
                collector.Visit(impl);
                usedGlobalVars = new HashSet<Variable>(collector.usedVars.Where(x => x is GlobalVariable));
            }

            List<Variable> modifiedVars = new List<Variable>();
            foreach (Cmd cmd in impl.Blocks.SelectMany(b => b.Cmds))
            {
                cmd.AddAssignedVariables(modifiedVars);
            }
            modifiedGlobalVars = new HashSet<Variable>(modifiedVars.Where(x => x is GlobalVariable));

            {
                VariableCollector collector = new VariableCollector();
                gate.ForEach(assertCmd => collector.Visit(assertCmd));
                gateUsedGlobalVars = new HashSet<Variable>(collector.usedVars.Where(x => x is GlobalVariable));
            }
        }

        private void SetupCopy(ref CodeExpr actionCopy, ref List<AssertCmd> gateCopy, ref List<Variable> inParamsCopy, ref List<Variable> outParamsCopy, ref Dictionary<Variable, Expr> varMap, string prefix)
        {
            foreach (Variable x in proc.InParams)
            {
                Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), true, x.Attributes);
                inParamsCopy.Add(xCopy);
                varMap[x] = Expr.Ident(xCopy);
            }
            foreach (Variable x in proc.OutParams)
            {
                Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), false, x.Attributes);
                outParamsCopy.Add(xCopy);
                varMap[x] = Expr.Ident(xCopy);
            }
            List<Variable> thisLocVars = new List<Variable>();
            foreach (Variable x in impl.LocVars)
            {
                Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), false);
                varMap[x] = Expr.Ident(xCopy);
                thisLocVars.Add(xCopy);
            }
            Contract.Assume(proc.TypeParameters.Count == 0);
            Substitution thisSubst = Substituter.SubstitutionFromHashtable(varMap);
            foreach (AssertCmd assertCmd in gate)
            {
                gateCopy.Add((AssertCmd)Substituter.Apply(thisSubst, assertCmd));
            }
            actionCopy = new CodeExpr(thisLocVars, SubstituteBlocks(impl.Blocks, thisSubst, prefix));
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

        public bool IsRightMover { get { return moverType == MoverType.Right || moverType == MoverType.Both; } }
        public bool IsLeftMover { get { return moverType == MoverType.Left || moverType == MoverType.Both; } }

        public bool HasAssumeCmd { get { return impl.Blocks.Any(b => b.Cmds.Any(c => c is AssumeCmd)); } }

        public bool TriviallyCommutesWith(AtomicAction other)
        {
            return this.modifiedGlobalVars.Intersect(other.usedGlobalVars).Count() == 0 &&
                   this.usedGlobalVars.Intersect(other.modifiedGlobalVars).Count() == 0;
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
    }

    public abstract class YieldingProc
    {
        public Procedure proc;
        public MoverType moverType;
        public int upperLayer;

        public YieldingProc(Procedure proc, MoverType moverType, int upperLayer)
        {
            this.proc = proc;
            this.moverType = moverType;
            this.upperLayer = upperLayer;
        }
    }

    public class SkipProc : YieldingProc
    {
        public SkipProc(Procedure proc, int upperLayer)
            : base(proc, MoverType.Both, upperLayer) { }
    }

    public class MoverProc : YieldingProc
    {
        public HashSet<Variable> modifiedGlobalVars;

        public MoverProc(Procedure proc, MoverType moverType, int upperLayer)
            : base(proc, moverType, upperLayer)
        {
            modifiedGlobalVars = new HashSet<Variable>(proc.Modifies.Select(ie => ie.Decl));
        }
    }

    public class ActionProc : YieldingProc
    {
        public AtomicAction refinedAction;

        public ActionProc(Procedure proc, AtomicAction refinedAction, int upperLayer)
            : base(proc, refinedAction.moverType, upperLayer)
        {
            this.refinedAction = refinedAction;
        }
    }

    public class InstrumentationProc
    {
        public LayerRange layerRange;
        public bool isLeaking;

        public InstrumentationProc(LayerRange layerRange, bool isLeaking)
        {
            this.isLeaking = isLeaking;
            this.layerRange = layerRange;
        }
    }

    public class SharedVariableInfo
    {
        public LayerRange layerRange;

        public SharedVariableInfo(LayerRange layerRange)
        {
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

        public static bool IsExtern(this Declaration decl) { return decl.HasAttribute("extern"); }
    }

    public class CivlTypeChecker
    {
        public CheckingContext checkingContext;

        public Program program;
        public Dictionary<Variable, SharedVariableInfo> globalVarToSharedVarInfo;
        public Dictionary<Variable, LocalVariableInfo> localVarToLocalVariableInfo;
        public Dictionary<Procedure, AtomicAction> procToAtomicAction;
        public Dictionary<Procedure, YieldingProc> procToYieldingProc;
        public Dictionary<Procedure, InstrumentationProc> procToInstrumentationProc;
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

        private List<int> FindLayers(QKeyValue kv)
        {
            List<int> layers = new List<int>();
            for (; kv != null; kv = kv.Next)
            {
                if (kv.Key != CivlAttributes.LAYER) continue;
                foreach (var o in kv.Params)
                {
                    LiteralExpr l = o as LiteralExpr;
                    if (l != null && l.isBigNum)
                    {
                        layers.Add(l.asBigNum.ToIntSafe);
                    }
                    else
                    {
                        checkingContext.Error(kv, "Layer has to be an integer.");
                    }
                }
            }
            return layers;
        }

        private LayerRange ToLayerRange(List<int> layerNums, Absy absy)
        {
            // We return min-max range for invalid declarations in order to proceed with type checking.
            if (layerNums.Count == 0)
            {
                return new LayerRange(int.MinValue, int.MaxValue);
            }
            else if (layerNums.Count == 1)
            {
                return new LayerRange(layerNums[0], layerNums[0]);
            }
            else if (layerNums.Count == 2)
            {
                if (layerNums[0] <= layerNums[1])
                {
                    return new LayerRange(layerNums[0], layerNums[1]);
                }
                else
                {
                    Error(absy, "Invalid layer range");
                    return new LayerRange(int.MinValue, int.MaxValue);
                }
            }
            else
            {
                Error(absy, "Invalid layer range");
                return new LayerRange(int.MinValue, int.MaxValue);
            }
        }

        /// Parses attributes for mover type declarations.
        /// Returns the first mover type found (or null if none is found) and issues warnings if multiple mover types are found.
        private MoverType? GetMoverType(QKeyValue kv)
        {
            MoverType? moverType = null;
            
            for (; kv != null; kv = kv.Next)
            {
                if (kv.Params.Count == 0)
                {
                    MoverType? x = null;
                    if (kv.Key == CivlAttributes.ATOMIC)
                        x = MoverType.Atomic;
                    else if (kv.Key == CivlAttributes.RIGHT)
                        x = MoverType.Right;
                    else if (kv.Key == CivlAttributes.LEFT)
                        x = MoverType.Left;
                    else if (kv.Key == CivlAttributes.BOTH)
                        x = MoverType.Both;

                    if (x.HasValue)
                    {
                        if (moverType.HasValue)
                            checkingContext.Warning(kv, string.Format("Ignoring duplicate mover type declaration ({0}).", kv.Key));
                        else
                            moverType = x;
                    }
                }
            }

            return moverType;
        }

        public CivlTypeChecker(Program program)
        {
            this.checkingContext = new CheckingContext(null);
            this.program = program;

            this.localVarToLocalVariableInfo = new Dictionary<Variable, LocalVariableInfo>();
            this.absyToLayerNums = new Dictionary<Absy, HashSet<int>>();
            this.globalVarToSharedVarInfo = new Dictionary<Variable, SharedVariableInfo>();
            this.procToAtomicAction = new Dictionary<Procedure, AtomicAction>();
            this.procToYieldingProc = new Dictionary<Procedure, YieldingProc>();
            this.procToInstrumentationProc = new Dictionary<Procedure, InstrumentationProc>();
            this.pureCallToLayer = new Dictionary<CallCmd, int>();
        }

        public void TypeCheck()
        {
            TypeCheckGlobalVariables();
            TypeCheckAtomicActions();
            TypeCheckInstrumentationProcedures();
            if (checkingContext.ErrorCount > 0) return;
            TypeCheckYieldingProcedures();
            if (checkingContext.ErrorCount > 0) return;

            // Store a list of all layers
            allLayerNums = procToYieldingProc.Values.Select(a => a.upperLayer).OrderBy(l => l).Distinct().ToList();

            foreach (var kv in absyToLayerNums)
            {
                foreach (var layer in kv.Value)
                {
                    if (!allLayerNums.Contains(layer))
                    {
                        Error(kv.Key, "No refinement on layer {0}");
                    }
                }
            }
            
            sharedVariables = globalVarToSharedVarInfo.Keys.ToList();
            sharedVariableIdentifiers = sharedVariables.Select(v => Expr.Ident(v)).ToList();

            new AttributeEraser().VisitProgram(program);
        }

        private void TypeCheckGlobalVariables()
        {
            foreach (var g in program.GlobalVariables)
            {
                LayerRange layerRange = ToLayerRange(FindLayers(g.Attributes), g);
                globalVarToSharedVarInfo[g] = new SharedVariableInfo(layerRange);
            }
        }

        private void TypeCheckAtomicActions()
        {
            AtomicActionVisitor atomicActionVisitor = new AtomicActionVisitor(this);
            // Atomic action:
            // * no {:yield}
            // * mover type
            // * layer range
            foreach (var proc in program.Procedures.Where(p => !p.IsYield()))
            {
                MoverType? moverType = GetMoverType(proc.Attributes);
                if (!moverType.HasValue) continue;

                LayerRange layerRange = ToLayerRange(FindLayers(proc.Attributes), proc);

                if (proc.Requires.Count + proc.Ensures.Count > 0)
                {
                    Error(proc, "Atomic action can not have preconditions or postconditions");
                }

                Implementation impl = program.FindImplementation(proc.Name);
                if (impl == null)
                {
                    Error(proc, "Atomic action specification missing");
                    continue;
                }

                impl.PruneUnreachableBlocks();
                Graph<Block> cfg = Program.GraphFromImpl(impl);
                if (!Graph<Block>.Acyclic(cfg, impl.Blocks[0]))
                {
                    Error(proc, "Atomic action specification can not have loops");
                    continue;
                }

                procToAtomicAction[proc] = new AtomicAction(proc, impl, moverType.Value, layerRange);

                atomicActionVisitor.VisitAction(procToAtomicAction[proc]);
            }
        }

        private void TypeCheckInstrumentationProcedures()
        {
            // Instrumentation procedure:
            // * no {:yield}
            // * no mover type
            // layer range
            foreach (var proc in program.Procedures.Where(proc => !proc.IsYield()))
            {
                LayerRange layerRange = ToLayerRange(FindLayers(proc.Attributes), proc);
                bool isLeaking = proc.Modifies.Count + proc.OutParams.Count > 0;
                procToInstrumentationProc[proc] = new InstrumentationProc(layerRange, isLeaking);
            }
            if (checkingContext.ErrorCount > 0) return;

            InstrumentationProcedureVisitor visitor = new InstrumentationProcedureVisitor(this);
            foreach (Implementation impl in program.Implementations.Where(impl => procToInstrumentationProc.ContainsKey(impl.Proc)))
            {
                visitor.VisitImplementation(impl);
            }
        }

        private void TypeCheckYieldingProcedures()
        {
            foreach (var proc in program.Procedures.Where(proc => proc.IsYield()))
            {
                int upperLayer;  // must be initialized by the following code, otherwise it is an error
                List<int> layers = FindLayers(proc.Attributes);
                if (layers.Count == 1)
                {
                    upperLayer = layers[0];
                }
                else
                {
                    Error(proc, "Expected single layer number for yielding procedure");
                    continue;
                }

                string refinesName = QKeyValue.FindStringAttribute(proc.Attributes, CivlAttributes.REFINES);
                MoverType? moverType = GetMoverType(proc.Attributes);
                if (refinesName != null && moverType.HasValue)
                {
                    Error(proc, "A yielding procedure cannot have both a refines annotation and a mover type");
                    continue;
                }

                if (refinesName != null) // proc is an action procedure
                {
                    AtomicAction refinedAction = procToAtomicAction.Values.Where(a => a.proc.Name == refinesName).FirstOrDefault();
                    if (refinedAction == null)
                    {
                        Error(proc, "Could not find refined atomic action");
                        continue;
                    }

                    // Check that layers and parameters of proc and action match!

                    procToYieldingProc[proc] = new ActionProc(proc, refinedAction, upperLayer);
                }
                else if (moverType.HasValue) // proc is a mover procedure
                {
                    procToYieldingProc[proc] = new MoverProc(proc, moverType.Value, upperLayer);
                }
                else // proc is a skip procedure
                {
                    procToYieldingProc[proc] = new SkipProc(proc, upperLayer);
                }
            }
            if (checkingContext.ErrorCount > 0) return;
            CollectLocalVariableLayers();
            if (checkingContext.ErrorCount > 0) return;

            YieldingProcVisitor visitor = new YieldingProcVisitor(this);
            foreach (var impl in program.Implementations.Where(impl => procToYieldingProc.ContainsKey(impl.Proc)))
            {
                visitor.VisitProcedure(impl.Proc);
                visitor.VisitImplementation(impl);

                // TODO: Check the modifies clause of mover procedures.
                // Calls to instrumentation procedures!

                //if (actionInfo is MoverActionInfo)
                //{
                //    var declaredModifiedVars = ((MoverActionInfo)actionInfo).modifiedGlobalVars;
                //    foreach (var callCmd in impl.Blocks.SelectMany(b => b.Cmds).OfType<CallCmd>())
                //    {
                //        if (!procToActionInfo.ContainsKey(callCmd.Proc))
                //        {
                //            throw new NotSupportedException("Modset check for mover procedures only supports calls to yielding procedures");
                //        }
                //        else
                //        {
                //            var calledAction = procToActionInfo[callCmd.Proc];
                //            HashSet<Variable> mods = null;
                //            if (calledAction is AtomicActionInfo)
                //            {
                //                mods = ((AtomicActionInfo)calledAction).modifiedGlobalVars;
                //            }
                //            else if (calledAction is MoverActionInfo)
                //            {
                //                mods = ((MoverActionInfo)calledAction).modifiedGlobalVars;
                //            }
                //            else
                //            {
                //                Debug.Assert(calledAction is SkipActionInfo);
                //                mods = new HashSet<Variable>();
                //            }
                //            foreach(var mod in mods)
                //            {
                //                if (!declaredModifiedVars.Contains(mod))
                //                {
                //                    Error(callCmd, string.Format("Modified variable {0} does not appear in modifies clause of mover procedure.", mod.Name));
                //                }
                //            }
                //        }
                //    }
                //}
            }
        }

        private void CollectLocalVariableLayers()
        {
            foreach (Procedure proc in procToYieldingProc.Keys)
            {
                foreach (var param in Enumerable.Union(proc.InParams, proc.OutParams))
                {
                    var layer = FindLocalVariableLayer(proc, param, procToYieldingProc[proc].upperLayer);
                    if (layer == int.MinValue) continue;
                    localVarToLocalVariableInfo[param] = new LocalVariableInfo(layer);
                }
            }
            foreach (Implementation impl in program.Implementations.Where(i => procToYieldingProc.ContainsKey(i.Proc)))
            {
                foreach (Variable v in impl.LocVars)
                {
                    var layer = FindLocalVariableLayer(impl, v, procToYieldingProc[impl.Proc].upperLayer);
                    localVarToLocalVariableInfo[v] = new LocalVariableInfo(layer);
                }
                for (int i = 0; i < impl.Proc.InParams.Count; i++)
                {
                    Variable v = impl.Proc.InParams[i];
                    var layer = localVarToLocalVariableInfo[v].layer;
                    localVarToLocalVariableInfo[impl.InParams[i]] = new LocalVariableInfo(layer);
                }
                for (int i = 0; i < impl.Proc.OutParams.Count; i++)
                {
                    Variable v = impl.Proc.OutParams[i];
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

        private static List<int> RemoveDuplicatesAndSort(List<int> attrs)
        {
            HashSet<int> layerSet = new HashSet<int>(attrs);
            List<int> layers = new List<int>(layerSet);
            layers.Sort();
            return layers;
        }

        public void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
        }

        private class AtomicActionVisitor : ReadOnlyVisitor
        {
            private CivlTypeChecker ctc;
            private AtomicAction atomicAction;

            public AtomicActionVisitor(CivlTypeChecker ctc)
            {
                this.ctc = ctc;
            }

            internal void VisitAction(AtomicAction atomicAction)
            {
                this.atomicAction = atomicAction;
                VisitImplementation(atomicAction.impl);
            }

            public override Procedure VisitProcedure(Procedure node)
            {
                // This visitor only has to check the body of atomic action specifications
                return node;
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                return base.VisitImplementation(node);
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                if (node.Decl is GlobalVariable)
                {
                    var sharedVarLayerRange = ctc.globalVarToSharedVarInfo[node.Decl].layerRange;
                    if (!sharedVarLayerRange.Subset(atomicAction.layerRange) || sharedVarLayerRange.lowerLayerNum == atomicAction.layerRange.lowerLayerNum) 
                        // a shared variable introduced at layer n is visible to an atomic action only at layer n+1 or higher
                        // thus, a shared variable with layer range [n,n] is not accessible by an atomic action
                    {
                        ctc.Error(node, "Shared variable is not available in atomic action specification");
                    }
                }
                return base.VisitIdentifierExpr(node);
            }

            public override Cmd VisitHavocCmd(HavocCmd node)
            {
                ctc.Error(node, "Havoc command not allowed inside an atomic actions");
                return base.VisitHavocCmd(node);
            }

            public override Cmd VisitCallCmd(CallCmd node)
            {
                ctc.Error(node, "Call command not allowed inside an atomic actions");
                return base.VisitCallCmd(node);
            }
        }

        private class InstrumentationProcedureVisitor : StandardVisitor
        {
            private CivlTypeChecker ctc;
            private InstrumentationProc instrumentationProc;

            public InstrumentationProcedureVisitor(CivlTypeChecker civlTypeChecker)
            {
                this.ctc = civlTypeChecker;
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                instrumentationProc = ctc.procToInstrumentationProc[node.Proc];
                return base.VisitImplementation(node);
            }

            public override Cmd VisitCallCmd(CallCmd callCmd)
            {
                if (!ctc.procToInstrumentationProc.ContainsKey(callCmd.Proc))
                {
                    ctc.Error(callCmd, "Instrumentation procedure can only call an instrumentation procedure");
                    return base.VisitCallCmd(callCmd);
                }
                var calleeInfo = ctc.procToInstrumentationProc[callCmd.Proc];
                if (!instrumentationProc.layerRange.Subset(calleeInfo.layerRange))
                {
                    ctc.Error(callCmd, "Caller layers must be subset of callee layers");
                }
                return base.VisitCallCmd(callCmd);
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                if (node.Decl is GlobalVariable)
                {
                    LayerRange layerRange = ctc.globalVarToSharedVarInfo[node.Decl].layerRange;
                    if (!instrumentationProc.layerRange.Subset(layerRange))
                    {
                        ctc.Error(node, "Shared variable is not accessible in instrumentation procedure");
                    }
                }
                return node;
            }
        }

        private class YieldingProcVisitor : ReadOnlyVisitor
        {
            CivlTypeChecker ctc;
            YieldingProc yieldingProc;
            bool insideSpec;
            LayerRange specLayerRange;
            int introducedLocalVarsUpperBound;

            public YieldingProcVisitor(CivlTypeChecker ctc)
            {
                this.ctc = ctc;
                this.insideSpec = false;
                introducedLocalVarsUpperBound = int.MaxValue;
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                Debug.Assert(yieldingProc == null);
                yieldingProc = ctc.procToYieldingProc[node.Proc];
                var ret = base.VisitImplementation(node);
                yieldingProc = null;
                return ret;
            }

            public override Procedure VisitProcedure(Procedure node)
            {
                if (yieldingProc != null)
                {
                    // We don't want to descend from an implementation into the corresponding procedure,
                    // otherwise the procedure would be visited twice, causing duplicate error messages.
                    return node;
                }
                yieldingProc = ctc.procToYieldingProc[node];
                var ret = base.VisitProcedure(node);
                yieldingProc = null;
                return ret;
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                if (node.Decl is GlobalVariable)
                {
                    if (insideSpec)
                    {
                        if (!specLayerRange.Subset(ctc.globalVarToSharedVarInfo[node.Decl].layerRange))
                        {
                            ctc.Error(node, "Shared variable is not available on all layers");
                        }
                    }
                    else
                    {
                        ctc.Error(node, "Shared variable can be accessed only in instrumentation procedures, atomic actions, and specifications");
                    }
                }
                else if ((node.Decl is Formal || node.Decl is Variable) && ctc.localVarToLocalVariableInfo.ContainsKey(node.Decl))
                {
                    var localVariableInfo = ctc.localVarToLocalVariableInfo[node.Decl];
                    if (introducedLocalVarsUpperBound < localVariableInfo.layer)
                    {
                        ctc.Error(node, "Introduced local variable is not accessible");
                    }
                }
                return base.VisitIdentifierExpr(node);
            }

            public override Ensures VisitEnsures(Ensures ensures)
            {
                VisitSpec(ensures);
                return ensures;
            }

            public override Requires VisitRequires(Requires requires)
            {
                VisitSpec(requires);
                return requires;
            }

            public override Cmd VisitAssertCmd(AssertCmd assert)
            {
                VisitSpec(assert);
                return assert;
            }

            public void VisitSpec<T>(T node)
                where T : Absy, ICarriesAttributes
            {
                insideSpec = true;
                CheckAndAddLayers(node);
                introducedLocalVarsUpperBound = specLayerRange.lowerLayerNum;
                base.Visit(node);
                introducedLocalVarsUpperBound = int.MaxValue;
                insideSpec = false;
            }

            private void CheckAndAddLayers<T>(T node)
                where T : Absy, ICarriesAttributes
            {
                var layers = RemoveDuplicatesAndSort(ctc.FindLayers(node.Attributes));
                if (layers.Count == 0)
                {
                    specLayerRange = new LayerRange(int.MinValue, int.MaxValue);
                    ctc.Error(node, "Specification layer(s) not present");
                    return;
                }

                specLayerRange = new LayerRange(layers.Min(), layers.Max());
                ctc.absyToLayerNums[node] = new HashSet<int>(layers);

                if (specLayerRange.upperLayerNum > yieldingProc.upperLayer)
                {
                    ctc.Error(node, "Specification layer cannot be greater than the layer of enclosing procedure");
                }
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
                    if (calleeAction is AtomicActionInfo || (calleeAction is SkipActionInfo && callerAction is MoverActionInfo))
                    {
                        if (callerLayerNum <= calleeLayerNum)
                        {
                            ctc.Error(call, "The layer of the caller must be greater than the layer of the callee");
                        }
                    }
                    else if (calleeAction is SkipActionInfo)
                    {
                        /*if (callerAction is MoverActionInfo)
                        {
                            ctc.Error(call, "A mover procedure cannot call a skip procedure");
                        }
                        else*/
                        if (callerLayerNum < calleeLayerNum)
                        {
                            ctc.Error(call, "The layer of the caller must be greater than or equal to the layer of the callee");
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
                                    ctc.Error(call, "An output variable of the enclosing implementation cannot be used as output argument for this call");
                                }
                            }
                        }
                    }
                    else if (calleeAction is MoverActionInfo)
                    {
                        if (callerLayerNum != calleeLayerNum)
                        {
                            ctc.Error(call, "The layer of the caller must be equal to the layer of the callee");
                        }
                    }

                    // check that callee is available
                    if (calleeAction.availableUptoLayerNum < callerLayerNum && !(calleeAction is MoverActionInfo)) // for mover procedures we already have a tighter check above
                    {
                        ctc.Error(call, "The callee is not available in the caller procedure");
                    }

                    if (call.IsAsync && !calleeAction.IsLeftMover)
                    {
                        ctc.Error(call, "Target of async call must be a left mover");
                    }

                    for (int i = 0; i < call.Ins.Count; i++)
                    {
                        var formal = call.Proc.InParams[i];
                        if (ctc.localVarToLocalVariableInfo.ContainsKey(formal))
                            introducedLocalVarsUpperBound = ctc.localVarToLocalVariableInfo[formal].layer;
                        else
                            introducedLocalVarsUpperBound = int.MaxValue;

                        // Visitor checks for global variable accesses and introduced local variables
                        Visit(call.Ins[i]);

                        introducedLocalVarsUpperBound = int.MaxValue;
                    }

                    for (int i = 0; i < call.Outs.Count; i++)
                    {
                        var formal = call.Proc.OutParams[i];
                        var actual = call.Outs[i].Decl;

                        // Visitor only called to check for global variable accesses
                        introducedLocalVarsUpperBound = int.MaxValue;
                        Visit(call.Outs[i]);

                        if (ctc.localVarToLocalVariableInfo.ContainsKey(formal) &&
                            (!ctc.localVarToLocalVariableInfo.ContainsKey(actual) ||
                              ctc.localVarToLocalVariableInfo[actual].layer < ctc.localVarToLocalVariableInfo[formal].layer))
                        {
                            ctc.Error(call, "Formal return parameter of call must be introduced no later than the actual parameter");
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
                                        ctc.Error(call, "Output variable must be introduced");
                                    }
                                    else if (inferredLayer != localVarToLocalVariableInfo[ie.Decl].layer)
                                    {
                                        ctc.Error(call, "All output variables must be introduced at the same layer");
                                    }
                                }
                            }
                            Debug.Assert(introducedLocalVarsUpperBound == int.MinValue);
                            foreach (var e in call.Ins)
                            {
                                Visit(e);
                                if (inferredLayer < introducedLocalVarsUpperBound)
                                {
                                    ctc.Error(call, "An introduced local variable is not accessible");
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
                            ctc.Error(call, "Creation layer of caller must be the upper bound of the layer range of callee");
                        }
                        foreach (var ie in call.Proc.Modifies)
                        {
                            if (callerLayerNum != globalVarToSharedVarInfo[ie.Decl].introLayerNum)
                            {
                                ctc.Error(call, "Creation layer of caller must be identical to the introduction layer of modified variable");
                            }
                        }
                        foreach (var ie in call.Outs)
                        {
                            if (localVarToLocalVariableInfo.ContainsKey(ie.Decl) &&
                                callerLayerNum == localVarToLocalVariableInfo[ie.Decl].layer)
                                continue;
                            ctc.Error(call, "Output variable must be introduced at the creation layer of caller");
                        }
                    }
                    return call;
                }
                else
                {
                    ctc.Error(call, "A yielding procedure can call only atomic or yielding procedures");
                    return call;
                }
            }

            public override Cmd VisitParCallCmd(ParCallCmd parCall)
            {
                // TODO: rewrite to handle mover procedures!
                int enclosingProcLayerNum = procToActionInfo[enclosingImpl.Proc].createdAtLayerNum;
                bool allLeftMover = true;
                bool allRightMover = true;
                int maxCalleeLayerNum = int.MinValue;
                int atomicActionCalleeLayerNum = int.MinValue;
                int numAtomicActions = 0;
                foreach (CallCmd iter in parCall.CallCmds)
                {
                    ActionInfo actionInfo = procToActionInfo[iter.Proc];
                    allLeftMover = allLeftMover && actionInfo.IsLeftMover;
                    allRightMover = allRightMover && actionInfo.IsRightMover;

                    if (actionInfo is MoverActionInfo)
                    {
                        ctc.Error(parCall, "Mover procedure cannot be part of a parallel call");
                    }
                    else if (actionInfo is AtomicActionInfo)
                    {
                        numAtomicActions++;
                        if (atomicActionCalleeLayerNum == int.MinValue)
                        {
                            atomicActionCalleeLayerNum = actionInfo.createdAtLayerNum;
                        }
                        else if (atomicActionCalleeLayerNum != actionInfo.createdAtLayerNum)
                        {
                            ctc.Error(parCall, "All atomic actions must be introduced at the same layer");
                        }
                    }

                    if (actionInfo.createdAtLayerNum > maxCalleeLayerNum)
                    {
                        maxCalleeLayerNum = actionInfo.createdAtLayerNum;
                    }
                }
                if (numAtomicActions > 1 && !allLeftMover && !allRightMover)
                {
                    // TODO: Error message is misleading, since there can be a single non-mover.
                    ctc.Error(parCall, "The atomic actions in the parallel call must be all right movers or all left movers");
                }
                if (atomicActionCalleeLayerNum != int.MinValue && atomicActionCalleeLayerNum < maxCalleeLayerNum)
                {
                    ctc.Error(parCall, "Atomic actions must be introduced at the highest layer");
                }
                return base.VisitParCallCmd(parCall);
            }

            public override YieldCmd VisitYieldCmd(YieldCmd node)
            {
                if (yieldingProc is MoverProc)
                {
                    ctc.Error(node, "A mover procedure cannot contain explicit yield statements");
                }
                return base.VisitYieldCmd(node);
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
