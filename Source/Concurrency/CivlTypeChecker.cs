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

        public List<AssertCmd> gate;

        public CodeExpr thisAction;
        public List<AssertCmd> thisGate;
        public List<Variable> thisInParams;
        public List<Variable> thisOutParams;
        public Dictionary<Variable, Expr> thisMap;

        public CodeExpr thatAction;
        public List<AssertCmd> thatGate;
        public List<Variable> thatInParams;
        public List<Variable> thatOutParams;
        public Dictionary<Variable, Expr> thatMap;

        public Dictionary<Variable, Function> triggerFuns;
        public HashSet<Variable> usedGlobalVars;
        public HashSet<Variable> modifiedGlobalVars;
        public HashSet<Variable> gateUsedGlobalVars;

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
            
            // The gate of an atomic action is represented as asserts at the beginning of the procedure body.
            // Calls to atomic actions are inlined and for most calls the gate is assumed, so we rewrite the asserts to assumes.
            // Only at specific calls the gate has to be asserted and thus we keep the asserts on the side.
            var cmds = impl.Blocks[0].Cmds;
            for (int i = 0; i < cmds.Count; i++)
            {
                AssertCmd assertCmd = cmds[i] as AssertCmd;
                if (assertCmd == null) break;
                gate.Add(assertCmd);
                cmds[i] = new AssumeCmd(assertCmd.tok, assertCmd.Expr);
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

        // TODO: Check usage!
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

        public bool IsRightMover { get { return moverType == MoverType.Right || moverType == MoverType.Both; } }
        public bool IsLeftMover { get { return moverType == MoverType.Left || moverType == MoverType.Both; } }
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
        public bool isLeaky;

        public InstrumentationProc(LayerRange layerRange, bool isLeaking)
        {
            this.isLeaky = isLeaking;
            this.layerRange = layerRange;
        }
    }

    public class LayerRange
    {
        public int lowerLayerNum;
        public int upperLayerNum;

        public static LayerRange MinMax = new LayerRange(int.MinValue, int.MaxValue);

        public LayerRange(int layer) : this(layer, layer) { }

        public LayerRange(int lower, int upper)
        {
            Debug.Assert(lower <= upper);
            this.lowerLayerNum = lower;
            this.upperLayerNum = upper;
        }

        public bool Contains(int layerNum)
        {
            return lowerLayerNum <= layerNum && layerNum <= upperLayerNum;
        }

        public bool Subset(LayerRange other)
        {
            return other.lowerLayerNum <= lowerLayerNum && upperLayerNum <= other.upperLayerNum;
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

        // Don't access directly!
        // TypeCheckLocalVariables initializes globalVarToLayerRange such that variables with min-max layer range are not explicitely stored.
        // Similarly for localVartoIntroLayer / TypeCheckLocalVariables.
        // Use public access methods.
        private Dictionary<Variable, LayerRange> globalVarToLayerRange;
        private Dictionary<Variable, int> localVarToIntroLayer;

        public Dictionary<Procedure, AtomicAction> procToAtomicAction;
        public Dictionary<Procedure, YieldingProc> procToYieldingProc;
        public Dictionary<Procedure, InstrumentationProc> procToInstrumentationProc;

        public Dictionary<Absy, HashSet<int>> absyToLayerNums;
        Dictionary<CallCmd, int> instrumentationCallToLayer;

        // This collections are for convenience in later phases and are only initialized at the end of type checking.
        public List<int> allLayerNums;
        public List<Variable> sharedVariables;
        public List<IdentifierExpr> sharedVariableIdentifiers;

        public CivlTypeChecker(Program program)
        {
            this.checkingContext = new CheckingContext(null);
            this.program = program;

            this.globalVarToLayerRange = new Dictionary<Variable, LayerRange>();
            this.localVarToIntroLayer = new Dictionary<Variable, int>();
            this.absyToLayerNums = new Dictionary<Absy, HashSet<int>>();
            this.procToAtomicAction = new Dictionary<Procedure, AtomicAction>();
            this.procToYieldingProc = new Dictionary<Procedure, YieldingProc>();
            this.procToInstrumentationProc = new Dictionary<Procedure, InstrumentationProc>();
            this.instrumentationCallToLayer = new Dictionary<CallCmd, int>();
        }

        public bool CallExists(CallCmd callCmd, int enclosingProcLayerNum, int layerNum)
        {
            Debug.Assert(procToInstrumentationProc.ContainsKey(callCmd.Proc));
            var instrumentationProc = procToInstrumentationProc[callCmd.Proc];
            if (instrumentationProc.isLeaky)
            {
                return enclosingProcLayerNum == layerNum;
            }
            else
            {
                return instrumentationCallToLayer[callCmd] <= layerNum;
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
                return LayerRange.MinMax;
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
                    return LayerRange.MinMax;
                }
            }
            else
            {
                Error(absy, "Invalid layer range");
                return LayerRange.MinMax;
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

            //sharedVariables = globalVarToLayerRange.Keys.ToList();
            sharedVariables = program.GlobalVariables.ToList<Variable>();
            sharedVariableIdentifiers = sharedVariables.Select(v => Expr.Ident(v)).ToList();

            new AttributeEraser().VisitProgram(program);
        }

        private void TypeCheckGlobalVariables()
        {
            foreach (var g in program.GlobalVariables)
            {
                var layerRange = ToLayerRange(FindLayers(g.Attributes), g);
                if (layerRange != LayerRange.MinMax)
                    globalVarToLayerRange[g] = layerRange;
            }
        }

        public LayerRange GlobalVariableLayerRange(Variable g)
        {
            if (globalVarToLayerRange.ContainsKey(g))
                return globalVarToLayerRange[g];
            return LayerRange.MinMax;
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

                var actionImpls = program.Implementations.Where(i => i.Name == proc.Name).ToList();
                if (actionImpls.Count == 0)
                {
                    Error(proc, "Atomic action specification missing");
                    continue;
                }
                else if (actionImpls.Count > 1)
                {
                    Error(proc, "More then one atomic action specification provided");
                    continue;
                }
                Implementation impl = actionImpls[0];

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
            foreach (var proc in program.Procedures.Where(proc => !proc.IsYield() && !GetMoverType(proc.Attributes).HasValue))
            {
                LayerRange layerRange = ToLayerRange(FindLayers(proc.Attributes), proc);
                bool isLeaky = proc.Modifies.Count + proc.OutParams.Count > 0;
                foreach (var ie in proc.Modifies)
                {
                    if (GlobalVariableLayerRange(ie.Decl).lowerLayerNum != layerRange.lowerLayerNum)
                    {
                        Error(ie, "Instrumentation procedures can modify shared variables only on their introduction layer");
                    }
                }

                procToInstrumentationProc[proc] = new InstrumentationProc(layerRange, isLeaky);
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

                    // TODO: Check that layers and parameters of proc and action match!

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
            TypeCheckLocalVariables();
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

        private void TypeCheckLocalVariables()
        {
            // Local variable with no declared introduction layer implicitely have layer int.MinValue.
            // However, to save space and avoid hash collisions, we do not explicitely store variables with layer int.MinValue.

            // First we collect in and out parameter layers from procedures
            foreach (Procedure proc in procToYieldingProc.Keys)
            {
                foreach (var param in Enumerable.Union(proc.InParams, proc.OutParams))
                {
                    var layer = FindLocalVariableLayer(proc, param, procToYieldingProc[proc].upperLayer);
                    if (layer != int.MinValue)
                        localVarToIntroLayer[param] = layer;
                }
            }
            foreach (Implementation impl in program.Implementations.Where(i => procToYieldingProc.ContainsKey(i.Proc)))
            {
                // then we collect the layers of local variables in implementations
                foreach (Variable v in impl.LocVars)
                {
                    var layer = FindLocalVariableLayer(impl, v, procToYieldingProc[impl.Proc].upperLayer);
                    if (layer != int.MinValue)
                        localVarToIntroLayer[v] = layer;
                }
                // and finally just copy the layer information from procedure parameters to their corresponding implementation parameter
                // (i.e., layer declarations are only taken from procedures, not implementations)
                for (int i = 0; i < impl.Proc.InParams.Count; i++)
                {
                    Variable v = impl.Proc.InParams[i];
                    if (localVarToIntroLayer.ContainsKey(v))
                        localVarToIntroLayer[impl.InParams[i]] = localVarToIntroLayer[v];
                }
                for (int i = 0; i < impl.Proc.OutParams.Count; i++)
                {
                    Variable v = impl.Proc.OutParams[i];
                    if (localVarToIntroLayer.ContainsKey(v))
                        localVarToIntroLayer[impl.OutParams[i]] = localVarToIntroLayer[v];
                }
            }
        }

        public int LocalVariableIntroLayer(Variable l)
        {
            if (localVarToIntroLayer.ContainsKey(l))
                return localVarToIntroLayer[l];
            return int.MinValue;
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
                    var sharedVarLayerRange = ctc.GlobalVariableLayerRange(node.Decl);
                    if (!atomicAction.layerRange.Subset(sharedVarLayerRange) || sharedVarLayerRange.lowerLayerNum == atomicAction.layerRange.lowerLayerNum) 
                        // a shared variable introduced at layer n is visible to an atomic action only at layer n+1 or higher
                        // thus, a shared variable with layer range [n,n] is not accessible by an atomic action
                    {
                        ctc.Error(node, string.Format("Shared variable {0} is not available in atomic action specification", node.Decl.Name));
                    }
                }
                return base.VisitIdentifierExpr(node);
            }

            public override Cmd VisitHavocCmd(HavocCmd node)
            {
                ctc.Error(node, "Havoc command not allowed inside an atomic action");
                return base.VisitHavocCmd(node);
            }

            public override Cmd VisitCallCmd(CallCmd node)
            {
                ctc.Error(node, "Call command not allowed inside an atomic actions");
                return base.VisitCallCmd(node);
            }
        }

        private class InstrumentationProcedureVisitor : ReadOnlyVisitor
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
                InstrumentationProc calleeProc = ctc.procToInstrumentationProc[callCmd.Proc];
                if (!instrumentationProc.layerRange.Subset(calleeProc.layerRange))
                {
                    ctc.Error(callCmd, "Caller layers must be subset of callee layers");
                }
                return base.VisitCallCmd(callCmd);
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                if (node.Decl is GlobalVariable)
                {
                    LayerRange globalVarLayerRange = ctc.GlobalVariableLayerRange(node.Decl);
                    if (!instrumentationProc.layerRange.Subset(globalVarLayerRange))
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
            List<IdentifierExpr> sharedVariableAccesses;
            List<IdentifierExpr> localVariableAccesses;

            Implementation enclosingImpl;

            public YieldingProcVisitor(CivlTypeChecker ctc)
            {
                this.ctc = ctc;

                sharedVariableAccesses = null;
                localVariableAccesses = null;

                enclosingImpl = null;
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                Debug.Assert(yieldingProc == null);
                enclosingImpl = node;
                yieldingProc = ctc.procToYieldingProc[node.Proc];
                var ret = base.VisitImplementation(node);
                enclosingImpl = null;
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
                    if (sharedVariableAccesses != null)
                    {
                        sharedVariableAccesses.Add(node);
                    }
                    else
                    {
                        ctc.Error(node, "Shared variable can be accessed only in instrumentation procedures, atomic actions, and specifications");
                    }
                }
                else
                {
                    if (localVariableAccesses != null)
                    {
                        localVariableAccesses.Add(node);
                    }
                }
                return base.VisitIdentifierExpr(node);
            }

            // All preconditions, postconditions, and assertions are treated similarly:
            // * VisitSpecPre activates collection of accessed global and local variables
            // * Call to base visitor actually does the collection
            // * VisitSpecPost checks the consistency of layer annotations

            public override Ensures VisitEnsures(Ensures ensures)
            {
                VisitSpecPre();
                base.VisitEnsures(ensures);
                VisitSpecPost(ensures);
                return ensures;
            }

            public override Requires VisitRequires(Requires requires)
            {
                VisitSpecPre();
                base.VisitRequires(requires);
                VisitSpecPost(requires);
                return requires;
            }

            public override Cmd VisitAssertCmd(AssertCmd assert)
            {
                VisitSpecPre();
                base.VisitAssertCmd(assert);
                VisitSpecPost(assert);
                return assert;
            }

            public void VisitSpecPre()
            {
                sharedVariableAccesses = new List<IdentifierExpr>();
                localVariableAccesses = new List<IdentifierExpr>();
            }

            public void VisitSpecPost<T>(T node)
                where T : Absy, ICarriesAttributes
            {
                var specLayers = ctc.FindLayers(node.Attributes).Distinct().OrderBy(l => l).ToList();
                if (specLayers.Count == 0)
                {
                    ctc.Error(node, "Specification layer(s) not present");
                    return;
                }

                ctc.absyToLayerNums[node] = new HashSet<int>(specLayers);

                foreach (var layer in specLayers)
                {
                    if (layer > yieldingProc.upperLayer)
                    {
                        ctc.Error(node, string.Format("Specification layer {0} is greater than enclosing procedure layer {1}", layer, yieldingProc.upperLayer));
                    }
                    foreach (var ie in sharedVariableAccesses)
                    {
                        if (!ctc.GlobalVariableLayerRange(ie.Decl).Contains(layer))
                        {
                            ctc.Error(ie, string.Format("Global variable {0} is not available at layer {1}", ie.Name, layer));
                        }
                    }
                    foreach (var ie in localVariableAccesses)
                    {
                        if (layer < ctc.LocalVariableIntroLayer(ie.Decl))
                        {
                            ctc.Error(ie, string.Format("Local variable {0} is not available at layer {1}", ie.Name, layer));
                        }
                    }
                }

                sharedVariableAccesses = null;
                localVariableAccesses = null;
            }

            public override Cmd VisitCallCmd(CallCmd call)
            {
                YieldingProc callerProc = yieldingProc;

                if (ctc.procToYieldingProc.ContainsKey(call.Proc))
                {
                    VisitYieldingProcCallCmd(call, callerProc, ctc.procToYieldingProc[call.Proc]);
                }
                else if (ctc.procToInstrumentationProc.ContainsKey(call.Proc))
                {
                    VisitInstrumentationProcCallCmd(call, callerProc, ctc.procToInstrumentationProc[call.Proc]);

                }
                else
                {
                    ctc.Error(call, "A yielding procedure can call only atomic or yielding procedures");
                }
                return call;
            }

            private void VisitYieldingProcCallCmd (CallCmd call, YieldingProc callerProc, YieldingProc calleeProc)
            {
                if (calleeProc is ActionProc)
                {
                    if (callerProc.upperLayer <= calleeProc.upperLayer)
                    {
                        ctc.Error(call, "The layer of the caller must be greater than the layer of the callee");
                    }
                    if (((ActionProc)calleeProc).refinedAction.layerRange.upperLayerNum < callerProc.upperLayer)
                    {
                        ctc.Error(call, "The callee is not available in the caller procedure");
                    }
                }
                else if (calleeProc is SkipProc)
                {
                    if (callerProc is MoverProc && callerProc.upperLayer <= calleeProc.upperLayer)
                    {
                        ctc.Error(call, "The layer of the caller must be greater than the layer of the callee");
                    }
                    else if (callerProc.upperLayer < calleeProc.upperLayer)
                    {
                        ctc.Error(call, "The layer of the caller must be greater than or equal to the layer of the callee");
                    }
                    else if (callerProc.upperLayer == calleeProc.upperLayer && enclosingImpl.OutParams.Count > 0)
                    {
                        // TODO: Is this condition really necessary? If not, enclosingImpl can be eliminated.
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
                else if (calleeProc is MoverProc)
                {
                    if (callerProc.upperLayer != calleeProc.upperLayer)
                    {
                        ctc.Error(call, "The layer of the caller must be equal to the layer of the callee");
                    }
                }

                if (call.IsAsync && !calleeProc.IsLeftMover)
                {
                    ctc.Error(call, "Target of async call must be a left mover");
                }

                for (int i = 0; i < call.Ins.Count; i++)
                {
                    // Visitor checks for global variable accesses and collects accessed local variables
                    localVariableAccesses = new List<IdentifierExpr>();
                    Visit(call.Ins[i]);

                    var formalIntroLayer = ctc.LocalVariableIntroLayer(call.Proc.InParams[i]);
                    foreach (var ie in localVariableAccesses)
                    {
                        var actualIntroLayer = ctc.LocalVariableIntroLayer(ie.Decl);
                        if (ctc.LocalVariableIntroLayer(ie.Decl) > formalIntroLayer)
                        {
                            ctc.Error(ie, string.Format("Variable {0} introduced on layer {1} can not be passed to formal parameter introduced on layer {2}", ie.Decl.Name, actualIntroLayer, formalIntroLayer));
                        }
                    }

                    localVariableAccesses = null;
                }

                for (int i = 0; i < call.Outs.Count; i++)
                {
                    Variable formal = call.Proc.OutParams[i];
                    IdentifierExpr actualIdentifierExpr = call.Outs[i];
                    Variable actual = actualIdentifierExpr.Decl;
                    int formalIntroLayer = ctc.LocalVariableIntroLayer(formal);
                    int actualIntroLayer = ctc.LocalVariableIntroLayer(actual);

                    // Visitor only called to check for global variable accesses
                    Visit(actualIdentifierExpr);

                    if (actualIntroLayer < formalIntroLayer)
                    {
                        ctc.Error(actualIdentifierExpr, "Formal return parameter of call must be introduced no later than the actual parameter");
                    }
                }
            }

            private void VisitInstrumentationProcCallCmd(CallCmd call, YieldingProc callerProc, InstrumentationProc calleeProc)
            {
                if (!calleeProc.layerRange.Contains(callerProc.upperLayer))
                {
                    ctc.Error(call, string.Format("Called instrumentation procedure {0} is not available at layer {1}", callerProc.proc.Name, callerProc.upperLayer));
                    return;
                }

                if (calleeProc.isLeaky)
                {
                    // Call to leaky instrumentation procedure only exists at the upper layer of caller yielding procedure.
                    // Thus, all local variables are already introduced and we only have to check output variables.
                    foreach (var ie in call.Outs)
                    {
                        if (ctc.LocalVariableIntroLayer(ie.Decl) != callerProc.upperLayer)
                        {
                            ctc.Error(ie, string.Format("Output variable {0} must be introduced at layer {1}", ie.Decl.Name, callerProc.upperLayer));
                        }
                    }
                }
                else
                {
                    // Call to non-leaky instrumentation procedure exists as soon as all local variables used as input are available.
                    // I.e., we compute the maximum introduction layer of all local variables used as input.
                    foreach (var e in call.Ins)
                    {
                        localVariableAccesses = new List<IdentifierExpr>();
                        Visit(e);
                        ctc.instrumentationCallToLayer[call] = localVariableAccesses.Max(ie => ctc.LocalVariableIntroLayer(ie.Decl));
                        localVariableAccesses = null;
                    }
                }
            }

            public override Cmd VisitParCallCmd(ParCallCmd parCall)
            {
                bool allLeftMover = true;
                bool allRightMover = true;
                int maxCalleeLayerNum = int.MinValue;
                int atomicActionCalleeLayerNum = int.MinValue;
                int numAtomicActions = 0;
                foreach (CallCmd iter in parCall.CallCmds)
                {
                    YieldingProc callee = ctc.procToYieldingProc[iter.Proc];
                    allLeftMover = allLeftMover && callee.IsLeftMover;
                    allRightMover = allRightMover && callee.IsRightMover;

                    if (callee is MoverProc)
                    {
                        ctc.Error(parCall, "Mover procedure cannot be part of a parallel call");
                    }
                    else if (callee is ActionProc)
                    {
                        numAtomicActions++;
                        if (atomicActionCalleeLayerNum == int.MinValue)
                        {
                            atomicActionCalleeLayerNum = callee.upperLayer;
                        }
                        else if (atomicActionCalleeLayerNum != callee.upperLayer)
                        {
                            ctc.Error(parCall, "All atomic actions must be introduced at the same layer");
                        }
                    }

                    if (callee.upperLayer > maxCalleeLayerNum)
                    {
                        maxCalleeLayerNum = callee.upperLayer;
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
