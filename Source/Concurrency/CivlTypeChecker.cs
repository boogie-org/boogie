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

        public Dictionary<int, AtomicActionCopy> layerToActionCopy;
        public int asyncFreeLayer;

        public AtomicAction(Procedure proc, Implementation impl, MoverType moverType, LayerRange layerRange)
        {
            this.proc = proc;
            this.impl = impl;
            this.moverType = moverType;
            this.layerRange = layerRange;

            this.layerToActionCopy = new Dictionary<int, AtomicActionCopy>();

            // We usually declare the Boogie procedure and implementation of an atomic action together.
            // Since Boogie only stores the supplied attributes (in particular linearity) in the procedure parameters,
            // we copy them into the implementation parameters here.
            for (int i = 0; i < proc.InParams.Count; i++)
            {
                impl.InParams[i].Attributes = proc.InParams[i].Attributes;
            }
            for (int i = 0; i < proc.OutParams.Count; i++)
            {
                impl.OutParams[i].Attributes = proc.OutParams[i].Attributes;
            }
        }

        // TODO: Check usage!
        public bool IsRightMover { get { return moverType == MoverType.Right || moverType == MoverType.Both; } }
        public bool IsLeftMover { get { return moverType == MoverType.Left || moverType == MoverType.Both; } }
    }

    public class AtomicActionCopy
    {
        public Procedure proc;
        public Implementation impl;

        // Strictly speaking the gate is the same on every layer, but for easier parameter substitution
        // we keep the per-layer version of gates.
        public List<AssertCmd> gate;

        public List<AssertCmd> firstGate;
        public CodeExpr firstAction;
        public List<Variable> firstInParams;
        public List<Variable> firstOutParams;
        public Dictionary<Variable, Expr> firstMap;

        public List<AssertCmd> secondGate;
        public CodeExpr secondAction;
        public List<Variable> secondInParams;
        public List<Variable> secondOutParams;
        public Dictionary<Variable, Expr> secondMap;

        public Dictionary<Variable, Function> triggerFuns;
        public HashSet<Variable> gateUsedGlobalVars;
        public HashSet<Variable> actionUsedGlobalVars;
        public HashSet<Variable> modifiedGlobalVars;

        public AtomicActionCopy(Procedure proc, Implementation impl)
        {
            this.proc = proc;
            this.impl = impl;

            this.triggerFuns = new Dictionary<Variable, Function>();

            // The gate of an atomic action is represented as asserts at the beginning of the procedure body.
            this.gate = impl.Blocks[0].cmds.TakeWhile((c, i) => c is AssertCmd).Cast<AssertCmd>().ToList();
            impl.Blocks[0].cmds.RemoveRange(0, gate.Count);
        }

        public void Setup()
        {
            SetupCopy(ref firstGate, ref firstAction, ref firstInParams, ref firstOutParams, ref firstMap, "first_");
            SetupCopy(ref secondGate, ref secondAction, ref secondInParams, ref secondOutParams, ref secondMap, "second_");

            gateUsedGlobalVars   = new HashSet<Variable>(VariableCollector.Collect(gate).Where(x => x is GlobalVariable));
            actionUsedGlobalVars = new HashSet<Variable>(VariableCollector.Collect(impl).Where(x => x is GlobalVariable));
            modifiedGlobalVars   = new HashSet<Variable>(AssignedVariables().Where(x => x is GlobalVariable));
        }

        private void SetupCopy(ref List<AssertCmd> gateCopy, ref CodeExpr actionCopy, ref List<Variable> inParamsCopy, ref List<Variable> outParamsCopy, ref Dictionary<Variable, Expr> varMap, string prefix)
        {
            gateCopy = new List<AssertCmd>();
            inParamsCopy = new List<Variable>();
            outParamsCopy = new List<Variable>();
            varMap = new Dictionary<Variable, Expr>();

            foreach (Variable x in impl.InParams)
            {
                Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), true, x.Attributes);
                inParamsCopy.Add(xCopy);
                varMap[x] = Expr.Ident(xCopy);
            }
            foreach (Variable x in impl.OutParams)
            {
                Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), false, x.Attributes);
                outParamsCopy.Add(xCopy);
                varMap[x] = Expr.Ident(xCopy);
            }
            List<Variable> localsCopy = new List<Variable>();
            foreach (Variable x in impl.LocVars)
            {
                Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), false);
                varMap[x] = Expr.Ident(xCopy);
                localsCopy.Add(xCopy);
            }
            Contract.Assume(proc.TypeParameters.Count == 0);
            AtomicActionDuplicator aad = new AtomicActionDuplicator(prefix, varMap);
            foreach (AssertCmd assertCmd in gate)
            {
                gateCopy.Add((AssertCmd)aad.Visit(assertCmd));
            }
            actionCopy = new CodeExpr(localsCopy, SubstituteBlocks(impl.Blocks, aad));
        }

        private List<Block> SubstituteBlocks(List<Block> blocks, AtomicActionDuplicator aad)
        {
            Dictionary<Block, Block> blockMap = new Dictionary<Block, Block>();
            List<Block> otherBlocks = new List<Block>();
            foreach (Block block in blocks)
            {
                List<Cmd> otherCmds = new List<Cmd>();
                foreach (Cmd cmd in block.Cmds)
                {
                    otherCmds.Add((Cmd)aad.Visit(cmd));
                }
                Block otherBlock = new Block();
                otherBlock.tok = block.tok;
                otherBlock.Cmds = otherCmds;
                otherBlock.Label = aad.prefix + block.Label;
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

        private List<Variable> AssignedVariables()
        {
            List<Variable> modifiedVars = new List<Variable>();
            foreach (Cmd cmd in impl.Blocks.SelectMany(b => b.Cmds))
            {
                cmd.AddAssignedVariables(modifiedVars);
            }
            return modifiedVars;
        }

        public bool HasAssumeCmd { get { return impl.Blocks.Any(b => b.Cmds.Any(c => c is AssumeCmd)); } }

        public bool TriviallyCommutesWith(AtomicActionCopy other)
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
    }

    /// <summary>
    /// Renames variables (first_ and second_ prefix) in atomic action copies.
    /// We do not use standard substitution, because we also need to rename bound variables
    /// (because of potential substitution in commutativity checkers).
    /// A substitution for regular variables is supplied from the outside, replacements for
    /// bound variables are created on the fly.
    /// </summary>
    class AtomicActionDuplicator : Duplicator
    {
        public string prefix;
        public Dictionary<Variable,Expr> subst;
        private Dictionary<Variable,Expr> bound;

        public AtomicActionDuplicator(string prefix, Dictionary<Variable,Expr> subst) {
            this.prefix = prefix;
            this.subst = subst;
            this.bound = new Dictionary<Variable, Expr>();
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (subst.ContainsKey(node.Decl))
            {
                return subst[node.Decl];
            }
            else if (bound.ContainsKey(node.Decl))
            {
                return bound[node.Decl];
            }
            return base.VisitIdentifierExpr(node);
        }

        public override BinderExpr VisitBinderExpr(BinderExpr node)
        {
            var oldToNew = node.Dummies.ToDictionary(x => x, x => new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), x.Attributes));

            foreach (var x in node.Dummies)
            {
                bound.Add(x, Expr.Ident(oldToNew[x]));
            }

            BinderExpr expr = base.VisitBinderExpr(node);
            expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();

            // We process triggers of quantifer expressions here, because otherwise the
            // substitutions for bound variables have to be leaked outside this procedure.
            if (node is QuantifierExpr quantifierExpr)
            {
                if (quantifierExpr.Triggers != null)
                {
                    ((QuantifierExpr)expr).Triggers = this.VisitTrigger(quantifierExpr.Triggers);
                }
            }

            foreach (var x in node.Dummies)
            {
                bound.Remove(x);
            }

            return expr;
        }

        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            // Don't remove this implementation! Triggers should be duplicated in VisitBinderExpr.
            return (QuantifierExpr)this.VisitBinderExpr(node);
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
        public Procedure addPendingAsyncProc;

        public ActionProc(Procedure proc, AtomicAction refinedAction, int upperLayer)
            : base(proc, refinedAction.moverType, upperLayer)
        {
            this.refinedAction = refinedAction;
        }
    }

    public class IntroductionProc
    {
        public Procedure proc;
        public LayerRange layerRange;
        public bool isLeaky;

        public IntroductionProc(Procedure proc, LayerRange layerRange, bool isLeaking)
        {
            this.proc = proc;
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
        // TypeCheckLocalVariables initializes globalVarToLayerRange such that variables with min-max layer range are not explicitly stored.
        // Similarly for localVarToIntroLayer / TypeCheckLocalVariables.
        // Use public access methods.
        private Dictionary<Variable, LayerRange> globalVarToLayerRange;
        private Dictionary<Variable, int> localVarToIntroLayer;

        public Dictionary<Procedure, AtomicAction> procToAtomicAction;
        public Dictionary<Procedure, YieldingProc> procToYieldingProc;
        public Dictionary<Procedure, IntroductionProc> procToIntroductionProc;

        public Dictionary<Absy, HashSet<int>> absyToLayerNums;
        Dictionary<CallCmd, int> introductionCallToLayer;

        public GlobalVariable pendingAsyncMultiset;

        // This collections are for convenience in later phases and are only initialized at the end of type checking.
        public List<int> allRefinementLayers;
        public List<int> allAtomicActionLayers;
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
            this.procToIntroductionProc = new Dictionary<Procedure, IntroductionProc>();
            this.introductionCallToLayer = new Dictionary<CallCmd, int>();
        }

        public bool CallExists(CallCmd callCmd, int enclosingProcLayerNum, int layerNum)
        {
            Debug.Assert(procToIntroductionProc.ContainsKey(callCmd.Proc));
            var introductionProc = procToIntroductionProc[callCmd.Proc];
            if (introductionProc.isLeaky)
            {
                return enclosingProcLayerNum == layerNum;
            }
            else
            {
                return introductionCallToLayer[callCmd] <= layerNum;
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
                    if (o is LiteralExpr l && l.isBigNum)
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
                            checkingContext.Warning(kv, "Ignoring duplicate mover type declaration ({0}).", kv.Key);
                        else
                            moverType = x;
                    }
                }
            }

            return moverType;
        }

        public void TypeCheck()
        {
            // TODO: eliminate early returns
            // Can we make later phases resilient to errors in previous phases,
            // such that as much feedback as possible is generated for the user?
            // For example, by creating "invalid" objects like an ActionProc with
            // null refinedAction in TypeCheckYieldingProcedureDecls, such that
            // later checks can work with them but also do not cash.

            TypeCheckGlobalVariables();
            TypeCheckIntroductionProcedures();

            TypeCheckAtomicActionDecls();
            TypeCheckYieldingProcedureDecls();

            TypeCheckLocalVariables();

            TypeCheckAtomicActionImpls();

            if (checkingContext.ErrorCount != 0)
                return;

            ComputeAsyncFreeLayers();

            // List of all layers where refinement happens
            allRefinementLayers = procToYieldingProc.Values.Select(a => a.upperLayer).OrderBy(l => l).Distinct().ToList();

            // List of all layers where the set of available atomic actions changes (through availability or refinement)
            allAtomicActionLayers = allRefinementLayers.ToList();
            allAtomicActionLayers.AddRange(procToAtomicAction.Values.Select(a => a.layerRange.lowerLayerNum));
            allAtomicActionLayers.AddRange(procToAtomicAction.Values.Select(a => a.layerRange.upperLayerNum));
            allAtomicActionLayers = allAtomicActionLayers.Distinct().OrderBy(l => l).ToList();

            foreach (var kv in absyToLayerNums)
            {
                foreach (var layer in kv.Value)
                {
                    if (!allRefinementLayers.Contains(layer))
                    {
                        checkingContext.Error(kv.Key, "No refinement on layer {0}", layer);
                    }
                }
            }

            CheckAtomicActionAcyclicity();

            if (checkingContext.ErrorCount != 0)
                return;

            AddPendingAsyncMachinery();
            GenerateAtomicActionCopies();
            TypeCheckYieldingProcedureImpls();

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

        private void TypeCheckAtomicActionDecls()
        {
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

                bool inGate = true;
                foreach (var cmd in impl.Blocks[0].cmds)
                {
                    if (inGate && !(cmd is AssertCmd))
                    {
                        inGate = false;
                    }
                    else if (!inGate && cmd is AssertCmd)
                    {
                        Error(cmd, "Assert is only allowed in the gate of an atomic action");
                    }
                }
                foreach (var cmd in impl.Blocks.Skip(1).SelectMany(b => b.cmds).OfType<AssertCmd>())
                {
                    Error(cmd, "Assert is only allowed in the gate of an atomic action");
                }

                procToAtomicAction[proc] = new AtomicAction(proc, impl, moverType.Value, layerRange);
            }
        }

        private void TypeCheckAtomicActionImpls()
        {
            AtomicActionVisitor atomicActionVisitor = new AtomicActionVisitor(this);
            foreach (var action in procToAtomicAction.Values)
            {
                atomicActionVisitor.VisitAction(action);
            }
        }

        private void TypeCheckIntroductionProcedures()
        {
            // Introduction procedure:
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
                        Error(ie, "Introduction procedures can modify shared variables only on their introduction layer");
                    }
                }

                procToIntroductionProc[proc] = new IntroductionProc(proc, layerRange, isLeaky);
            }
            if (checkingContext.ErrorCount > 0) return;

            IntroductionProcedureVisitor visitor = new IntroductionProcedureVisitor(this);
            foreach (Implementation impl in program.Implementations.Where(impl => procToIntroductionProc.ContainsKey(impl.Proc)))
            {
                visitor.VisitImplementation(impl);
            }
        }

        private void TypeCheckYieldingProcedureDecls()
        {
            YieldingProcVisitor visitor = new YieldingProcVisitor(this);

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
                    if (!refinedAction.layerRange.Contains(upperLayer + 1))
                    {
                        // Strictly speaking, there could be a layer gap if some layer is not used
                        // for refinement. However, at this point we do not know the refinement layers,
                        // so we use this conservative check which seems reasonable in practice.
                        checkingContext.Error(proc, "Refined atomic action must be available at layer {0}", upperLayer + 1);
                    }

                    CheckSignatures(proc, refinedAction.proc);

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

                visitor.VisitProcedure(proc);
            }
        }

        private void TypeCheckYieldingProcedureImpls()
        {
            YieldingProcVisitor visitor = new YieldingProcVisitor(this);

            foreach (var impl in program.Implementations.Where(impl => procToYieldingProc.ContainsKey(impl.Proc)))
            {
                visitor.VisitImplementation(impl);

                // TODO: Check the modifies clause of mover procedures.
                // Calls to introduction procedures!

                YieldingProc yieldingProc = procToYieldingProc[impl.Proc];

                if (yieldingProc is MoverProc)
                {
                    var declaredModifiedVars = ((MoverProc)yieldingProc).modifiedGlobalVars;
                    HashSet<Variable> mods = null;
                    foreach (var callCmd in impl.Blocks.SelectMany(b => b.Cmds).OfType<CallCmd>())
                    {
                        if (procToYieldingProc.ContainsKey(callCmd.Proc))
                        {
                            var calledProc = procToYieldingProc[callCmd.Proc];
                            if (calledProc is ActionProc)
                            {
                                mods = ((ActionProc)calledProc).refinedAction.layerToActionCopy[yieldingProc.upperLayer].modifiedGlobalVars;
                            }
                            else if (calledProc is MoverProc)
                            {
                                mods = ((MoverProc)calledProc).modifiedGlobalVars;
                            }
                            else
                            {
                                Debug.Assert(calledProc is SkipProc);
                                mods = new HashSet<Variable>();
                            }
                        }
                        else if (procToIntroductionProc.ContainsKey(callCmd.Proc))
                        {
                            mods = new HashSet<Variable>(callCmd.Proc.Modifies.Select(ie => ie.Decl));
                        }
                        else
                        {
                            Debug.Assert(false);
                        }

                        foreach (var mod in mods)
                        {
                            if (!declaredModifiedVars.Contains(mod))
                            {
                                checkingContext.Error(callCmd, "Modified variable {0} does not appear in modifies clause of mover procedure.", mod.Name);
                            }
                        }
                    }
                }
            }
        }

        // Check that an action procedure has the same interface as the refined atomic action.
        // CheckSignatures and MatchFormals are adapted from type checking implementations in Absy.cs,
        // i.e., that implementations have the same interface as the corresponding procedure.
        private void CheckSignatures(Procedure proc, Procedure action)
        {
            if (proc.TypeParameters.Count != action.TypeParameters.Count)
            {
                checkingContext.Error(proc, "mismatched number of type parameters in refinement procedure: {0}", proc.Name);
            }
            else
            {
                // if the numbers of type parameters are different, it is
                // difficult to compare the argument types
                MatchFormals(proc, action, proc.InParams, action.InParams, "in");
                MatchFormals(proc, action, proc.OutParams, action.OutParams, "out");
            }
        }

        void MatchFormals(Procedure proc, Procedure action, List<Variable> procFormals, List<Variable> actionFormals, string inout)
        {
            if (procFormals.Count != actionFormals.Count)
            {
                checkingContext.Error(proc, "mismatched number of {0}-parameters in refinement procedure: {1}", inout, proc.Name);
            }
            else
            {
                // unify the type parameters so that types can be compared
                IDictionary<TypeVariable, Type> subst1 = new Dictionary<TypeVariable, Type>();
                IDictionary<TypeVariable, Type> subst2 = new Dictionary<TypeVariable, Type>();

                for (int i = 0; i < proc.TypeParameters.Count; ++i)
                {
                    TypeVariable newVar = new TypeVariable(Token.NoToken, action.TypeParameters[i].Name);
                    subst1.Add(action.TypeParameters[i], newVar);
                    subst2.Add(proc.TypeParameters[i], newVar);
                }

                for (int i = 0; i < procFormals.Count; i++)
                {
                    // For error messages below
                    string procName = procFormals[i].Name;
                    string actionName = actionFormals[i].Name;
                    string msg;
                    if (procName == actionName)
                    {
                        msg = procName;
                    }
                    else
                    {
                        msg = String.Format("{0} (named {1} in atomic action)", procName, actionName);
                    }

                    // the names of the formals are allowed to change from the proc to the impl
                    // but types must be identical
                    Type t = procFormals[i].TypedIdent.Type.Substitute(subst2);
                    Type u = actionFormals[i].TypedIdent.Type.Substitute(subst1);
                    if (!t.Equals(u))
                    {
                        
                        checkingContext.Error(proc, "mismatched type of {0}-parameter in refinement procedure {1}: {2}", inout, proc.Name, msg);
                    }

                    if (QKeyValue.FindStringAttribute(procFormals[i].Attributes, CivlAttributes.LINEAR) != QKeyValue.FindStringAttribute(actionFormals[i].Attributes, CivlAttributes.LINEAR) ||
                        QKeyValue.FindStringAttribute(procFormals[i].Attributes, CivlAttributes.LINEAR_IN) != QKeyValue.FindStringAttribute(actionFormals[i].Attributes, CivlAttributes.LINEAR_IN) ||
                        QKeyValue.FindStringAttribute(procFormals[i].Attributes, CivlAttributes.LINEAR_OUT) != QKeyValue.FindStringAttribute(actionFormals[i].Attributes, CivlAttributes.LINEAR_OUT))
                    {
                        checkingContext.Error(proc, "mismatched linearity type of {0}-parameter in refinement procedure {1}: {2}", inout, proc.Name, msg);
                    }
                }
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

        public int AllInParamsIntroducedLayer(Procedure proc)
        {
            return proc.InParams.Select(inParam => LocalVariableIntroLayer(inParam)).DefaultIfEmpty(int.MinValue).Max();
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

        /// <summary>
        /// Fixpoint computation to determine for each atomic action the least layer at which it becomes async free.
        /// </summary>
        private void ComputeAsyncFreeLayers()
        {
            foreach (var a in procToAtomicAction.Values)
            {
                a.asyncFreeLayer = a.layerRange.lowerLayerNum;
            }

            bool proceed = true;
            while (proceed)
            {
                proceed = false;
                foreach (var a in procToAtomicAction.Values)
                {
                    foreach (var call in a.impl.Blocks.SelectMany(b => b.cmds.OfType<CallCmd>()))
                    {
                        var target = procToYieldingProc[call.Proc];
                        int x = target.upperLayer + 1;
                        if (target is ActionProc actionProc)
                        {
                            x = Math.Max(x, actionProc.refinedAction.asyncFreeLayer);
                        }
                        if (x > a.asyncFreeLayer)
                        {
                            a.asyncFreeLayer = x;
                            proceed = true;
                        }
                    }
                }
            }
        }

        // TODO: Is it necessary to construct a graph for every layer independently?
        /// <summary>
        /// Check (for each layer individually), if atomic actions have a cyclic dependency through pending asyncs.
        /// </summary>
        private void CheckAtomicActionAcyclicity()
        {
            foreach (var layer in allAtomicActionLayers)
            {
                Graph<AtomicAction> graph = new Graph<AtomicAction>();

                foreach (var action in procToAtomicAction.Values.Where(a => a.layerRange.Contains(layer)))
                {
                    foreach (var callCmd in action.impl.Blocks.SelectMany(b => b.Cmds).OfType<CallCmd>())
                    {
                        Debug.Assert(callCmd.IsAsync);

                        if (procToYieldingProc[callCmd.Proc] is ActionProc calleeProc && layer > calleeProc.upperLayer)
                        {
                            graph.AddEdge(action, calleeProc.refinedAction);
                        }
                    }
                }

                if (!Graph<AtomicAction>.Acyclic(graph, null))
                    checkingContext.Error(Token.NoToken, "Atomic actions have cyclic dependency at layer " + layer);
            }
        }

        private void AddPendingAsyncMachinery()
        {
            CtorType pendingAsyncType = null;

            // We do not want to disturb non-CIVL programs
            if (procToAtomicAction.Count != 0)
            {
                // datatype
                pendingAsyncType = new CtorType(Token.NoToken, new TypeCtorDecl(Token.NoToken, "PendingAsync", 0, new QKeyValue(Token.NoToken, "datatype", new List<object>(), null)), new List<Type>());
                program.AddTopLevelDeclaration(pendingAsyncType.Decl);

                // global multiset variable
                MapType pendingAsyncMultisetType = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type>{ pendingAsyncType }, Type.Int);
                this.pendingAsyncMultiset = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "pendingAsyncMultiset", pendingAsyncMultisetType));
                program.AddTopLevelDeclaration(pendingAsyncMultiset);
            }

            foreach (var actionProc in procToYieldingProc.Values.OfType<ActionProc>())
            {
                Debug.Assert(pendingAsyncType != null);

                // constructor function
                Function f = new Function(
                                 Token.NoToken,
                                 "PendingAsync_" + actionProc.proc.Name,
                                 new List<TypeVariable>(),
                                 actionProc.proc.InParams.Select(v => new Formal(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type), true)).ToList<Variable>(),
                                 new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "x", pendingAsyncType), false),
                                 null,
                                 new QKeyValue(Token.NoToken, "constructor", new List<object>(), null)
                             );
                DatatypeConstructor c = new DatatypeConstructor(f);
                program.AddTopLevelDeclaration(c);

                // pending async adder procedure & implementation
                string name = "AddPendingAsync_" + actionProc.proc.Name;
                Procedure p = new Procedure(
                                  Token.NoToken,
                                  name,
                                  new List<TypeVariable>(),
                                  actionProc.proc.InParams.Select(v => (Variable)v.Clone()).ToList(),
                                  new List<Variable>(),
                                  new List<Requires>(),
                                  new List<IdentifierExpr> { Expr.Ident(pendingAsyncMultiset) },
                                  new List<Ensures>()
                              );
                p.InParams.ForEach(inParam => inParam.Attributes = null);
                CivlUtil.AddInlineAttribute(p);
                p.Typecheck(new TypecheckingContext(null));
                actionProc.addPendingAsyncProc = p;
                program.AddTopLevelDeclaration(p);

                var inParams = actionProc.proc.InParams.Select(v => (Variable)v.Clone()).ToList();
                inParams.ForEach(inParam => inParam.Attributes = null);
                Expr idx = new NAryExpr(
                               Token.NoToken,
                               new FunctionCall(c),
                               inParams.Select(v => Expr.Ident(v)).ToList<Expr>());
                
                MapAssignLhs lhs = new MapAssignLhs(Token.NoToken, new SimpleAssignLhs(Token.NoToken, Expr.Ident(pendingAsyncMultiset)), new List<Expr> { idx });
                Expr sel = Expr.Select(Expr.Ident(pendingAsyncMultiset), new List<Expr>{ idx });
                Expr plusOne = Expr.Add(sel, new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                AssignCmd cmd = new AssignCmd(Token.NoToken, new List<AssignLhs>{ lhs }, new List<Expr> { plusOne });

                Implementation i = new Implementation(
                                       Token.NoToken,
                                       name,
                                       new List<TypeVariable>(),
                                       inParams,
                                       new List<Variable>(),
                                       new List<Variable>(),
                                       new List<Block> { new Block(Token.NoToken, "L", new List<Cmd> { cmd }, new ReturnCmd(Token.NoToken)) });
                i.Proc = p;
                i.OriginalBlocks = i.Blocks;
                i.OriginalLocVars = i.LocVars;
                CivlUtil.AddInlineAttribute(i);
                i.Typecheck(new TypecheckingContext(null));
                program.AddTopLevelDeclaration(i);
            }
        }

        private void GenerateAtomicActionCopies()
        {
            foreach (var layer in allAtomicActionLayers)
            {
                // Generate layer specific versions of atomic actions (i.e., resolve pending async calls)
                AtomicActionCopier copier = new AtomicActionCopier(layer, this);
                copier.GenerateCopies();

                // AtomicActionCopy constructur removes gate from atomic action implementation
                foreach (var action in copier.actions)
                {
                    action.layerToActionCopy[layer] = new AtomicActionCopy(copier.procMap[action.proc], copier.implMap[action.impl]);
                }

                program.AddTopLevelDeclarations(copier.procMap.Values);
                program.AddTopLevelDeclarations(copier.implMap.Values);

                // Fully inline atomic action implementations
                foreach (var impl in copier.implMap.Values)
                {
                    impl.OriginalBlocks = impl.Blocks;
                    impl.OriginalLocVars = impl.LocVars;
                }
                foreach (var impl in copier.implMap.Values)
                {
                    Inliner.ProcessImplementation(program, impl);

                    // Havoc commands are not allowed in atomic actions. However, the
                    // inliner above introduces havocs for uninitialized local variables
                    // in case an inlined procedure is called in a loop. Since loops are
                    // also not allowed in atomic actions, we can remove the havocs here.
                    impl.Blocks.ForEach(b => b.Cmds.RemoveAll(c => c is HavocCmd));
                }
                foreach (var impl in copier.implMap.Values)
                {
                    impl.OriginalBlocks = null;
                    impl.OriginalLocVars = null;
                }

                // Generate first/second versions of atomic actions (used in transition relation computation)
                // and initialize used/modified variable infos.
                foreach (var action in copier.actions)
                {
                    action.layerToActionCopy[layer].Setup();
                }
            }
        }

        public class AtomicActionCopier : Duplicator
        {
            private int layer;
            private CivlTypeChecker ctc;

            public List<AtomicAction> actions;
            public Dictionary<Procedure,Procedure> procMap;
            public Dictionary<Implementation, Implementation> implMap;

            public AtomicActionCopier(int layer, CivlTypeChecker ctc)
            {
                this.layer = layer;
                this.ctc = ctc;
                this.actions = ctc.procToAtomicAction.Values.Where(a => a.layerRange.Contains(layer)).ToList();
                this.procMap = new Dictionary<Procedure, Procedure>();
                this.implMap = new Dictionary<Implementation, Implementation>();
            }

            public void GenerateCopies()
            {
                foreach (var action in actions)
                {
                    VisitProcedure(action.proc);
                }
                foreach (var action in actions)
                {
                    VisitImplementation(action.impl);
                }
            }

            public override Procedure VisitProcedure(Procedure node)
            {
                if (procMap.ContainsKey(node))
                    return procMap[node];
                
                Procedure proc = base.VisitProcedure(node);
                proc.Name = string.Format("{0}_{1}", node.Name, layer);
                procMap[node] = proc;
                CivlUtil.AddInlineAttribute(proc);
                return proc;
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                if (implMap.ContainsKey(node))
                    return implMap[node];
                
                Procedure proc = procMap[node.Proc];
                Implementation impl = base.VisitImplementation(node);
                impl.Proc = proc;
                impl.Name = proc.Name;
                implMap[node] = impl;
                CivlUtil.AddInlineAttribute(impl);
                return impl;
            }

            public override Cmd VisitCallCmd(CallCmd node)
            {
                CallCmd call = (CallCmd)base.VisitCallCmd(node);
                call.IsAsync = false;
                Debug.Assert(ctc.procToYieldingProc[node.Proc] is ActionProc);
                ActionProc target = (ActionProc)ctc.procToYieldingProc[node.Proc];
                if (target.upperLayer >= layer)
                    call.Proc = target.addPendingAsyncProc;
                else
                    call.Proc = procMap[target.refinedAction.proc];
                call.callee = call.Proc.Name;
                return call;
            }
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
                        ctc.checkingContext.Error(node, "Shared variable {0} is not available in atomic action specification", node.Decl.Name);
                    }
                }
                return base.VisitIdentifierExpr(node);
            }

            public override Cmd VisitHavocCmd(HavocCmd node)
            {
                // Note: Inlining in GenerateAtomicActionCopies generates havocs that are
                // manually removed again (see explanation there). If havocs were to be
                // allowed in atomic actions in the future, this has to be addressed.
                ctc.Error(node, "Havoc command not allowed inside an atomic action");
                return base.VisitHavocCmd(node);
            }

            public override Cmd VisitCallCmd(CallCmd node)
            {
                if (node.IsAsync)
                {
                    if (atomicAction.moverType != MoverType.Atomic && atomicAction.moverType != MoverType.Left)
                    {
                        ctc.Error(node, "Atomic action with pending async must have mover type atomic or left");
                    }
                    if (!ctc.procToYieldingProc.ContainsKey(node.Proc) || !(ctc.procToYieldingProc[node.Proc] is ActionProc))
                    {
                        ctc.Error(node, "Target of a pending async must be an action procedure");
                    }
                    else
                    {
                        ActionProc target = (ActionProc)ctc.procToYieldingProc[node.Proc];
                        if (!target.IsLeftMover)
                        {
                            ctc.Error(node, "Target of async call must be a left mover");
                        }
                        if (target.refinedAction.layerRange.upperLayerNum < atomicAction.layerRange.upperLayerNum)
                        {
                            ctc.Error(node, "Callee disappears before caller");
                        }
                        if (ctc.AllInParamsIntroducedLayer(target.proc) > atomicAction.layerRange.lowerLayerNum)
                        {
                            ctc.Error(node, "Target of a pending async must have all input variables introduced");
                        }
                    }
                }
                else
                {
                    ctc.Error(node, "Call command not allowed inside an atomic action");
                }
                return base.VisitCallCmd(node);
            }

            public override Expr VisitOldExpr(OldExpr node)
            {
                ctc.Error(node, "Old expression not allowed inside an atomic action");
                return base.VisitOldExpr(node);
            }
        }

        private class IntroductionProcedureVisitor : ReadOnlyVisitor
        {
            private CivlTypeChecker ctc;
            private IntroductionProc introductionProc;

            public IntroductionProcedureVisitor(CivlTypeChecker civlTypeChecker)
            {
                this.ctc = civlTypeChecker;
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                introductionProc = ctc.procToIntroductionProc[node.Proc];
                return base.VisitImplementation(node);
            }

            public override Cmd VisitCallCmd(CallCmd callCmd)
            {
                if (!ctc.procToIntroductionProc.ContainsKey(callCmd.Proc))
                {
                    ctc.Error(callCmd, "Introduction procedure can only call an introduction procedure");
                    return base.VisitCallCmd(callCmd);
                }
                IntroductionProc calleeProc = ctc.procToIntroductionProc[callCmd.Proc];
                if (!introductionProc.layerRange.Subset(calleeProc.layerRange))
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
                    if (!introductionProc.layerRange.Subset(globalVarLayerRange))
                    {
                        ctc.Error(node, "Shared variable is not accessible in introduction procedure");
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

            Procedure enclosingProc;
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
                enclosingProc = node;
                yieldingProc = ctc.procToYieldingProc[node];
                var ret = base.VisitProcedure(node);
                enclosingProc = null;
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
                    else if (enclosingProc != null)
                    {
                        // Modifies clauses of mover procedures need access to global variables.
                    }
                    else
                    {
                        ctc.Error(node, "Shared variable can be accessed only in introduction procedures, atomic actions, and specifications");
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
                        ctc.checkingContext.Error(node, "Specification layer {0} is greater than enclosing procedure layer {1}", layer, yieldingProc.upperLayer);
                    }
                    foreach (var ie in sharedVariableAccesses)
                    {
                        if (!ctc.GlobalVariableLayerRange(ie.Decl).Contains(layer))
                        {
                            ctc.checkingContext.Error(ie, "Global variable {0} is not available at layer {1}", ie.Name, layer);
                        }
                    }
                    foreach (var ie in localVariableAccesses)
                    {
                        if (layer < ctc.LocalVariableIntroLayer(ie.Decl))
                        {
                            ctc.checkingContext.Error(ie, "Local variable {0} is not available at layer {1}", ie.Name, layer);
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
                else if (ctc.procToIntroductionProc.ContainsKey(call.Proc))
                {
                    VisitIntroductionProcCallCmd(call, callerProc, ctc.procToIntroductionProc[call.Proc]);
                }
                else
                {
                    ctc.Error(call, "A yielding procedure can only call yielding or introduction procedures");
                }
                return call;
            }

            private void VisitYieldingProcCallCmd(CallCmd call, YieldingProc callerProc, YieldingProc calleeProc)
            {
                // Skip and mover procedures have to be async-free at their upper layer
                if (callerProc is SkipProc || callerProc is MoverProc)
                {
                    if (call.IsAsync && calleeProc.upperLayer > callerProc.upperLayer)
                    {
                        ctc.Error(call, "Disappearing layer of caller cannot be lower than that of callee");
                    }
                    else
                    {
                        if (calleeProc is ActionProc actionProc && actionProc.refinedAction.asyncFreeLayer > callerProc.upperLayer)
                        {
                            ctc.Error(call, "Disappearing layer of caller cannot be lower than async-free layer of callee");
                        }
                    }
                }

                if (calleeProc is ActionProc)
                {
                    if (callerProc.upperLayer == calleeProc.upperLayer)
                    {
                        ctc.Error(call, "The layer of the caller must be greater than the layer of the callee");
                    }
                    else if (callerProc.upperLayer < calleeProc.upperLayer)
                    {
                        if (!call.IsAsync)
                        {
                            ctc.Error(call, "The layer of the caller must be greater than the layer of the callee");
                        }
                        else if (ctc.AllInParamsIntroducedLayer(calleeProc.proc) > callerProc.upperLayer)
                        {
                            ctc.Error(call, "Target of a pending async must have all input variables introduced");
                        }
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
                        // Skip procedures have the effect of havocing their output variables.
                        // Currently, the snapshotting during refinement checking does not account for that,
                        // so we forbid propagation to the callers output variables.
                        HashSet<Variable> callerOutParams = new HashSet<Variable>(enclosingImpl.OutParams);
                        foreach (var x in call.Outs)
                        {
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
                            ctc.checkingContext.Error(ie, "Variable {0} introduced on layer {1} can not be passed to formal parameter introduced on layer {2}", ie.Decl.Name, actualIntroLayer, formalIntroLayer);
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

            private void VisitIntroductionProcCallCmd(CallCmd call, YieldingProc callerProc, IntroductionProc calleeProc)
            {
                if (!calleeProc.layerRange.Contains(callerProc.upperLayer))
                {
                    ctc.checkingContext.Error(call, "Called introduction procedure {0} is not available at layer {1}", calleeProc.proc.Name, callerProc.upperLayer);
                    return;
                }

                if (calleeProc.isLeaky)
                {
                    // Call to leaky introduction procedure only exists at the upper layer of caller yielding procedure.
                    // Thus, all local variables are already introduced and we only have to check output variables.
                    foreach (var ie in call.Outs)
                    {
                        if (ctc.LocalVariableIntroLayer(ie.Decl) != callerProc.upperLayer)
                        {
                            ctc.checkingContext.Error(ie, "Output variable {0} must be introduced at layer {1}", ie.Decl.Name, callerProc.upperLayer);
                        }
                    }
                }
                else
                {
                    // Call to non-leaky introduction procedure exists as soon as all local variables used as input are available.
                    // I.e., we compute the maximum introduction layer of all local variables used as input.
                    localVariableAccesses = new List<IdentifierExpr>();
                    foreach (var e in call.Ins) { Visit(e); }
                    ctc.introductionCallToLayer[call] = localVariableAccesses
                                                           .Select(ie => ctc.LocalVariableIntroLayer(ie.Decl))
                                                           .Concat1(calleeProc.layerRange.lowerLayerNum)
                                                           .Max(); 
                    localVariableAccesses = null;
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
                CivlAttributes.RemoveRefinesAttribute(node);
                return base.VisitProcedure(node);
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                CivlAttributes.RemoveYieldsAttribute(node);
                CivlAttributes.RemoveMoverAttribute(node);
                CivlAttributes.RemoveLayerAttribute(node);
                CivlAttributes.RemoveRefinesAttribute(node);
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
