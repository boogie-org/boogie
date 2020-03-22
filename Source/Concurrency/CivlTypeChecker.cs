using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
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
        public Dictionary<Procedure, AtomicAction> procToIsInvariant;
        public Dictionary<Procedure, AtomicAction> procToIsAbstraction;
        public Dictionary<Procedure, YieldingProc> procToYieldingProc;
        public Dictionary<Procedure, IntroductionProc> procToIntroductionProc;
        public CommutativityHints commutativityHints;

        public List<InductiveSequentialization> inductiveSequentializations;

        public Dictionary<Absy, HashSet<int>> absyToLayerNums;

        public CtorType pendingAsyncType;
        public MapType pendingAsyncMultisetType;
        public Function pendingAsyncAdd;
        public Dictionary<Implementation, Variable> implToPendingAsyncCollector;

        // This collections are for convenience in later phases and are only initialized at the end of type checking.
        public List<int> allRefinementLayers;
        public List<GlobalVariable> sharedVariables;
        public List<IdentifierExpr> sharedVariableIdentifiers;

        public LinearTypeChecker linearTypeChecker;
        
        public CivlTypeChecker(Program program)
        {
            this.checkingContext = new CheckingContext(null);
            this.program = program;

            this.globalVarToLayerRange = new Dictionary<Variable, LayerRange>();
            this.localVarToIntroLayer = new Dictionary<Variable, int>();
            this.absyToLayerNums = new Dictionary<Absy, HashSet<int>>();
            this.procToAtomicAction = new Dictionary<Procedure, AtomicAction>();
            this.procToIsInvariant = new Dictionary<Procedure, AtomicAction>();
            this.procToIsAbstraction = new Dictionary<Procedure, AtomicAction>();
            this.procToYieldingProc = new Dictionary<Procedure, YieldingProc>();
            this.procToIntroductionProc = new Dictionary<Procedure, IntroductionProc>();
            this.implToPendingAsyncCollector = new Dictionary<Implementation, Variable>();
            this.inductiveSequentializations = new List<InductiveSequentialization>();
        }

        public void TypeCheck()
        {
            // TODO: eliminate early returns
            // Can we make later phases resilient to errors in previous phases,
            // such that as much feedback as possible is generated for the user?
            // For example, by creating "invalid" objects like an ActionProc with
            // null refinedAction in TypeCheckYieldingProcedureDecls, such that
            // later checks can work with them but also do not crash.

            TypeCheckGlobalVariables();
            TypeCheckIntroductionProcedures();

            TypeCheckAtomicActionDecls();
            TypeCheckPendingAsyncMachinery();

            if (checkingContext.ErrorCount > 0)
                return;

            TypeCheckInductiveSequentializations();
            TypeCheckYieldingProcedureDecls();

            TypeCheckLocalVariables();

            if (checkingContext.ErrorCount > 0)
                return;

            TypeCheckAtomicActionImpls();
            TypeCheckYieldingProcedureImpls();

            TypeCheckRefinementLayers();

            TypeCheckCommutativityHints();

            AttributeEraser.Erase(this);

            if (checkingContext.ErrorCount > 0)
                return;

            var yieldTypeChecker = new YieldTypeChecker(this);
            yieldTypeChecker.TypeCheck();
            if (checkingContext.ErrorCount > 0)
            {
                return;
            }

            linearTypeChecker = new LinearTypeChecker(this);
            linearTypeChecker.TypeCheck();
        }

        private void TypeCheckRefinementLayers()
        {
            // List of all layers where refinement happens
            allRefinementLayers = procToYieldingProc.Values.Select(a => a.upperLayer).OrderBy(l => l).Distinct().ToList();

            foreach (var kv in absyToLayerNums)
            {
                foreach (var layer in kv.Value)
                {
                    if (!allRefinementLayers.Contains(layer))
                    {
                        Error(kv.Key, $"No refinement at layer {layer}");
                    }
                }
            }

            var allInductiveSequentializationLayers = inductiveSequentializations.Select(x => x.inputAction.layerRange.upperLayerNum).ToList();

            var intersect = allRefinementLayers.Intersect(allInductiveSequentializationLayers).ToList();
            if (intersect.Any())
                checkingContext.Error(Token.NoToken, "The following layers mix refinement with IS: " + string.Join(",", intersect));

            foreach(var g in sharedVariables)
            {
                var layerRange = GlobalVariableLayerRange(g);
                if (allInductiveSequentializationLayers.Contains(layerRange.lowerLayerNum))
                    Error(g, $"Shared variable {g.Name} cannot be introduced at layer with IS");
                if (allInductiveSequentializationLayers.Contains(layerRange.upperLayerNum))
                    Error(g, $"Shared variable {g.Name} cannot be hidden at layer with IS");
            }

        }

        private void TypeCheckCommutativityHints()
        {
            CommutativityHintVisitor visitor = new CommutativityHintVisitor(this);
            visitor.VisitFunctions();
            this.commutativityHints = visitor.commutativityHints;
        }

        private void TypeCheckGlobalVariables()
        {
            foreach (var g in program.GlobalVariables)
            {
                var layerRange = ToLayerRange(FindLayers(g.Attributes), g);
                if (layerRange != LayerRange.MinMax)
                    globalVarToLayerRange[g] = layerRange;
            }
            sharedVariables = program.GlobalVariables.ToList();
            sharedVariableIdentifiers = sharedVariables.Select(v => Expr.Ident(v)).ToList();
        }

        private void TypeCheckAtomicActionDecls()
        {
            // Atomic action:
            // * no {:yield}
            // * mover type
            // * layer range
            foreach (var proc in program.Procedures.Where(IsAtomicAction))
            {
                MoverType moverType = GetActionMoverType(proc);
                LayerRange layerRange = ToLayerRange(FindLayers(proc.Attributes), proc);

                if (proc.Requires.Count + proc.Ensures.Count > 0)
                {
                    Error(proc, "Atomic action cannot have preconditions or postconditions");
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
                    Error(proc, "Atomic action specification cannot have loops");
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

                var action = new AtomicAction(proc, impl, moverType, layerRange);
                if (proc.HasAttribute(CivlAttributes.IS_INVARIANT))
                    procToIsInvariant[proc] = action;
                else if (proc.HasAttribute(CivlAttributes.IS_ABSTRACTION))
                    procToIsAbstraction[proc] = action;
                else
                    procToAtomicAction[proc] = action;
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

        private void TypeCheckInductiveSequentializations()
        {
            foreach (var action in procToAtomicAction.Values)
            {
                var layer = action.layerRange.upperLayerNum;
                AtomicAction invariantAction = null;
                Dictionary<AtomicAction, AtomicAction> elim = new Dictionary<AtomicAction, AtomicAction>();

                for (QKeyValue kv = action.proc.Attributes; kv != null; kv = kv.Next)
                {
                    if (kv.Key == CivlAttributes.IS)
                    {
                        if (action.refinedAction != null || invariantAction != null)
                            Error(kv, "Duplicate inductive sequentialization");
                        if (kv.Params.Count == 2 &&
                            kv.Params[0] is string refinedActionName &&
                            kv.Params[1] is string invariantActionName)
                        {
                            action.refinedAction = FindAtomicAction(refinedActionName);
                            invariantAction = FindIsInvariant(invariantActionName);
                            if (action.refinedAction == null)
                                Error(kv, "Could not find refined atomic action");
                            else
                            {
                                if (!action.refinedAction.layerRange.Contains(layer + 1))
                                    Error(action.proc, $"IS target does not exist at layer {layer + 1}");
                                if (action.IsLeftMover && action.refinedAction.IsLeftMover)
                                    Error(action.proc, "IS output must preserve left moverness");
                            }

                            if (invariantAction == null)
                                Error(kv, "Could not find invariant action");
                            else if (!invariantAction.layerRange.Contains(layer))
                                Error(action.proc, $"IS invariant does not exist at layer {layer}");
                        }
                        else
                        {
                            Error(kv, "Inductive sequentialization attribute expects two strings");
                        }
                    }
                    if (kv.Key == CivlAttributes.ELIM)
                    {
                        if (kv.Params.Count >= 1 && kv.Params.Count <= 2 && kv.Params.All(p => p is string))
                        {
                            string actionName = (string)kv.Params[0];
                            AtomicAction elimAction = FindAtomicAction(actionName);
                            AtomicAction absAction = null;
                            if (elimAction == null)
                            {
                                Error(kv, "Could not find elim atomic action");
                            }
                            else
                            {
                                if (elimAction.pendingAsyncCtor == null)
                                    Error(kv, $"No pending async constructor for atomic action {actionName}");
                                if (!elimAction.layerRange.Contains(layer)) 
                                    Error(kv, $"Elim action does not exist at layer {layer}");
                            }
                            if (kv.Params.Count == 2)
                            {
                                string abstractionName = (string)kv.Params[1];
                                absAction = FindAtomicAction(abstractionName);
                                if (absAction == null)
                                    absAction = FindIsAbstraction(abstractionName);
                                if (absAction == null)
                                    Error(kv, "Could not find abstraction action");
                                else if (!absAction.layerRange.Contains(layer))
                                    Error(kv, "Abstraction action does not exist at layer {layer}");
                            }
                            else
                            {
                                absAction = elimAction;
                            }
                            if (elimAction != null && absAction != null)
                            {
                                CheckSignatures(elimAction.proc, absAction.proc);
                                elim[elimAction] = absAction;
                            }
                        }
                        else
                        {
                            Error(kv, "Elim attribute expects one or two strings");
                        }
                    }
                }

                if (invariantAction != null && action.refinedAction != null)
                {
                    // Invariant action can have extra choice parameter and
                    // IS output might not have pending async parameter.
                    CheckSignatures(action.proc, invariantAction.proc, invariantAction.hasChoice ? 1 : 0);
                    CheckSignatures(action.refinedAction.proc, action.proc, action.HasPendingAsyncs && !action.refinedAction.HasPendingAsyncs ? 1 : 0);
                    inductiveSequentializations.Add(
                        new InductiveSequentialization(action, action.refinedAction, invariantAction, elim));
                }
            }
        }

        private void TypeCheckIntroductionProcedures()
        {
            // Introduction procedure:
            // * no {:yield}
            // * no mover type
            // layer range
            foreach (var proc in program.Procedures.Where(IsIntroductionProcedure))
            {
                LayerRange layerRange = ToLayerRange(FindLayers(proc.Attributes), proc);
                if (proc.Modifies.Count > 0)
                {
                    if (layerRange.lowerLayerNum == layerRange.upperLayerNum)
                    {
                        foreach (var ie in proc.Modifies)
                        {
                            if (GlobalVariableLayerRange(ie.Decl).lowerLayerNum != layerRange.lowerLayerNum)
                            {
                                Error(ie,"Introduction procedures can modify a shared variable only on its introduction layer");
                            }
                        }
                    }
                    else
                    {
                        Error(proc,"Layer range of an introduction procedure that modifies a global variable should be singleton");
                    }
                }
                procToIntroductionProc[proc] = new IntroductionProc(proc, layerRange);
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

            foreach (var proc in program.Procedures.Where(IsYieldingProcedure))
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
                MoverType? moverType = GetMoverType(proc);
                if (refinesName != null && moverType.HasValue)
                {
                    Error(proc, "A yielding procedure cannot have both a refines annotation and a mover type");
                    continue;
                }

                if (refinesName != null) // proc is an action procedure
                {
                    AtomicAction refinedAction = FindAtomicAction(refinesName);
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

                    CheckSignatures(proc, refinedAction.proc, refinedAction.HasPendingAsyncs ? 1 : 0);

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
            }
        }

        // CheckSignatures and MatchFormals are adapted from type checking implementations in Absy.cs,
        // i.e., that implementations have the same interface as the corresponding procedure.
        private void CheckSignatures(DeclWithFormals decl1, DeclWithFormals decl2, int extraOutputs = 0)
        {
            if (decl1.TypeParameters.Count != decl2.TypeParameters.Count)
            {
                // if the numbers of type parameters are different, it is
                // difficult to compare the argument types
                checkingContext.Error(decl1, $"mismatched number of type parameters in {decl2.Name}");
            }
            else
            {
                // In some cases there can be extra output parameters related to pending asyncs
                MatchFormals(decl1, decl2, decl1.InParams, decl2.InParams, "in");
                MatchFormals(decl1, decl2, decl1.OutParams, decl2.OutParams, "out", extraOutputs);
            }
        }

        private void CheckInputSignature(DeclWithFormals decl1, DeclWithFormals decl2)
        {
            if (decl1.TypeParameters.Count != decl2.TypeParameters.Count)
            {
                checkingContext.Error(decl1, $"mismatched number of type parameters in {decl2.Name}");
            }
            else
            {
                MatchFormals(decl1, decl2, decl1.InParams, decl2.InParams, "in", 0, false);
            }
        }

        private void MatchFormals(DeclWithFormals decl1, DeclWithFormals decl2,
            List<Variable> formals1, List<Variable> formals2, string inout,
            int extraParams = 0, bool checkLinearity = true)
        {
            if (formals1.Count < formals2.Count - extraParams || formals1.Count > formals2.Count)
            {
                checkingContext.Error(decl1, $"mismatched number of {inout}-parameters in {decl2.Name}");
            }
            else
            {
                // unify the type parameters so that types can be compared
                IDictionary<TypeVariable, Type> subst1 = new Dictionary<TypeVariable, Type>();
                IDictionary<TypeVariable, Type> subst2 = new Dictionary<TypeVariable, Type>();

                for (int i = 0; i < decl1.TypeParameters.Count; ++i)
                {
                    TypeVariable newVar = new TypeVariable(Token.NoToken, decl1.TypeParameters[i].Name);
                    subst1.Add(decl1.TypeParameters[i], newVar);
                    subst2.Add(decl2.TypeParameters[i], newVar);
                }

                for (int i = 0; i < formals1.Count; i++)
                {
                    // For error messages below
                    string name1 = formals1[i].Name;
                    string name2 = formals2[i].Name;
                    string msg = (name1 == name2)? name1 : $"{name1} (named {name2} in {decl2.Name})";

                    // the names of the formals are allowed to change from the proc to the impl
                    // but types must be identical
                    Type t1 = formals1[i].TypedIdent.Type.Substitute(subst1);
                    Type t2 = formals2[i].TypedIdent.Type.Substitute(subst2);
                    if (!t1.Equals(t2))
                    {
                        checkingContext.Error(decl1, $"mismatched type of {inout}-parameter in {decl2.Name}: {msg}");
                    }

                    if (checkLinearity &&
                       (QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR) != QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR) ||
                        QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR_IN) != QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR_IN) ||
                        QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR_OUT) != QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR_OUT)))
                    {
                        checkingContext.Error(decl1, $"mismatched linearity type of {inout}-parameter in {decl2.Name}: {msg}");
                    }
                }
            }
        }

        private void TypeCheckLocalVariables()
        {
            // Local variable with no declared introduction layer implicitly have layer int.MinValue.
            // However, to save space and avoid hash collisions, we do not explicitly store variables with layer int.MinValue.

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
                    int upperLayer = procToYieldingProc[impl.Proc].upperLayer;
                    int layer = FindLocalVariableLayer(impl, v, upperLayer);
                    if (v.HasAttribute(CivlAttributes.PENDING_ASYNC))
                    {
                        if (implToPendingAsyncCollector.ContainsKey(impl))
                            Error(v, "Duplicate pending async collector");
                        if (!v.TypedIdent.Type.Equals(pendingAsyncMultisetType))
                            Error(v, "Pending async collector is of incorrect type");
                        if (layer != int.MinValue && layer != upperLayer)
                            Error(v, "Pending async collector must be introduced at the disappearing layer of the enclosing procedure");
                        implToPendingAsyncCollector[impl] = v;
                    }
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

        private void TypeCheckPendingAsyncMachinery()
        {
            foreach (var typeCtorDecl in program.TopLevelDeclarations.OfType<TypeCtorDecl>())
            {
                if (typeCtorDecl.HasAttribute(CivlAttributes.PENDING_ASYNC))
                {
                    if (pendingAsyncType == null)
                    {
                        pendingAsyncType = new CtorType(typeCtorDecl.tok, typeCtorDecl, new List<Type>());
                        pendingAsyncMultisetType = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { pendingAsyncType }, Type.Int);
                    }
                    else
                    {
                        Error(typeCtorDecl, $"Duplicate pending async type {typeCtorDecl.Name}");
                    }
                }
            }

            if(pendingAsyncType != null)
            {
                pendingAsyncAdd = new Function(Token.NoToken, "AddPAs",
                    new List<Variable>
                    {
                        VarHelper.Formal("a", pendingAsyncMultisetType, true),
                        VarHelper.Formal("b", pendingAsyncMultisetType, true)
                    },
                    VarHelper.Formal("c", pendingAsyncMultisetType, false));
                if (CommandLineOptions.Clo.UseArrayTheory)
                {
                    pendingAsyncAdd.AddAttribute("builtin", "MapAdd");
                }
                else
                {
                    throw new NotSupportedException("Pending asyncs need array theory");
                }
                program.AddTopLevelDeclaration(pendingAsyncAdd);
            }

            foreach (var ctor in program.TopLevelDeclarations.OfType<DatatypeConstructor>())
            {
                string actionName = QKeyValue.FindStringAttribute(ctor.Attributes, CivlAttributes.PENDING_ASYNC);
                if (actionName != null)
                {
                    AtomicAction action = FindAtomicAction(actionName);
                    if (!ctor.OutParams[0].TypedIdent.Type.Equals(pendingAsyncType))
                    {
                        Error(ctor, "Pending async constructor is of incorrect type");
                    }
                    if (action == null)
                    {
                        Error(ctor, $"{actionName} is not an atomic action");
                    }
                    else
                    {
                        if (action.pendingAsyncCtor != null)
                            Error(ctor, $"Duplicate pending async constructor for action {actionName}");
                        if (action.proc.HasAttribute(CivlAttributes.IS))
                            Error(ctor, "Actions transformed by IS cannot be pending asyncs");
                        CheckInputSignature(action.proc, ctor);
                        action.pendingAsyncCtor = ctor;
                    }
                }
            }

            foreach (var action in procToAtomicAction.Values.Union(procToIsAbstraction.Values))
            {
                if (action.impl.OutParams.Count >= 1)
                {
                    CheckPendingAsyncOutput(action, action.impl.OutParams.Last());
                    if (action.HasPendingAsyncs && action.IsRightMover)
                        Error(action.proc, "Action with pending async cannot be a right mover");
                }
                if (action.pendingAsyncCtor != null && action.impl.OutParams.Count > (action.HasPendingAsyncs ? 1 : 0))
                    Error(action.proc, $"Action declared as pending async cannot have output parameters");

            }
            foreach (var action in procToIsInvariant.Values)
            {
                var count = action.impl.OutParams.Count;
                if (count >= 2 &&
                    action.impl.OutParams[count - 1].HasAttribute(CivlAttributes.CHOICE))
                {
                    action.hasChoice = true;
                    CheckPendingAsyncOutput(action, action.impl.OutParams[count - 2]);
                    CheckPendingAsyncChoice(action, action.impl.OutParams[count - 1]);
                }
                else if (count >= 1)
                {
                    CheckPendingAsyncOutput(action, action.impl.OutParams[count - 1]);
                }
                if(!action.HasPendingAsyncs)
                    Error(action.proc, "Invariant action must have pending async output");
            }
        }

        private void CheckPendingAsyncOutput(AtomicAction action, Variable outParam)
        {
            List<AtomicAction> pendingAsyncs = new List<AtomicAction>();
            bool found = false;
            for (QKeyValue kv = outParam.Attributes; kv != null; kv = kv.Next)
            {
                if (kv.Key == CivlAttributes.PENDING_ASYNC)
                {
                    found = true;
                    foreach (var param in kv.Params)
                    {
                        if (param is string actionName)
                        {
                            var pendingAsync = FindAtomicAction(actionName);
                            if (pendingAsync != null)
                            {
                                if (!action.layerRange.Subset(pendingAsync.layerRange))
                                    Error(kv, $"Pending async {actionName} is not available on all layers of {action.proc.Name}");
                                if (pendingAsync.pendingAsyncCtor != null)
                                    pendingAsyncs.Add(pendingAsync);
                                else
                                    Error(kv, $"No pending async constructor for atomic action {actionName}");
                            }
                            else
                                Error(kv, $"Could not find atomic action {actionName}");
                        }
                        else
                        {
                            Error(kv, "Expected atomic action names");
                        }
                    }
                }
            }
            if (found)
            {
                if (outParam.TypedIdent.Type.Equals(pendingAsyncMultisetType))
                {
                    action.pendingAsyncs = new HashSet<AtomicAction>(pendingAsyncs);
                }
                else
                {
                    Error(outParam, "Pending async output is of incorrect type");
                }
            }
        }

        private void CheckPendingAsyncChoice(AtomicAction action, Variable outParam)
        {
            if (!outParam.TypedIdent.Type.Equals(pendingAsyncType))
                Error(outParam, "Pending aync choice is of incorrect type");
        }

        #region Helpers for attribute parsing
        private bool IsYieldingProcedure(Procedure proc)
        {
            return proc.HasAttribute(CivlAttributes.YIELDS);
        }

        private bool IsAtomicAction(Procedure proc)
        {
            return !IsYieldingProcedure(proc) &&
                (GetMoverType(proc) != null ||
                 proc.HasAttribute(CivlAttributes.IS_INVARIANT) ||
                 proc.HasAttribute(CivlAttributes.IS_ABSTRACTION));
        }

        private bool IsIntroductionProcedure(Procedure proc)
        {
            return !IsYieldingProcedure(proc) && !IsAtomicAction(proc) && FindLayers(proc.Attributes).Count > 0;
        }

        private MoverType GetActionMoverType(Procedure proc)
        {
            if (proc.HasAttribute(CivlAttributes.IS_INVARIANT))
                return MoverType.Atomic;
            else if (proc.HasAttribute(CivlAttributes.IS_ABSTRACTION))
                return MoverType.Left;
            else
                return GetMoverType(proc).Value;
        }

        /// Parses attributes for mover type declarations.
        /// Returns the first mover type found (or null if none is found) and issues warnings if multiple mover types are found.
        private MoverType? GetMoverType(ICarriesAttributes absy)
        {
            MoverType? moverType = null;

            for (QKeyValue kv = absy.Attributes; kv != null; kv = kv.Next)
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
                            checkingContext.Warning(kv, "Ignoring duplicate mover type declaration ({0})", kv.Key);
                        else
                            moverType = x;
                    }
                }
            }

            return moverType;
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
                        checkingContext.Error(kv, "Layer has to be an integer");
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
        #endregion

        #region Public access methods
        public LayerRange GlobalVariableLayerRange(Variable g)
        {
            if (globalVarToLayerRange.ContainsKey(g))
                return globalVarToLayerRange[g];
            return LayerRange.MinMax;
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

        public bool CallExists(CallCmd callCmd, int enclosingProcLayerNum, int layerNum)
        {
            Debug.Assert(procToIntroductionProc.ContainsKey(callCmd.Proc));
            var introductionProc = procToIntroductionProc[callCmd.Proc];
            if (!introductionProc.IsLemma)
            {
                return enclosingProcLayerNum == layerNum;
            }
            else
            {
                var layers = FindLayers(callCmd.Attributes);
                return layers.Contains(layerNum);
            }
        }

        public AtomicAction FindAtomicAction(string name)
        {
            return procToAtomicAction.Values.FirstOrDefault(a => a.proc.Name == name);
        }

        public AtomicAction FindIsInvariant(string name)
        {
            return procToIsInvariant.Values.FirstOrDefault(a => a.proc.Name == name);
        }

        public AtomicAction FindIsAbstraction(string name)
        {
            return procToIsAbstraction.Values.FirstOrDefault(a => a.proc.Name == name);
        }

        public AtomicAction FindAtomicActionOrAbstraction(string name)
        {
            var action = FindAtomicAction(name);
            if (action != null) return action;
            return FindIsAbstraction(name);
        }

        public IEnumerable<AtomicAction> AllActions =>
            procToAtomicAction.Union(procToIsInvariant).Union(procToIsAbstraction)
            .Select(x => x.Value);

        public void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
        }
        #endregion

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
                foreach(var g in atomicAction.gate)
                {
                    VisitAssertCmd(g);
                }
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

            public override Cmd VisitCallCmd(CallCmd node)
            {
                ctc.Error(node, "Call command not allowed inside an atomic action");
                return base.VisitCallCmd(node);
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
                CheckMoverProcModifiesClause();
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

            private bool Require(bool condition, Absy absy, string errorMessage)
            {
                if (!condition)
                    ctc.Error(absy, errorMessage);
                return condition;
            }

            private void VisitYieldingProcCallCmd(CallCmd call, YieldingProc callerProc, YieldingProc calleeProc)
            {
                if (calleeProc is ActionProc calleeActionProc)
                {
                    if (callerProc.upperLayer > calleeProc.upperLayer)
                    {
                        var highestRefinedAction = calleeActionProc.RefinedActionAtLayer(callerProc.upperLayer);
                        if (highestRefinedAction == null)
                        {
                            ctc.Error(call, $"Called action is not available at layer {callerProc.upperLayer}");
                        }
                        else
                        {
                            if (call.IsAsync)
                            {
                                if (call.HasAttribute(CivlAttributes.SYNC))
                                    Require(calleeActionProc.refinedAction.IsLeftMover, call, "Synchronized call must be a left mover");
                                else
                                    Require(highestRefinedAction.pendingAsyncCtor != null, call, "No pending-async constructor available for this call");
                            }
                            if (!(callerProc is ActionProc))
                            {
                                Require(!highestRefinedAction.HasPendingAsyncs && (!call.IsAsync || call.HasAttribute(CivlAttributes.SYNC)),
                                    call, "Only action procedures can summarize pending asyncs");
                            }
                        }
                    }
                    else if (callerProc.upperLayer == calleeProc.upperLayer)
                    {
                        // Calling an action procedure with the same disappearing layer as the caller is only possible if
                        // (1) the call is a non-synchronized asynchronous call (i.e., results in a pending async), and
                        // (2) the caller is an action procedure (that can summarize the pending async).
                        Require(callerProc is ActionProc && call.IsAsync && !call.HasAttribute(CivlAttributes.SYNC),
                            call, "Call to an action procedure on the same layer must be asynchronous (and turn into a pending async)");
                        Require(calleeActionProc.refinedAction.pendingAsyncCtor != null, call, "No pending-async constructor available for this call");
                    }
                    else
                    {
                        ctc.Error(call, "This call cannot have a callee with higher layer than the caller");
                    }
                }
                else if (calleeProc is SkipProc)
                {
                    if (callerProc is MoverProc)
                    {
                        Require(callerProc.upperLayer > calleeProc.upperLayer, call,
                            "The layer of the caller must be greater than the layer of the callee");
                    }
                    else
                    {
                        Require(callerProc.upperLayer >= calleeProc.upperLayer, call,
                            "The layer of the caller must be greater than or equal to the layer of the callee");
                    }
                    Require(callerProc.upperLayer == calleeProc.upperLayer || call.Outs.Count == 0, call,
                        $"Call is not erasable at layer {callerProc.upperLayer}");
                    if (callerProc is ActionProc && call.Outs.Count > 0 && enclosingImpl.OutParams.Count > 0)
                    {
                        // Skip procedures have the effect of havocing their output variables.
                        // Currently, refinement checking does not account for that,
                        // so we forbid propagation to the callers output variables.
                        HashSet<Variable> callerOutParams = new HashSet<Variable>(enclosingImpl.OutParams);
                        foreach (var x in call.Outs)
                        {
                            if (callerOutParams.Contains(x.Decl))
                            {
                                ctc.Error(x, "An output variable of the enclosing implementation cannot be used as output argument for this call");
                            }
                        }
                    }
                }
                else if (calleeProc is MoverProc)
                {
                    Require(callerProc.upperLayer == calleeProc.upperLayer, call,
                        "The layer of the caller must be equal to the layer of the callee");
                    if (call.IsAsync)
                    {
                        Require(calleeProc.IsLeftMover, call, "Synchronized call must be a left mover");
                    }
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
                            ctc.checkingContext.Error(ie, "Variable {0} introduced at layer {1} cannot be passed to formal parameter introduced at layer {2}", ie.Decl.Name, actualIntroLayer, formalIntroLayer);
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

            private void VisitIntroductionProcCallCmd(CallCmd call, YieldingProc callerProc,
                IntroductionProc calleeProc)
            {
                if (!calleeProc.IsLemma)
                {
                    // Call to ordinary introduction procedure only exists at the upper layer of caller yielding procedure.
                    if (!calleeProc.layerRange.Contains(callerProc.upperLayer))
                    {
                        ctc.checkingContext.Error(call, "Introduction procedure cannot be called at layer {0}", callerProc.upperLayer);
                    }
                    // All local variables are already introduced.
                    // Check output variables are introduced at upper layer of caller yielding procedure.
                    foreach (var ie in call.Outs)
                    {
                        if (ctc.LocalVariableIntroLayer(ie.Decl) != callerProc.upperLayer)
                        {
                            ctc.checkingContext.Error(ie, "Output variable {0} must be introduced at layer {1}",
                                ie.Decl.Name, callerProc.upperLayer);
                        }
                    }
                }
                else
                {
                    // All local variables used as input must be available at all layers at which this call exists.
                    // We compute the maximum introduction layer of all local variables used as input.
                    // This layer should be no larger than each layer at which this call exists.
                    localVariableAccesses = new List<IdentifierExpr>();
                    foreach (var e in call.Ins)
                    {
                        Visit(e);
                    }
                    var minLayerCallPossible = localVariableAccesses
                        .Select(ie => ctc.LocalVariableIntroLayer(ie.Decl))
                        .Concat1(calleeProc.layerRange.lowerLayerNum)
                        .Max();
                    var calledLayers = ctc.FindLayers(call.Attributes);
                    if (calledLayers.Count == 0)
                    {
                        ctc.checkingContext.Error(call, "Call to introduction lemma procedure must be annotated with layers");
                    }
                    else
                    {
                        var minCalledLayer = calledLayers.Min();
                        var maxCalledLayer = calledLayers.Max();
                        if (minCalledLayer < minLayerCallPossible)
                        {
                            ctc.checkingContext.Error(call, "Call not possible at layer {0}", minCalledLayer);
                        }

                        if (maxCalledLayer > callerProc.upperLayer)
                        {
                            ctc.checkingContext.Error(call, "Call not possible at layer {0}", maxCalledLayer);
                        }
                    }
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

            private void CheckMoverProcModifiesClause()
            {
                // TODO: Check the modifies clause of mover procedures.
                // Calls to introduction procedures!

                if (yieldingProc is MoverProc caller)
                {
                    var declaredModifiedVars = caller.modifiedGlobalVars;
                    HashSet<Variable> mods = null;
                    foreach (var callCmd in enclosingImpl.Blocks.SelectMany(b => b.Cmds).OfType<CallCmd>())
                    {
                        if (ctc.procToYieldingProc.TryGetValue(callCmd.Proc, out YieldingProc callee))
                        {
                            if (callee is ActionProc actionProc)
                            {
                                mods = actionProc.refinedAction.modifiedGlobalVars;
                            }
                            else if (callee is MoverProc moverProc)
                            {
                                mods = moverProc.modifiedGlobalVars;
                            }
                            else
                            {
                                Debug.Assert(callee is SkipProc);
                                mods = new HashSet<Variable>();
                            }
                        }
                        else if (ctc.procToIntroductionProc.ContainsKey(callCmd.Proc))
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
                                ctc.Error(callCmd, $"Modified variable {mod.Name} does not appear in modifies clause of mover procedure");
                            }
                        }
                    }
                }
            }
        }

        private class AttributeEraser : ReadOnlyVisitor
        {
            public static void Erase(CivlTypeChecker ctc)
            {
                var attributeEraser = new AttributeEraser();
                attributeEraser.VisitProgram(ctc.program);
                foreach (var action in ctc.AllActions)
                {
                    attributeEraser.VisitAtomicAction(action);
                }
            }

            public override Procedure VisitProcedure(Procedure node)
            {
                CivlAttributes.RemoveCivlAttributes(node);
                return base.VisitProcedure(node);
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                CivlAttributes.RemoveCivlAttributes(node);
                return base.VisitImplementation(node);
            }

            public override Requires VisitRequires(Requires node)
            {
                CivlAttributes.RemoveCivlAttributes(node);
                return base.VisitRequires(node);
            }

            public override Ensures VisitEnsures(Ensures node)
            {
                CivlAttributes.RemoveCivlAttributes(node);
                return base.VisitEnsures(node);
            }

            public override Cmd VisitAssertCmd(AssertCmd node)
            {
                CivlAttributes.RemoveCivlAttributes(node);
                return base.VisitAssertCmd(node);
            }

            public override Variable VisitVariable(Variable node)
            {
                CivlAttributes.RemoveCivlAttributes(node);
                return base.VisitVariable(node);
            }

            public override Function VisitFunction(Function node)
            {
                CivlAttributes.RemoveCivlAttributes(node);
                return base.VisitFunction(node);
            }

            public override Declaration VisitDeclaration(Declaration node)
            {
                CivlAttributes.RemoveCivlAttributes(node);
                return base.VisitDeclaration(node);
            }

            public void VisitAtomicAction(AtomicAction action)
            {
                Visit(action.firstImpl);
                Visit(action.secondImpl);
            }
        }
    }
}
