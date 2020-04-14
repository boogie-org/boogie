using System;
using System.Collections.Generic;
using System.ComponentModel.Design;
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
        // Use public access methods.
        private Dictionary<Variable, LayerRange> globalVarToLayerRange;
        private Dictionary<Variable, LayerRange> localVarToLayerRange;

        public Dictionary<Procedure, AtomicAction> procToAtomicAction;
        public Dictionary<Procedure, AtomicAction> procToIsInvariant;
        public Dictionary<Procedure, AtomicAction> procToIsAbstraction;
        public Dictionary<Procedure, YieldingProc> procToYieldingProc;
        public Dictionary<Procedure, LemmaProc> procToLemmaProc;
        public Dictionary<Procedure, IntroductionAction> procToIntroductionAction;
        public CommutativityHints commutativityHints;

        public List<InductiveSequentialization> inductiveSequentializations;

        public Dictionary<Absy, HashSet<int>> absyToLayerNums;

        public CtorType pendingAsyncType;
        public MapType pendingAsyncMultisetType;
        public Function pendingAsyncAdd;
        public Dictionary<Implementation, Variable> implToPendingAsyncCollector;

        // These collections are for convenience in later phases and are only initialized at the end of type checking.
        public List<int> allRefinementLayers;
        public IEnumerable<Variable> GlobalVariables => globalVarToLayerRange.Keys;

        public LinearTypeChecker linearTypeChecker;
        
        public CivlTypeChecker(Program program)
        {
            this.checkingContext = new CheckingContext(null);
            this.program = program;

            this.globalVarToLayerRange = new Dictionary<Variable, LayerRange>();
            this.localVarToLayerRange = new Dictionary<Variable, LayerRange>();
            this.absyToLayerNums = new Dictionary<Absy, HashSet<int>>();
            this.procToAtomicAction = new Dictionary<Procedure, AtomicAction>();
            this.procToIsInvariant = new Dictionary<Procedure, AtomicAction>();
            this.procToIsAbstraction = new Dictionary<Procedure, AtomicAction>();
            this.procToYieldingProc = new Dictionary<Procedure, YieldingProc>();
            this.procToLemmaProc = new Dictionary<Procedure, LemmaProc>();
            this.procToIntroductionAction = new Dictionary<Procedure, IntroductionAction>();
            this.implToPendingAsyncCollector = new Dictionary<Implementation, Variable>();
            this.inductiveSequentializations = new List<InductiveSequentialization>();
        }

        public void TypeCheck()
        {
            TypeCheckGlobalVariables();
            TypeCheckLemmaProcedures();

            TypeCheckActionDecls();
            TypeCheckPendingAsyncMachinery();

            if (checkingContext.ErrorCount > 0)
                return;

            TypeCheckInductiveSequentializations();
            TypeCheckYieldingProcedureDecls();
            TypeCheckLocalVariables();

            if (checkingContext.ErrorCount > 0)
                return;

            TypeCheckActionImpls();
            TypeCheckYieldingProcedureImpls();

            TypeCheckRefinementLayers();

            TypeCheckCommutativityHints();

            AttributeEraser.Erase(this);

            if (checkingContext.ErrorCount > 0)
                return;

            var yieldSufficiencyTypeChecker = new YieldSufficiencyTypeChecker(this);
            yieldSufficiencyTypeChecker.TypeCheck();
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

            foreach(var g in GlobalVariables)
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
                globalVarToLayerRange[g] = ToLayerRange(FindLayers(g.Attributes), g);
            }
        }

        private void TypeCheckActionDecls()
        {
            // Atomic action:
            // * no {:yield}
            // * {:right}, {:left}, {:both}, {:atomic}, {:intro}, {:IS_invariant}, {:IS_abstraction}
            // * layer range
            foreach (var proc in program.Procedures.Where(IsAction))
            {
                LayerRange layerRange = ToLayerRange(FindLayers(proc.Attributes), proc);
                if (proc.Requires.Count + proc.Ensures.Count > 0)
                {
                    Error(proc, "Action cannot have preconditions or postconditions");
                }
                var actionImpls = program.Implementations.Where(i => i.Name == proc.Name).ToList();
                if (actionImpls.Count == 0)
                {
                    Error(proc, "Action specification missing");
                    continue;
                }
                if (actionImpls.Count > 1)
                {
                    Error(proc, "More then one action specification provided");
                    continue;
                }

                Implementation impl = actionImpls[0];
                impl.PruneUnreachableBlocks();
                Graph<Block> cfg = Program.GraphFromImpl(impl);
                if (!Graph<Block>.Acyclic(cfg, impl.Blocks[0]))
                {
                    Error(proc, "Action specification cannot have loops");
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
                        Error(cmd, "Assert is only allowed in the gate of an action");
                    }
                }
                foreach (var cmd in impl.Blocks.Skip(1).SelectMany(b => b.cmds).OfType<AssertCmd>())
                {
                    Error(cmd, "Assert is only allowed in the gate of an action");
                }

                if (proc.HasAttribute(CivlAttributes.INTRO))
                {
                    if (GetMoverType(proc) != null)
                    {
                        Error(proc, "Action must be either an atomic action or introduction action");
                    }
                    else if (layerRange.lowerLayerNum != layerRange.upperLayerNum)
                    {
                        Error(proc,"Layer range of an introduction action should be singleton");
                    }
                    else if (proc.Modifies.Any(ie => GlobalVariableLayerRange(ie.Decl).lowerLayerNum != layerRange.lowerLayerNum))
                    {
                        Error(proc,"Introduction actions can modify a global variable only on its introduction layer");
                    }
                    else
                    {
                        procToIntroductionAction[proc] = new IntroductionAction(proc, impl, layerRange);
                    }
                }
                else
                {
                    var action = new AtomicAction(proc, impl, layerRange, GetActionMoverType(proc));
                    if (proc.HasAttribute(CivlAttributes.IS_INVARIANT))
                        procToIsInvariant[proc] = action;
                    else if (proc.HasAttribute(CivlAttributes.IS_ABSTRACTION))
                        procToIsAbstraction[proc] = action;
                    else
                        procToAtomicAction[proc] = action;
                }
            }
        }

        private void TypeCheckActionImpls()
        {
            ActionVisitor actionVisitor = new ActionVisitor(this);
            foreach (var action in procToAtomicAction.Values)
            {
                actionVisitor.VisitAction(action);
            }
            foreach (var action in procToIntroductionAction.Values)
            {
                actionVisitor.VisitAction(action);
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
                                if (!action.HasPendingAsyncs)
                                    Error(action.proc, "IS target must have pending async output");
                                if (!action.refinedAction.layerRange.Contains(layer + 1))
                                    Error(action.proc, $"IS target does not exist at layer {layer + 1}");
                                if (action.IsLeftMover && !action.refinedAction.IsLeftMover)
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
                                CheckInductiveSequentializationAbstractionSignature(elimAction, absAction);
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
                    CheckInductiveSequentializationSignature(action, invariantAction);
                    if(checkingContext.ErrorCount == 0)
                    {
                        inductiveSequentializations.Add(
                            new InductiveSequentialization(action, action.refinedAction, invariantAction, elim));
                    }
                }
            }
        }

        private void TypeCheckLemmaProcedures()
        {
            // Lemma procedure:
            // * {:lemma}
            // * no {:yield}
            // * no mover type
            // * no layer range
            foreach (var proc in program.Procedures.Where(IsLemmaProcedure))
            {
                if (proc.Modifies.Count > 0)
                {
                    Error(proc, "Lemma procedure cannot modify a global variable");
                }
                else
                {
                    procToLemmaProc[proc] = new LemmaProc(proc);
                }
            }

            if (checkingContext.ErrorCount > 0) return;

            LemmaProcedureVisitor visitor = new LemmaProcedureVisitor(this);
            foreach (Procedure proc in program.Procedures.Where(proc => procToLemmaProc.ContainsKey(proc)))
            {
                visitor.VisitProcedure(proc);
            }
            foreach (Implementation impl in program.Implementations.Where(impl => procToLemmaProc.ContainsKey(impl.Proc)))
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
                foreach (var param in Enumerable.Union(proc.InParams, proc.OutParams))
                {
                    localVarToLayerRange[param] = FindLocalVariableLayerRange(proc, param, upperLayer);
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
                        checkingContext.Error(proc, "Refined atomic action must be available at layer {0}", upperLayer + 1);
                        continue;
                    }
                    var actionProc = new ActionProc(proc, refinedAction, upperLayer);
                    CheckRefinementSignature(actionProc);
                    procToYieldingProc[proc] = actionProc;
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

        public class SignatureMatcher
        {
            public static string IN = "in";
            public static string OUT = "out";

            private DeclWithFormals decl1;
            private DeclWithFormals decl2;
            private CheckingContext checkingContext;

            public SignatureMatcher(DeclWithFormals decl1, DeclWithFormals decl2, CheckingContext checkingContext)
            {
                this.decl1 = decl1;
                this.decl2 = decl2;
                this.checkingContext = checkingContext;
            }

            public void MatchFormals(List<Variable> formals1, List<Variable> formals2,
                string inout, bool checkLinearity = true)
            {
                if (formals1.Count != formals2.Count)
                {
                    checkingContext.Error(decl1, $"mismatched number of {inout}-parameters in {decl2.Name}");
                }
                else
                {
                    for (int i = 0; i < formals1.Count; i++)
                    {
                        // For error messages below
                        string name1 = formals1[i].Name;
                        string name2 = formals2[i].Name;
                        string msg = (name1 == name2) ? name1 : $"{name1} (named {name2} in {decl2.Name})";

                        // the names of the formals are allowed to change from the proc to the impl
                        // but types must be identical
                        Type t1 = formals1[i].TypedIdent.Type;
                        Type t2 = formals2[i].TypedIdent.Type;
                        if (!t1.Equals(t2))
                        {
                            checkingContext.Error(formals1[i], $"mismatched type of {inout}-parameter in {decl2.Name}: {msg}");
                        }

                        if (checkLinearity &&
                            (QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR) != 
                             QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR) ||
                             QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR_IN) != 
                             QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR_IN) ||
                             QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR_OUT) !=
                             QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR_OUT)))
                        {
                            checkingContext.Error(formals1[i], $"mismatched linearity type of {inout}-parameter in {decl2.Name}: {msg}");
                        }
                    }
                }
            }
        }

        private void CheckRefinementSignature(ActionProc actionProc)
        {
            var signatureMatcher = new SignatureMatcher(actionProc.proc, actionProc.refinedAction.proc, checkingContext);
            Func<Variable, bool> isRemainingVariable = x =>
                LocalVariableLayerRange(x).upperLayerNum == actionProc.upperLayer &&
                !actionProc.hiddenFormals.Contains(x);
            var procInParams = actionProc.proc.InParams.Where(isRemainingVariable).ToList();
            var procOutParams = actionProc.proc.OutParams.Where(isRemainingVariable).ToList();
            var actionInParams = actionProc.refinedAction.proc.InParams;
            var actionOutParams = actionProc.refinedAction.proc.OutParams.SkipEnd(actionProc.refinedAction.HasPendingAsyncs ? 1 : 0).ToList();
            signatureMatcher.MatchFormals(procInParams, actionInParams, SignatureMatcher.IN);
            signatureMatcher.MatchFormals(procOutParams, actionOutParams, SignatureMatcher.OUT);
        }

        private void CheckInductiveSequentializationAbstractionSignature(AtomicAction original, AtomicAction abstraction)
        {
            // Input and output parameters have to match exactly
            var signatureMatcher = new SignatureMatcher(original.proc, abstraction.proc, checkingContext);
            signatureMatcher.MatchFormals(original.proc.InParams, abstraction.proc.InParams, SignatureMatcher.IN);
            signatureMatcher.MatchFormals(original.proc.OutParams, abstraction.proc.OutParams, SignatureMatcher.OUT);
        }

        private void CheckPendingAsyncSignature(AtomicAction action, DatatypeConstructor ctor)
        {
            // Pending asyncs cannot have output parameters, and we do not require linear annotations to be repeated in the pending async constructor
            var signatureMatcher = new SignatureMatcher(action.proc, ctor, checkingContext);
            signatureMatcher.MatchFormals(action.proc.InParams, ctor.InParams, SignatureMatcher.IN, false);
        }

        private void CheckInductiveSequentializationSignature(AtomicAction action, AtomicAction invariantAction)
        {
            // We drop pending async parameters, and in invariant action the choice parameter if present
            var actionOutParams = action.proc.OutParams.SkipEnd(1).ToList();
            var invariantActionOutParams = invariantAction.proc.OutParams.SkipEnd(invariantAction.hasChoice ? 2 : 1).ToList();
            var refinedActionOutParams = action.refinedAction.proc.OutParams.SkipEnd(action.refinedAction.HasPendingAsyncs ? 1 : 0).ToList();
            
            var signatureMatcher = new SignatureMatcher(action.proc, invariantAction.proc, checkingContext);
            signatureMatcher.MatchFormals(action.proc.InParams, invariantAction.proc.InParams, SignatureMatcher.IN);
            signatureMatcher.MatchFormals(actionOutParams, invariantActionOutParams, SignatureMatcher.OUT);
            
            signatureMatcher = new SignatureMatcher(action.proc, action.refinedAction.proc, checkingContext);
            signatureMatcher.MatchFormals(action.proc.InParams, action.refinedAction.proc.InParams, SignatureMatcher.IN);
            signatureMatcher.MatchFormals(actionOutParams, refinedActionOutParams, SignatureMatcher.OUT);
        }

        private void TypeCheckLocalVariables()
        {
            foreach (Implementation impl in program.Implementations.Where(i => procToYieldingProc.ContainsKey(i.Proc)))
            {
                // then we collect the layers of local variables in implementations
                foreach (Variable v in impl.LocVars)
                {
                    int upperLayer = procToYieldingProc[impl.Proc].upperLayer;
                    localVarToLayerRange[v] = FindLocalVariableLayerRange(impl, v, upperLayer);
                    var layer = localVarToLayerRange[v].lowerLayerNum;
                    if (v.HasAttribute(CivlAttributes.PENDING_ASYNC))
                    {
                        if (implToPendingAsyncCollector.ContainsKey(impl))
                            Error(v, "Duplicate pending async collector");
                        if (!v.TypedIdent.Type.Equals(pendingAsyncMultisetType))
                            Error(v, "Pending async collector is of incorrect type");
                        if (layer != upperLayer)
                            Error(v, "Pending async collector must be introduced at the disappearing layer of the enclosing procedure");
                        implToPendingAsyncCollector[impl] = v;
                    }
                }
                // and finally just copy the layer information from procedure parameters to their corresponding implementation parameter
                // (i.e., layer declarations are only taken from procedures, not implementations)
                for (int i = 0; i < impl.Proc.InParams.Count; i++)
                {
                    Variable v = impl.Proc.InParams[i];
                    if (localVarToLayerRange.ContainsKey(v))
                        localVarToLayerRange[impl.InParams[i]] = localVarToLayerRange[v];
                }
                for (int i = 0; i < impl.Proc.OutParams.Count; i++)
                {
                    Variable v = impl.Proc.OutParams[i];
                    if (localVarToLayerRange.ContainsKey(v))
                        localVarToLayerRange[impl.OutParams[i]] = localVarToLayerRange[v];
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
                        CheckPendingAsyncSignature(action, ctor);
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

        private bool IsAction(Procedure proc)
        {
            return !IsYieldingProcedure(proc) &&
                (GetMoverType(proc) != null ||
                 proc.HasAttribute(CivlAttributes.INTRO) ||
                 proc.HasAttribute(CivlAttributes.IS_INVARIANT) ||
                 proc.HasAttribute(CivlAttributes.IS_ABSTRACTION));
        }
        
        private bool IsLemmaProcedure(Procedure proc)
        {
            return !IsYieldingProcedure(proc) && proc.HasAttribute(CivlAttributes.LEMMA);
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

        public List<int> FindLayers(QKeyValue kv)
        {
            List<int> layers = new List<int>();
            for (; kv != null; kv = kv.Next)
            {
                if (kv.Key != CivlAttributes.LAYER) continue;
                foreach (var o in kv.Params)
                {
                    if (o is LiteralExpr l && l.isBigNum)
                    {
                        var n = l.asBigNum;
                        if (n.IsNegative)
                        {
                            checkingContext.Error(kv, "Layer must be non-negative");
                        }
                        else if (!n.InInt32)
                        {
                            checkingContext.Error(kv, "Layer is too large (max value is Int32.MaxValue)");
                        }
                        else
                        {
                            layers.Add(l.asBigNum.ToIntSafe);
                        }
                    }
                    else
                    {
                        checkingContext.Error(kv, "Layer must be a non-negative integer");
                    }
                }
            }
            return layers;
        }

        private LayerRange ToLayerRange(List<int> layerNums, Absy absy, LayerRange defaultLayerRange = null)
        {
            // We return min-max range for invalid declarations in order to proceed with type checking.
            if (defaultLayerRange == null)
            {
                defaultLayerRange = LayerRange.MinMax;
            }
            if (layerNums.Count == 0)
            {
                return defaultLayerRange;
            }
            if (layerNums.Count == 1)
            {
                return new LayerRange(layerNums[0], layerNums[0]);
            }
            if (layerNums.Count == 2)
            {
                if (layerNums[0] <= layerNums[1])
                {
                    return new LayerRange(layerNums[0], layerNums[1]);
                }
            }
            Error(absy, "Invalid layer range");
            return defaultLayerRange;
        }

        private LayerRange FindLocalVariableLayerRange(Declaration decl, Variable v, int enclosingProcLayerNum)
        {
            var layerRange = ToLayerRange(FindLayers(v.Attributes), v, new LayerRange(LayerRange.Min, enclosingProcLayerNum));
            if (layerRange.upperLayerNum > enclosingProcLayerNum)
            {
                Error(decl, "Hidden layer of local variable cannot be greater than the disappearing layer of enclosing procedure");
            }
            return layerRange; 
        }
        #endregion

        #region Public access methods
        public LayerRange GlobalVariableLayerRange(Variable g)
        {
            Debug.Assert(globalVarToLayerRange.ContainsKey(g));
            return globalVarToLayerRange[g];
        }

        public LayerRange LocalVariableLayerRange(Variable l)
        {
            Debug.Assert(localVarToLayerRange.ContainsKey(l));
            return localVarToLayerRange[l];
        }

        public bool FormalRemainsInAction(ActionProc actionProc, Variable param)
        {
            return LocalVariableLayerRange(param).Contains(actionProc.upperLayer) &&
                   !actionProc.hiddenFormals.Contains(param);
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

        private class ActionVisitor : ReadOnlyVisitor
        {
            private CivlTypeChecker ctc;
            private Action action;

            public ActionVisitor(CivlTypeChecker ctc)
            {
                this.ctc = ctc;
            }

            internal void VisitAction(Action action)
            {
                this.action = action;
                foreach(var g in action.gate)
                {
                    VisitAssertCmd(g);
                }
                VisitImplementation(action.impl);
            }

            public override Procedure VisitProcedure(Procedure node)
            {
                // This visitor only has to check the body of action specifications
                return node;
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                if (node.Decl is GlobalVariable)
                {
                    var sharedVarLayerRange = ctc.GlobalVariableLayerRange(node.Decl);
                    if (!action.layerRange.Subset(sharedVarLayerRange) || 
                        (sharedVarLayerRange.lowerLayerNum == action.layerRange.lowerLayerNum && 
                         action is AtomicAction))
                    // a shared variable introduced at layer n is visible to an atomic action only at layer n+1 or higher
                    // thus, a shared variable with layer range [n,n] is not accessible by an atomic action
                    // however, an introduction action may access the shared variable at layer n
                    {
                        ctc.checkingContext.Error(node, "Shared variable {0} is not available in action specification", node.Decl.Name);
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

        private class LemmaProcedureVisitor : ReadOnlyVisitor
        {
            private CivlTypeChecker ctc;

            public LemmaProcedureVisitor(CivlTypeChecker civlTypeChecker)
            {
                this.ctc = civlTypeChecker;
            }

            public override Cmd VisitCallCmd(CallCmd callCmd)
            {
                if (!ctc.procToLemmaProc.ContainsKey(callCmd.Proc))
                {
                    ctc.Error(callCmd, "Lemma procedure can only call a lemma procedure");
                    return callCmd;
                }
                return base.VisitCallCmd(callCmd);
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                if (node.Decl is GlobalVariable)
                {
                    ctc.Error(node, "Global variable is not accessible in lemma procedure");
                }
                return node;
            }
        }

        private class YieldingProcVisitor : ReadOnlyVisitor
        {
            CivlTypeChecker ctc;
            YieldingProc yieldingProc;
            List<IdentifierExpr> globalVariableAccesses;
            List<IdentifierExpr> localVariableAccesses;

            Procedure enclosingProc;
            Implementation enclosingImpl;

            public YieldingProcVisitor(CivlTypeChecker ctc)
            {
                this.ctc = ctc;

                globalVariableAccesses = null;
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
                    if (globalVariableAccesses != null)
                    {
                        globalVariableAccesses.Add(node);
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
                else if (node.Decl is Formal || node.Decl is LocalVariable)
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

            public override Cmd VisitAssumeCmd(AssumeCmd node)
            {
                localVariableAccesses = new List<IdentifierExpr>();
                var cmd = base.VisitAssumeCmd(node);
                var fullLayerRange = new LayerRange(LayerRange.Min, yieldingProc.upperLayer);
                if (!localVariableAccesses.TrueForAll(x => ctc.LocalVariableLayerRange(x.Decl).Equals(fullLayerRange)))
                {
                    ctc.checkingContext.Error(node, "Local variables accessed in assume command must be available at all layers where the enclosing procedure exists");
                }
                localVariableAccesses = null;
                return cmd;
            }

            public override Cmd VisitAssignCmd(AssignCmd node)
            {
                var cmd = base.VisitAssignCmd(node);
                for (int i = 0; i < node.Lhss.Count; i++)
                {
                    var lhs = node.Lhss[i].DeepAssignedVariable;
                    if (lhs is LocalVariable lhsLocalVariable)
                    {
                        var lhsLayerRange = ctc.LocalVariableLayerRange(lhsLocalVariable);
                        localVariableAccesses = new List<IdentifierExpr>();
                        base.Visit(node.Rhss[i]);
                        if (!localVariableAccesses.TrueForAll(x => lhsLayerRange.Subset(ctc.LocalVariableLayerRange(x.Decl))))
                        {
                            ctc.checkingContext.Error(node,
                                "Layer range mismatch at position {0}: local variables accessed in rhs must be available at all layers where the lhs exists", i);
                        }
                        localVariableAccesses = null;
                    }
                }
                return cmd;
            }

            public void VisitSpecPre()
            {
                globalVariableAccesses = new List<IdentifierExpr>();
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
                    foreach (var ie in globalVariableAccesses)
                    {
                        if (!ctc.GlobalVariableLayerRange(ie.Decl).Contains(layer))
                        {
                            ctc.checkingContext.Error(ie, "Global variable {0} is not available at layer {1}", ie.Name, layer);
                        }
                    }
                    foreach (var ie in localVariableAccesses)
                    {
                        if (!ctc.LocalVariableLayerRange(ie.Decl).Contains(layer))
                        {
                            ctc.checkingContext.Error(ie, "Local variable {0} is not available at layer {1}", ie.Name, layer);
                        }
                    }
                }

                globalVariableAccesses = null;
                localVariableAccesses = null;
            }

            public override Cmd VisitCallCmd(CallCmd call)
            {
                YieldingProc callerProc = yieldingProc;

                if (ctc.procToYieldingProc.ContainsKey(call.Proc))
                {
                    VisitYieldingProcCallCmd(call, callerProc, ctc.procToYieldingProc[call.Proc]);
                }
                else if (ctc.procToLemmaProc.ContainsKey(call.Proc))
                {
                    VisitLemmaProcCallCmd(call, callerProc);
                }
                else if (ctc.procToIntroductionAction.ContainsKey(call.Proc))
                {
                    VisitIntroductionActionCallCmd(call, callerProc, ctc.procToIntroductionAction[call.Proc]);
                }
                else
                {
                    ctc.Error(call, 
                        "A yielding procedure can only call yielding procedures, lemma procedures, or introduction actions");
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

                var hiddenFormals = new HashSet<Variable>();
                if (calleeProc is ActionProc actionProc)
                {
                    hiddenFormals = actionProc.hiddenFormals;
                }
                else if (calleeProc is SkipProc skipProc)
                {
                    hiddenFormals = skipProc.hiddenFormals;
                }
                for (int i = 0; i < call.Ins.Count; i++)
                {
                    // Visitor checks for global variable accesses and collects accessed local variables
                    localVariableAccesses = new List<IdentifierExpr>();
                    Visit(call.Ins[i]);

                    var formal = call.Proc.InParams[i];
                    var formalLayerRange = ctc.LocalVariableLayerRange(formal);
                    if (!hiddenFormals.Contains(formal) && calleeProc is ActionProc)
                    {
                        formalLayerRange = new LayerRange(formalLayerRange.lowerLayerNum, callerProc.upperLayer);
                    }
                    foreach (var ie in localVariableAccesses)
                    {
                        var actualLayerRange = ctc.LocalVariableLayerRange(ie.Decl);
                        if (formalLayerRange.Subset(actualLayerRange))
                        {
                            continue;
                        }
                        ctc.checkingContext.Error(ie, "Variable {0} cannot be used to compute the argument for formal parameter {1}", ie.Decl.Name, formal.Name);
                    }

                    localVariableAccesses = null;
                }
                for (int i = 0; i < call.Outs.Count; i++)
                {
                    IdentifierExpr actualIdentifierExpr = call.Outs[i];
                    // Visitor only called to check for global variable accesses
                    Visit(actualIdentifierExpr);

                    var actualLayerRange = ctc.LocalVariableLayerRange(actualIdentifierExpr.Decl);
                    var formal = call.Proc.OutParams[i];
                    var formalLayerRange = ctc.LocalVariableLayerRange(formal);
                    if (!hiddenFormals.Contains(formal) && calleeProc is ActionProc)
                    {
                        formalLayerRange = new LayerRange(formalLayerRange.lowerLayerNum, callerProc.upperLayer);
                    }
                    if (actualLayerRange.Subset(formalLayerRange))
                    {
                        continue;
                    }
                    ctc.Error(actualIdentifierExpr, "Formal return parameter of call available at fewer layers than the corresponding actual parameter");
                }
            }

            private void VisitLemmaProcCallCmd(CallCmd call, YieldingProc callerProc)
            {
                var calledLayers = ctc.FindLayers(call.Attributes);
                if (calledLayers.Count != 1)
                {
                    ctc.checkingContext.Error(call, "Call to lemma procedure must be annotated with a layer");
                }
                else
                {
                    var layerNum = calledLayers[0];
                    globalVariableAccesses = new List<IdentifierExpr>();
                    CheckCallInterface(call, callerProc, layerNum);
                    if (globalVariableAccesses.Any(ie => !ctc.globalVarToLayerRange[ie.Decl].Contains(layerNum)))
                    {
                        ctc.checkingContext.Error(call, "A global variable used in input to the call not available at layer {0}", layerNum);
                    }
                    globalVariableAccesses = null;
                }
            }
            
            private void VisitIntroductionActionCallCmd(CallCmd call, YieldingProc callerProc, IntroductionAction introductionAction)
            {
                if (introductionAction.LayerNum > callerProc.upperLayer)
                {
                    ctc.checkingContext.Error(call,
                        "The layer of the called introduction action must not be greater than the disappearing layer of the callee");
                    return;
                }
                
                CheckCallInterface(call, callerProc, introductionAction.LayerNum);
                
                if (callerProc.upperLayer != introductionAction.LayerNum &&
                    introductionAction.modifiedGlobalVars.Any(v => ctc.GlobalVariableLayerRange(v).upperLayerNum != introductionAction.LayerNum))
                {
                    ctc.checkingContext.Error(call,"All modified variables of callee must be hidden at layer {0}", introductionAction.LayerNum);
                }
            }

            private void CheckCallInterface(CallCmd call, YieldingProc callerProc, int layerNum)
            {
                // check inputs
                {
                    localVariableAccesses = new List<IdentifierExpr>();
                    foreach (var e in call.Ins)
                    {
                        Visit(e);
                    }
                    if (localVariableAccesses.Any(ie => !ctc.localVarToLayerRange[ie.Decl].Contains(layerNum)))
                    {
                        ctc.checkingContext.Error(call, "A local variable used in input to the call not available at layer {0}", layerNum);
                    }
                    localVariableAccesses = null;
                }
                
                // check outputs
                if (call.Outs.Any(ie => ctc.LocalVariableLayerRange(ie.Decl).lowerLayerNum != layerNum))
                {
                    ctc.checkingContext.Error(call, "All output variables must be introduced at layer {0}", layerNum);
                }
                else if (callerProc.upperLayer != layerNum &&
                         call.Outs.Any(ie => ctc.LocalVariableLayerRange(ie.Decl).upperLayerNum != layerNum))
                {
                    ctc.checkingContext.Error(call,"All output variables of call must be hidden at layer {0}", layerNum);
                }
            }
            
            public override Cmd VisitParCallCmd(ParCallCmd parCall)
            {
                bool allLeftMover = true;
                bool allRightMover = true;
                int maxCalleeLayerNum = LayerRange.Min;
                int atomicActionCalleeLayerNum = LayerRange.Min;
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
                        if (atomicActionCalleeLayerNum == LayerRange.Min)
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
                    ctc.Error(parCall, "The parallel call must either have a single arm or all arms are right movers or all arms are left movers");
                }
                if (atomicActionCalleeLayerNum != LayerRange.Min && atomicActionCalleeLayerNum < maxCalleeLayerNum)
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
                                mods = actionProc.RefinedActionAtLayer(caller.upperLayer).modifiedGlobalVars;
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
                        else if (ctc.procToIntroductionAction.ContainsKey(callCmd.Proc))
                        {
                            var introductionAction = ctc.procToIntroductionAction[callCmd.Proc];
                            if (caller.upperLayer == introductionAction.LayerNum)
                            {
                                mods = new HashSet<Variable>(callCmd.Proc.Modifies.Select(ie => ie.Decl));
                            }
                        }
                        else
                        {
                            Debug.Assert(ctc.procToLemmaProc.ContainsKey(callCmd.Proc));
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
