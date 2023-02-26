using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class CivlTypeChecker
  {
    public ConcurrencyOptions Options { get; }
    public CheckingContext checkingContext;
    public Program program;

    // Don't access directly!
    // Use public access methods.
    private Dictionary<Variable, LayerRange> globalVarToLayerRange;
    private Dictionary<Variable, LayerRange> localVarToLayerRange;
    private string namePrefix;

    public Dictionary<Block, YieldingLoop> yieldingLoops;
    public Dictionary<Block, HashSet<int>> cooperatingLoopHeaders;
    public HashSet<Procedure> cooperatingProcedures;

    public Dictionary<Procedure, AtomicAction> procToAtomicAction;
    public Dictionary<Procedure, InvariantAction> procToIsInvariant;
    public Dictionary<Procedure, AtomicAction> procToIsAbstraction;
    public Dictionary<Procedure, YieldingProc> procToYieldingProc;
    public Dictionary<Procedure, LemmaProc> procToLemmaProc;
    public Dictionary<Procedure, IntroductionAction> procToIntroductionAction;
    public Dictionary<Procedure, YieldInvariant> procToYieldInvariant;

    public List<InductiveSequentialization> inductiveSequentializations;

    public Dictionary<Absy, HashSet<int>> absyToLayerNums;
    
    public Dictionary<string, Procedure> pendingAsyncProcs;
    public Dictionary<Implementation, Dictionary<CtorType, Variable>> implToPendingAsyncCollector;
    
    // These collections are for convenience in later phases and are only initialized at the end of type checking.
    public List<int> allRefinementLayers;
    public IEnumerable<Variable> GlobalVariables => globalVarToLayerRange.Keys;
    
    public LinearTypeChecker linearTypeChecker;

    public AtomicAction SkipAtomicAction;

    public CivlTypeChecker(ConcurrencyOptions options, Program program)
    {
      this.checkingContext = new CheckingContext(null);
      this.program = program;
      this.Options = options;
      this.linearTypeChecker = new LinearTypeChecker(this);

      this.globalVarToLayerRange = new Dictionary<Variable, LayerRange>();
      this.localVarToLayerRange = new Dictionary<Variable, LayerRange>();
      this.yieldingLoops = new Dictionary<Block, YieldingLoop>();
      this.cooperatingLoopHeaders = new Dictionary<Block, HashSet<int>>();
      this.cooperatingProcedures = new HashSet<Procedure>();
      this.absyToLayerNums = new Dictionary<Absy, HashSet<int>>();
      this.procToAtomicAction = new Dictionary<Procedure, AtomicAction>();
      this.procToIsInvariant = new Dictionary<Procedure, InvariantAction>();
      this.procToIsAbstraction = new Dictionary<Procedure, AtomicAction>();
      this.procToYieldingProc = new Dictionary<Procedure, YieldingProc>();
      this.procToLemmaProc = new Dictionary<Procedure, LemmaProc>();
      this.procToIntroductionAction = new Dictionary<Procedure, IntroductionAction>();
      this.procToYieldInvariant = new Dictionary<Procedure, YieldInvariant>();
      this.implToPendingAsyncCollector = new Dictionary<Implementation, Dictionary<CtorType, Variable>>();
      this.inductiveSequentializations = new List<InductiveSequentialization>();

      IEnumerable<string> declNames = program.TopLevelDeclarations.OfType<NamedDeclaration>().Select(x => x.Name);
      IEnumerable<string> localVarNames = VariableNameCollector.Collect(program);
      IEnumerable<string> blockLabels = program.TopLevelDeclarations.OfType<Implementation>()
        .SelectMany(x => x.Blocks.Select(y => y.Label));
      var allNames = declNames.Union(localVarNames).Union(blockLabels);
      namePrefix = "Civl_";
      foreach (var name in allNames)
      {
        while (name.StartsWith(namePrefix))
        {
          namePrefix = namePrefix + "_";
        }
      }

      var skipProcedure = DeclHelper.Procedure(
        AddNamePrefix("Skip"),
        new List<Variable>(),
        new List<Variable>(),
        new List<Requires>(),
        new List<IdentifierExpr>(),
        new List<Ensures>());
      var skipImplementation = DeclHelper.Implementation(
        skipProcedure,
        new List<Variable>(),
        new List<Variable>(),
        new List<Variable>(),
        new List<Block> { BlockHelper.Block("init", new List<Cmd>()) });
      SkipAtomicAction = new AtomicAction(skipProcedure, skipImplementation, LayerRange.MinMax, MoverType.Both, null);
      SkipAtomicAction.CompleteInitialization(this, new List<AsyncAction>());
    }

    public string AddNamePrefix(string name)
    {
      return $"{namePrefix}{name}";
    }
    
    public LocalVariable LocalVariable(string name, Type type)
    {
      return VarHelper.LocalVariable($"{namePrefix}{name}", type);
    }

    public BoundVariable BoundVariable(string name, Type type)
    {
      return VarHelper.BoundVariable($"{namePrefix}{name}", type);
    }

    public Formal Formal(string name, Type type, bool incoming)
    {
      return VarHelper.Formal($"{namePrefix}{name}", type, incoming);
    }
    
    private class VariableNameCollector : ReadOnlyVisitor
    {
      private HashSet<string> localVarNames = new HashSet<string>();

      public static HashSet<string> Collect(Program program)
      {
        var collector = new VariableNameCollector();
        collector.VisitProgram(program);
        return collector.localVarNames;
      }

      public override Variable VisitVariable(Variable node)
      {
        localVarNames.Add(node.Name);
        return node;
      }
    }

    public void TypeCheck()
    {
      linearTypeChecker.TypeCheck();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      
      TypeCheckGlobalVariables();
      TypeCheckLemmaProcedures();
      TypeCheckYieldInvariants();
      TypeCheckActions();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      TypeCheckYieldingProcedureDecls();
      TypeCheckLocalVariables();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      
      TypeCheckYieldingProcedureImpls();
      TypeCheckLoopAnnotations();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      TypeCheckRefinementLayers();
      AttributeEraser.Erase(this);
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      YieldSufficiencyTypeChecker.TypeCheck(this);
    }

    private void TypeCheckRefinementLayers()
    {
      // List of all layers where refinement happens
      var yieldingProcsWithImpls = procToYieldingProc.Keys.Intersect(program.Implementations.Select(i => i.Proc));
      allRefinementLayers = yieldingProcsWithImpls.Select(p => procToYieldingProc[p].upperLayer).OrderBy(l => l)
        .Distinct().ToList();

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

      var allInductiveSequentializationLayers =
        inductiveSequentializations.Select(x => x.invariantAction.layerRange.upperLayerNum).ToList();

      var intersect = allRefinementLayers.Intersect(allInductiveSequentializationLayers).ToList();
      if (intersect.Any())
      {
        checkingContext.Error(Token.NoToken,
          "The following layers mix refinement with IS: " + string.Join(",", intersect));
      }

      foreach (var g in GlobalVariables)
      {
        var layerRange = GlobalVariableLayerRange(g);
        if (allInductiveSequentializationLayers.Contains(layerRange.lowerLayerNum))
        {
          Error(g, $"Global variable {g.Name} cannot be introduced at layer with IS");
        }

        if (allInductiveSequentializationLayers.Contains(layerRange.upperLayerNum))
        {
          Error(g, $"Global variable {g.Name} cannot be hidden at layer with IS");
        }
      }
    }

    private void TypeCheckGlobalVariables()
    {
      foreach (var g in program.GlobalVariables)
      {
        globalVarToLayerRange[g] = ToLayerRange(FindLayers(g.Attributes), g);
      }
    }

    private void TypeCheckCreates(
      Dictionary<Procedure, HashSet<string>> actionProcToCreates, 
      Dictionary<Procedure, LayerRange> actionProcToLayerRange)
    {
      actionProcToCreates.Keys.Iter(proc =>
      {
        actionProcToCreates[proc].Iter(name =>
        {
          if (!pendingAsyncProcs.ContainsKey(name))
          {
            Error(proc,
              $"{name} in creates list of {proc.Name} must be an atomic action with pending_async attribute");
          }
          else
          {
            var pendingAsync = pendingAsyncProcs[name];
            var actionLayerRange = actionProcToLayerRange[proc];
            var pendingAsyncLayerRange = actionProcToLayerRange[pendingAsync];
            if (!actionLayerRange.Subset(pendingAsyncLayerRange))
            {
              Error(proc, $"Pending async {name} is not available on all layers of {proc.Name}");
            }
          }
        });
      }); 
    }
    
    private void TypeCheckIntroductionAction(Procedure proc, LayerRange layerRange)
    {
      if (proc.HasAttribute(CivlAttributes.PENDING_ASYNC))
      {
        Error(proc, "Introduction action may not be a pending async");
      }
      if (proc.HasAttribute(CivlAttributes.CREATES))
      {
        Error(proc, "Introduction action may not create pending asyncs");
      }
      if (proc.Modifies.Any(ie => GlobalVariableLayerRange(ie.Decl).lowerLayerNum != layerRange.lowerLayerNum))
      {
        Error(proc, "Introduction actions can modify a global variable only on its introduction layer");
      }
    }

    private Dictionary<Procedure, Procedure> TypeCheckInvariantAction(Procedure proc,
      Dictionary<Procedure, HashSet<string>> actionProcToCreates,
      Dictionary<string, Procedure> absActionProcs, 
      Dictionary<Procedure, LayerRange> actionProcToLayerRange)
    {
      if (proc.HasAttribute(CivlAttributes.PENDING_ASYNC))
      {
        Error(proc, "Invariant action may not be a pending async");
      }
      var layer = actionProcToLayerRange[proc].upperLayerNum;
      var elimMap = new Dictionary<Procedure, Procedure>();
      var kvs = proc.FindAllAttributes(CivlAttributes.ELIM);
      if (!kvs.All(kv => 1 <= kv.Params.Count && kv.Params.Count <= 2 && kv.Params.All(p => p is string)))
      {
        Error(proc, "An elim attribute expects one or two strings");
        return null;
      }
      if (kvs.Select(kv => (string)kv.Params[0]).Distinct().Count() != kvs.Count)
      {
        Error(proc, "Each elim attribute must be distinct in the first action");
        return null;
      }
      foreach (var kv in kvs)
      {
        var names = kv.Params.OfType<string>().ToList();
        if (!pendingAsyncProcs.ContainsKey(names[0]))
        {
          Error(kv, $"Could not find pending async action {names[0]}");
        }
        if (names.Count == 2 && !absActionProcs.ContainsKey(names[1]))
        {
          Error(kv, $"Could not find atomic action {names[1]}");
        }
      }
      if (checkingContext.ErrorCount > 0)
      {
        return null;
      }
      var invariantModifies = new HashSet<Variable>(proc.Modifies.Select(ie => ie.Decl));
      foreach (var kv in kvs)
      {
        var names = kv.Params.OfType<string>().ToList();
        var actionName = names[0];
        Procedure elimProc = pendingAsyncProcs[actionName];
        if (!actionProcToLayerRange[elimProc].Contains(layer))
        {
          Error(kv, $"Action {actionName} does not exist at layer {layer}");
        }
        Procedure absProc = elimProc;
        if (kv.Params.Count == 2)
        {
          var abstractionName = names[1];
          absProc = absActionProcs[abstractionName];
          if (!actionProcToLayerRange[absProc].Contains(layer))
          {
            Error(kv, $"Action {abstractionName} does not exist at layer {layer}");
          }
        }
        if (!actionProcToCreates[proc].Contains(actionName))
        {
          Error(kv, $"{actionName} must be created by {proc.Name}");
        }
        if (!actionProcToCreates[elimProc].IsSubsetOf(actionProcToCreates[proc]))
        {
          Error(kv, $"each pending async created by {actionName} must also be created by {proc.Name}");
        }
        CheckInductiveSequentializationAbstractionSignature(elimProc, absProc);
        var elimModifies = new HashSet<Variable>(elimProc.Modifies.Select(ie => ie.Decl));
        if (!elimModifies.IsSubsetOf(invariantModifies))
        {
          Error(kv, $"Modifies list of {elimProc.Name} must be subset of modifies list of invariant action {proc.Name}");
        }
        var absModifies = new HashSet<Variable>(absProc.Modifies.Select(ie => ie.Decl));
        if (!absModifies.IsSubsetOf(elimModifies))
        {
          Error(kv, $"Modifies list of {absProc.Name} must be subset of modifies list of {elimProc.Name}");
        }
        elimMap[elimProc] = absProc;
      }
      return elimMap;
    }

    private (Procedure, Procedure) TypeCheckAtomicAction(Procedure proc,
      Dictionary<Procedure, HashSet<string>> actionProcToCreates,
      Dictionary<string, Procedure> invariantActionProcs, 
      Dictionary<Procedure, HashSet<string>> invariantProcToNonElims, 
      Dictionary<string, Procedure> atomicActionProcs, 
      Dictionary<Procedure, LayerRange> actionProcToLayerRange)
    {
      if (actionProcToCreates[proc].Count > 0 &&
          (proc.HasAttribute(CivlAttributes.RIGHT) || proc.HasAttribute(CivlAttributes.BOTH)))
      {
        Error(proc, "Action that creates a pending async cannot be a right mover");
      }
      var attrs = proc.FindAllAttributes(CivlAttributes.IS);
      if (attrs.Count == 0)
      {
        return (null, null);
      }
      if (attrs.Count > 1)
      {
        Error(proc, "Expected no more than one IS attribute");
        return (null, null);
      }
      if (pendingAsyncProcs.ContainsKey(proc.Name))
      {
        Error(proc, "Action transformed by IS cannot be a pending async");
        return (null, null);
      }
      var kv = attrs[0];
      if (!(kv.Params.Count == 2 &&
            kv.Params[0] is string refinedActionName &&
            kv.Params[1] is string invariantActionName))
      {
        Error(proc, "IS attribute expects two strings");
        return (null, null);
      }
      var layer = actionProcToLayerRange[proc].upperLayerNum;
      if (!atomicActionProcs.ContainsKey(refinedActionName))
      {
        Error(kv, $"Could not find refined atomic action {refinedActionName}");
      }
      if (!invariantActionProcs.ContainsKey(invariantActionName))
      {
        Error(kv, $"Could not find invariant action {invariantActionName}");
      }
      if (checkingContext.ErrorCount > 0)
      {
        return (null, null);
      }
      var refinedProc = atomicActionProcs[refinedActionName];
      if (!actionProcToLayerRange[refinedProc].Contains(layer + 1))
      {
        Error(kv, $"IS input does not exist at layer {layer + 1}");
      }
      var invariantProc = invariantActionProcs[invariantActionName];
      if (!actionProcToLayerRange[invariantProc].Contains(layer))
      {
        Error(kv, $"IS invariant does not exist at layer {layer}");
      }
      if (!actionProcToCreates[proc].IsSubsetOf(actionProcToCreates[invariantProc]))
      {
        Error(kv, $"Pending asyncs created by IS input must be subset of those created by invariant action {invariantActionName}");
      }
      if (!actionProcToCreates[refinedProc].SetEquals(invariantProcToNonElims[invariantProc]))
      {
        Error(kv, $"Pending asyncs created by IS output must be the same as those not eliminated by invariant action {invariantActionName}");
      }
      CheckInductiveSequentializationAbstractionSignature(proc, invariantProc);
      CheckInductiveSequentializationAbstractionSignature(proc, refinedProc);
      var procModifies = new HashSet<Variable>(proc.Modifies.Select(ie => ie.Decl));
      var refinedProcModifies = new HashSet<Variable>(refinedProc.Modifies.Select(ie => ie.Decl));
      var invariantProcModifies = new HashSet<Variable>(invariantProc.Modifies.Select(ie => ie.Decl));
      if (!procModifies.IsSubsetOf(invariantProcModifies))
      {
        Error(kv, $"Modifies list of {proc.Name} must be subset of modifies list of invariant action {invariantProc.Name}");
      }
      if (!refinedProcModifies.IsSubsetOf(invariantProcModifies))
      {
        Error(kv, $"Modifies list of {refinedProc.Name} must be subset of modifies list of invariant action {invariantProc.Name}");
      }
      return (refinedProc, invariantProc);
    }

    private void TypeCheckActions()
    {
      // Atomic action:
      // * no {:yield}
      // * {:right}, {:left}, {:both}, {:atomic}, {:intro}, {:IS_invariant}, {:IS_abstraction}, {:creates}
      // * layer range
      var actionProcs = program.Procedures.Where(IsAction).ToHashSet();
      var actionProcToImpl = new Dictionary<Procedure, Implementation>();
      foreach (var impl in program.Implementations)
      {
        if (actionProcToImpl.ContainsKey(impl.Proc))
        {
          Error(impl.Proc, "More then one action specification provided");
          continue;
        }
        if (actionProcs.Contains(impl.Proc))
        {
          actionProcToImpl.Add(impl.Proc, impl);
        }
      }
      var actionProcToLayerRange = new Dictionary<Procedure, LayerRange>();
      foreach (var proc in actionProcs)
      {
        var isIntroductionAction = proc.HasAttribute(CivlAttributes.INTRO) ? 1 : 0;
        var isAtomicAction = GetMoverType(proc) != null ? 1 : 0;
        var isInvariant = proc.HasAttribute(CivlAttributes.IS_INVARIANT) ? 1 : 0;
        var isAbstraction = proc.HasAttribute(CivlAttributes.IS_ABSTRACTION) ? 1 : 0;
        var isPendingAsync = proc.HasAttribute(CivlAttributes.PENDING_ASYNC) ? 1 : 0;
        if (isIntroductionAction + isAtomicAction + isInvariant + isAbstraction > 1)
        {
          Error(proc, "Introduction, invariant, abstraction, and atomic actions are mutually exclusive");
        }
        if (isPendingAsync > 0 && proc.OutParams.Count > 0)
        {
          Error(proc, $"Action declared as pending async cannot have output parameters");
        }
        if (isPendingAsync > 0 && isAtomicAction == 0)
        {
          Error(proc, "Only an atomic action may be a pending async"); 
        }
        if (proc.Requires.Count + proc.Ensures.Count > 0)
        {
          Error(proc, "Action cannot have preconditions or postconditions");
        }
        if (!actionProcToImpl.ContainsKey(proc))
        {
          Error(proc, "Action body missing");
          continue;
        }
        Implementation impl = actionProcToImpl[proc];
        impl.PruneUnreachableBlocks(Options);
        Graph<Block> cfg = Program.GraphFromImpl(impl);
        if (!Graph<Block>.Acyclic(cfg))
        {
          Error(proc, "Action body cannot have loops");
          continue;
        }
        LayerRange layerRange = ToLayerRange(FindLayers(proc.Attributes), proc);
        actionProcToLayerRange.Add(proc, layerRange);
      }

      // Set up useful data structures for the type checking
      pendingAsyncProcs = actionProcs.Where(proc => proc.HasAttribute(CivlAttributes.PENDING_ASYNC))
        .ToDictionary(proc => proc.Name, proc => proc);
      var actionProcToCreates = actionProcs.ToDictionary(proc => proc,
        proc =>
        {
          var createsAttr = proc.FindAttribute(CivlAttributes.CREATES);
          return createsAttr == null ? new HashSet<string>() : createsAttr.Params.OfType<string>().ToHashSet();
        });
      var atomicActionProcs = actionProcs.Where(proc => GetMoverType(proc) != null)
        .ToDictionary(proc => proc.Name, proc => proc);
      var absActionProcs = actionProcs.Where(proc => proc.HasAttribute(CivlAttributes.IS_ABSTRACTION))
        .ToDictionary(proc => proc.Name, proc => proc);
      var invariantActionProcs = actionProcs.Where(proc => proc.HasAttribute(CivlAttributes.IS_INVARIANT))
        .ToDictionary(proc => proc.Name, proc => proc);
      
      // type check creates lists
      TypeCheckCreates(actionProcToCreates, actionProcToLayerRange);
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      
      // type check introduction actions
      actionProcs.Where(proc => proc.HasAttribute(CivlAttributes.INTRO)).Iter(proc =>
      {
        TypeCheckIntroductionAction(proc, actionProcToLayerRange[proc]);
      });
      
      // type check invariant actions and calculate for each invariant action the non-eliminated actions
      var invariantProcToElimMap = new Dictionary<Procedure, Dictionary<Procedure, Procedure>>();
      actionProcs.Where(proc => proc.HasAttribute(CivlAttributes.IS_INVARIANT)).Iter(proc =>
      {
        var elimMap = TypeCheckInvariantAction(proc, actionProcToCreates, absActionProcs, actionProcToLayerRange);
        if (elimMap != null)
        {
          invariantProcToElimMap[proc] = elimMap;
        }
      });
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      var invariantProcToNonElims = invariantProcToElimMap.Keys.ToDictionary(proc => proc,
        proc =>
        {
          var nonElims = new HashSet<string>(actionProcToCreates[proc]);
          nonElims.ExceptWith(invariantProcToElimMap[proc].Keys.Select(x => x.Name));
          return nonElims;
        });
      
      // type check atomic actions
      var actionProcToRefinedProc = new Dictionary<Procedure, Procedure>();
      var actionProcToInvariantProc = new Dictionary<Procedure, Procedure>();
      actionProcs.Where(proc => GetMoverType(proc) != null).Iter(proc =>
      {
        var (refinedProc, invariantProc) = TypeCheckAtomicAction(proc, actionProcToCreates, invariantActionProcs,
          invariantProcToNonElims, atomicActionProcs, actionProcToLayerRange);
        if (refinedProc != null)
        {
          actionProcToRefinedProc[proc] = refinedProc;
          actionProcToInvariantProc[proc] = invariantProc;
        }
      });
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      
      // Type check action bodies
      var actionImplVisitor = new ActionImplVisitor(this, actionProcToLayerRange, actionProcToCreates);
      foreach (var impl in actionProcToImpl.Values)
      {
        actionImplVisitor.VisitImplementation(impl);
      }
      if (!actionImplVisitor.IsCallGraphAcyclic())
      {
        Error(program, "Call graph over atomic actions must be acyclic");
      }
      actionProcs.Iter(proc =>
      {
        if (proc.FindAttribute("inline") != null)
        {
          Error(proc, "unnecessary to provide inline attribute on action");
        }
      });
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      // Inline atomic actions
      CivlUtil.AddInlineAttribute(SkipAtomicAction.proc);
      actionProcs.Iter(proc =>
      {
        CivlUtil.AddInlineAttribute(proc);
      });
      actionProcs.Iter(proc =>
      {
        var impl = actionProcToImpl[proc];
        impl.OriginalBlocks = impl.Blocks;
        impl.OriginalLocVars = impl.LocVars;
      });
      actionProcs.Iter(proc =>
      {
        Inliner.ProcessImplementation(Options, program, actionProcToImpl[proc]);
      });
      actionProcs.Iter(proc =>
      {
        var impl = actionProcToImpl[proc];
        impl.OriginalBlocks = null;
        impl.OriginalLocVars = null;
      });
      
      // Two-step initialization process for actions
      // - First, create all actions.
      // - Second, initialize pendingAsync actions across all actions.
      foreach (var proc in actionProcs.Except(actionProcToRefinedProc.Keys))
      {
        // In this loop, we create all introduction, invariant, and abstraction actions,
        // but only those atomic actions (pending async or otherwise) that do not refine
        // another action.
        Implementation impl = actionProcToImpl[proc];
        LayerRange layerRange = actionProcToLayerRange[proc];
        if (proc.HasAttribute(CivlAttributes.INTRO))
        {
          procToIntroductionAction[proc] = new IntroductionAction(proc, impl, layerRange);
        }
        else if (proc.HasAttribute(CivlAttributes.IS_INVARIANT))
        {
          procToIsInvariant[proc] = new InvariantAction(proc, impl, layerRange);
        }
        else if (proc.HasAttribute(CivlAttributes.IS_ABSTRACTION))
        {
          procToIsAbstraction[proc] = new AtomicAction(proc, impl, layerRange, GetActionMoverType(proc), null);
        }
        else if (proc.HasAttribute(CivlAttributes.PENDING_ASYNC))
        {
          procToAtomicAction[proc] = new AsyncAction(this, proc, impl, layerRange, GetActionMoverType(proc));
        }
        else
        {
          procToAtomicAction[proc] = new AtomicAction(proc, impl, layerRange, GetActionMoverType(proc), null);
        }
      }
      // Now we create all atomic actions that refine other actions via an inductive sequentialization.
      // Earlier type checking guarantees that each such action is not a pending async action.
      // Therefore, only the type AtomicAction will be created now.
      actionProcToRefinedProc.Keys.Iter(proc =>
      {
        CreateActionsThatRefineAnotherAction(proc, actionProcToImpl, actionProcToLayerRange, actionProcToRefinedProc);
      });
      // All actions have been created. Now we initialize their pending asyncs and desugar primitive
      // invocations (for creating pending asyncs and setting choice) inside them. 
      procToIntroductionAction.Keys.Iter(proc =>
      {
        var action = procToIntroductionAction[proc];
        action.CompleteInitialization(this, new List<AsyncAction>());
      });
      procToAtomicAction.Keys.Iter(proc =>
      {
        var action = procToAtomicAction[proc];
        action.CompleteInitialization(this,
          actionProcToCreates[proc].Select(name => FindAtomicAction(name) as AsyncAction));
      });
      procToIsAbstraction.Keys.Iter(proc =>
      {
        var action = procToIsAbstraction[proc];
        action.CompleteInitialization(this,
          actionProcToCreates[proc].Select(name => FindAtomicAction(name) as AsyncAction));
      });
      var invariantProcToInductiveSequentialization = new Dictionary<Procedure, InductiveSequentialization>();
      procToIsInvariant.Keys.Iter(proc =>
      {
        var action = procToIsInvariant[proc];
        action.CompleteInitialization(this,
          actionProcToCreates[proc].Select(name => FindAtomicAction(name) as AsyncAction),
          invariantProcToElimMap[proc].Keys.Select(x => procToAtomicAction[x]).OfType<AsyncAction>());
        action.InitializeInputOutputRelation(this);
        var elimMap = invariantProcToElimMap[proc];
        elimMap.Keys.Iter(proc => procToAtomicAction[proc].InitializeInputOutputRelation(this));
        var elim = elimMap.Keys.ToDictionary(x => (AsyncAction)procToAtomicAction[x],
          x =>
          {
            var absProc = elimMap[x];
            return procToIsAbstraction.ContainsKey(absProc)
              ? procToIsAbstraction[absProc]
              : procToAtomicAction[absProc];
          });
        var inductiveSequentialization = new InductiveSequentialization(this, action, elim);
        inductiveSequentializations.Add(inductiveSequentialization);
        invariantProcToInductiveSequentialization[proc] = inductiveSequentialization;
      });
      actionProcToRefinedProc.Keys.Iter(proc =>
      {
        var action = procToAtomicAction[proc];
        var invariantProc = actionProcToInvariantProc[proc];
        var inductiveSequentialization = invariantProcToInductiveSequentialization[invariantProc];
        inductiveSequentialization.AddTarget(action);
      });
    }

    void CreateActionsThatRefineAnotherAction(Procedure proc, 
      Dictionary<Procedure, Implementation> actionProcToImpl,
      Dictionary<Procedure, LayerRange> actionProcToLayerRange,
      Dictionary<Procedure, Procedure> actionProcToRefinedProc)
    {
      if (procToAtomicAction.ContainsKey(proc))
      {
        return;
      }
      var refinedProc = actionProcToRefinedProc[proc];
      CreateActionsThatRefineAnotherAction(refinedProc, actionProcToImpl, actionProcToLayerRange, actionProcToRefinedProc);
      var refinedAction = procToAtomicAction[refinedProc];
      Implementation impl = actionProcToImpl[proc];
      LayerRange layerRange = actionProcToLayerRange[proc];
      procToAtomicAction[proc] = new AtomicAction(proc, impl, layerRange, GetActionMoverType(proc), refinedAction);
    }

    private void TypeCheckLemmaProcedures()
    {
      // Lemma procedure:
      // * {:lemma}
      // * no {:yields}
      // * no mover type
      // * no layer range
      LemmaProcedureVisitor visitor = new LemmaProcedureVisitor(this);
      foreach (var proc in program.Procedures.Where(IsLemmaProcedure))
      {
        if (proc.Modifies.Count > 0)
        {
          Error(proc, "Lemma procedure cannot modify a global variable");
        }
        else
        {
          procToLemmaProc[proc] = new LemmaProc(proc);
          visitor.VisitProcedure(proc);
        }
      }

      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      foreach (Implementation impl in program.Implementations.Where(impl => procToLemmaProc.ContainsKey(impl.Proc)))
      {
        visitor.VisitImplementation(impl);
      }
    }

    private void TypeCheckYieldInvariants()
    {
      // Yield invariant:
      // * {:yield_invariant}
      // * {:layer n}
      foreach (var proc in program.Procedures.Where(IsYieldInvariant))
      {
        var layers = FindLayers(proc.Attributes);
        if (layers.Count != 1)
        {
          Error(proc, "A yield invariant must be annotated with a single layer");
          continue;
        }

        var visitor = new YieldInvariantVisitor(this, layers[0]);
        visitor.VisitProcedure(proc);
        var yieldInvariant = new YieldInvariant(proc, layers[0]);
        procToYieldInvariant[proc] = yieldInvariant;
        foreach (var param in proc.InParams)
        {
          localVarToLayerRange[param] = new LayerRange(yieldInvariant.LayerNum);
          var linearKind = LinearDomainCollector.FindLinearKind(param);
          if (linearKind == LinearKind.LINEAR_IN || linearKind == LinearKind.LINEAR_OUT)
          {
            Error(param, "Parameter to yield invariant can only be :linear");
          }
        }
      }

      foreach (Implementation impl in program.Implementations.Where(impl => procToYieldInvariant.ContainsKey(impl.Proc))
      )
      {
        Error(impl, "A yield invariant cannot have an implementation");
      }
    }

    private void TypeCheckYieldingPrePostDecls(Procedure proc,
      out List<CallCmd> yieldRequires,
      out List<CallCmd> yieldEnsures)
    {
      yieldRequires = new List<CallCmd>();
      yieldEnsures = new List<CallCmd>();
      
      foreach (var attr in CivlAttributes.FindAllAttributes(proc, CivlAttributes.YIELD_REQUIRES))
      {
        var callCmd = YieldInvariantCallChecker.CheckRequires(this, attr, proc);
        if (callCmd != null)
        {
          yieldRequires.Add(StripOld(callCmd));
        }
      }

      foreach (var attr in CivlAttributes.FindAllAttributes(proc, CivlAttributes.YIELD_ENSURES))
      {
        var callCmd = YieldInvariantCallChecker.CheckEnsures(this, attr, proc);
        if (callCmd != null)
        {
          yieldEnsures.Add(callCmd);
        }
      }

      foreach (var attr in CivlAttributes.FindAllAttributes(proc, CivlAttributes.YIELD_PRESERVES))
      {
        var callCmd = YieldInvariantCallChecker.CheckPreserves(this, attr, proc);
        if (callCmd != null)
        {
          yieldRequires.Add(StripOld(callCmd));
          yieldEnsures.Add(callCmd);
        }
      }
    }

    private static T StripOld<T>(T cmd) where T : Cmd
    {
      var emptySubst = Substituter.SubstitutionFromDictionary(new Dictionary<Variable, Expr>());
      return (T) Substituter.ApplyReplacingOldExprs(emptySubst, emptySubst, cmd);
    }

    private void TypeCheckYieldingProcedureDecls()
    {
      foreach (var proc in program.Procedures.Where(IsYieldingProcedure))
      {
        int upperLayer; // must be initialized by the following code, otherwise it is an error
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

        TypeCheckYieldingPrePostDecls(proc, out var yieldRequires, out var yieldEnsures);

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

          if (proc.Modifies.Count > 0)
          {
            Error(proc, $"Modifies clause must be empty");
            continue;
          }

          var hiddenFormals =
            new HashSet<Variable>(proc.InParams.Concat(proc.OutParams).Where(x => x.HasAttribute(CivlAttributes.HIDE)));
          var actionProc = new ActionProc(proc, refinedAction, upperLayer, hiddenFormals, yieldRequires, yieldEnsures);
          CheckRefinementSignature(actionProc);
          procToYieldingProc[proc] = actionProc;
        }
        else if (moverType.HasValue) // proc is a mover procedure
        {
          if (!proc.Modifies.All(ie => GlobalVariableLayerRange(ie.Decl).Contains(upperLayer)))
          {
            Error(proc,
              $"All variables in the modifies clause of a mover procedure must be available at its disappearing layer");
            continue;
          }

          procToYieldingProc[proc] = new MoverProc(proc, moverType.Value, upperLayer, yieldRequires, yieldEnsures);
        }
        else // proc refines the skip action
        {
          if (proc.Modifies.Count > 0)
          {
            Error(proc, $"Modifies clause must be empty");
            continue;
          }

          if (!procToAtomicAction.ContainsKey(SkipAtomicAction.proc))
          {
            procToAtomicAction[SkipAtomicAction.proc] = SkipAtomicAction;
          }

          var hiddenFormals = new HashSet<Variable>(proc.InParams.Concat(proc.OutParams)
            .Where(x => localVarToLayerRange[x].upperLayerNum == upperLayer));
          var actionProc = new ActionProc(proc, SkipAtomicAction, upperLayer, hiddenFormals, yieldRequires,
            yieldEnsures);
          procToYieldingProc[proc] = actionProc;
        }

        YieldingProcVisitor visitor = new YieldingProcVisitor(this, yieldRequires, yieldEnsures);
        visitor.VisitProcedure(proc);
        if (proc.HasAttribute(CivlAttributes.COOPERATES))
        {
          cooperatingProcedures.Add(proc);
        }
      }

      if (procToAtomicAction.ContainsKey(SkipAtomicAction.proc))
      {
        program.AddTopLevelDeclaration(SkipAtomicAction.proc);
        program.AddTopLevelDeclaration(SkipAtomicAction.impl);
      }
    }

    private void TypeCheckYieldingProcedureImpls()
    {
      foreach (var impl in program.Implementations.Where(impl => procToYieldingProc.ContainsKey(impl.Proc)))
      {
        YieldingProcVisitor visitor = new YieldingProcVisitor(this);
        visitor.VisitImplementation(impl);
      }
    }

    private void TypeCheckLoopAnnotations()
    {
      foreach (var impl in program.Implementations.Where(impl => procToYieldingProc.ContainsKey(impl.Proc)))
      {
        var graph = Program.GraphFromImpl(impl);
        graph.ComputeLoops();
        if (!graph.Reducible)
        {
          Error(impl, "Irreducible flow graphs are unsupported.");
          continue;
        }

        foreach (var header in graph.Headers)
        {
          var yieldingLayers = new HashSet<int>();
          var cooperatingLayers = new HashSet<int>();
          foreach (PredicateCmd predCmd in header.Cmds.TakeWhile(cmd => cmd is PredicateCmd))
          {
            if (predCmd.HasAttribute(CivlAttributes.YIELDS))
            {
              yieldingLayers.UnionWith(absyToLayerNums[predCmd]);
            }

            if (predCmd.HasAttribute(CivlAttributes.COOPERATES))
            {
              cooperatingLayers.UnionWith(absyToLayerNums[predCmd]);
            }
          }

          if (yieldingLayers.Intersect(cooperatingLayers).Count() != 0)
          {
            Error(header, "Loop cannot be both yielding and cooperating on the same layer.");
            continue;
          }

          var yieldInvariants = new List<CallCmd>();
          foreach (PredicateCmd predCmd in header.Cmds.TakeWhile(cmd => cmd is PredicateCmd))
          {
            foreach (var attr in CivlAttributes.FindAllAttributes(predCmd, CivlAttributes.YIELD_LOOP))
            {
              var callCmd = YieldInvariantCallChecker.CheckLoop(this, attr, header);
              if (callCmd == null)
              {
                continue;
              }

              var calleeLayerNum = procToYieldInvariant[callCmd.Proc].LayerNum;
              if (yieldingLayers.Contains(calleeLayerNum))
              {
                yieldInvariants.Add(callCmd);
              }
              else
              {
                Error(attr, $"Loop must yield at layer {calleeLayerNum} of the called yield invariant");
              }
            }
          }

          yieldingLoops[header] = new YieldingLoop(yieldingLayers, yieldInvariants);
          cooperatingLoopHeaders[header] = cooperatingLayers;
        }
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
            
            Type t1 = formals1[i].TypedIdent.Type;
            Type t2 = formals2[i].TypedIdent.Type;
            if (name1 != name2)
            {
              checkingContext.Error(formals1[i], $"mismatched name of {inout}-parameter {name1}: (named {name2} in {decl2.Name})");
            }
            else if (!t1.Equals(t2))
            {
              checkingContext.Error(formals1[i], $"mismatched type of {inout}-parameter {name1} in {decl2.Name}");
            }
            else if (checkLinearity &&
                (QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR) !=
                 QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR) ||
                 QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR_IN) !=
                 QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR_IN) ||
                 QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR_OUT) !=
                 QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR_OUT)))
            {
              checkingContext.Error(formals1[i],
                $"mismatched linearity annotation of {inout}-parameter {name1} in {decl2.Name}");
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
      var actionOutParams = actionProc.refinedAction.proc.OutParams
        .SkipEnd(actionProc.refinedAction.pendingAsyncs.Count).ToList();
      signatureMatcher.MatchFormals(procInParams, actionInParams, SignatureMatcher.IN);
      signatureMatcher.MatchFormals(procOutParams, actionOutParams, SignatureMatcher.OUT);
    }

    private void CheckInductiveSequentializationAbstractionSignature(Procedure original, Procedure abstraction)
    {
      // Input and output parameters have to match exactly
      var signatureMatcher = new SignatureMatcher(original, abstraction, checkingContext);
      signatureMatcher.MatchFormals(original.InParams, abstraction.InParams, SignatureMatcher.IN);
      signatureMatcher.MatchFormals(original.OutParams, abstraction.OutParams, SignatureMatcher.OUT);
    }

    private void TypeCheckLocalVariables()
    {
      var pendingAsyncMultisetTypes = program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>()
        .Where(decl => pendingAsyncProcs.ContainsKey(decl.Name)).Select(decl =>
          TypeHelper.MapType(TypeHelper.CtorType(decl), Type.Int)).ToHashSet();
      foreach (Implementation impl in program.Implementations.Where(i => procToYieldingProc.ContainsKey(i.Proc)))
      {
        // then we collect the layers of local variables in implementations
        implToPendingAsyncCollector[impl] = new Dictionary<CtorType, Variable>();
        foreach (Variable v in impl.LocVars)
        {
          int upperLayer = procToYieldingProc[impl.Proc].upperLayer;
          localVarToLayerRange[v] = FindLocalVariableLayerRange(impl, v, upperLayer);
          var layer = localVarToLayerRange[v].lowerLayerNum;
          if (v.HasAttribute(CivlAttributes.PENDING_ASYNC))
          {
            if (!pendingAsyncMultisetTypes.Contains(v.TypedIdent.Type))
            {
              Error(v, "Pending async collector is of incorrect type");
            }
            else if (layer != upperLayer)
            {
              Error(v,
                "Pending async collector must be introduced at the disappearing layer of the enclosing procedure");
            }
            else
            {
              var mapType = (MapType)v.TypedIdent.Type;
              var ctorType = (CtorType)mapType.Arguments[0];
              if (implToPendingAsyncCollector[impl].ContainsKey(ctorType))
              {
                Error(v, "Duplicate pending async collector");
              }
              else
              {
                implToPendingAsyncCollector[impl][ctorType] = v;
              }
            }
          }
        }

        // and finally just copy the layer information from procedure parameters to their corresponding implementation parameter
        // (i.e., layer declarations are only taken from procedures, not implementations)
        for (int i = 0; i < impl.Proc.InParams.Count; i++)
        {
          Variable v = impl.Proc.InParams[i];
          if (localVarToLayerRange.ContainsKey(v))
          {
            localVarToLayerRange[impl.InParams[i]] = localVarToLayerRange[v];
          }
        }

        for (int i = 0; i < impl.Proc.OutParams.Count; i++)
        {
          Variable v = impl.Proc.OutParams[i];
          if (localVarToLayerRange.ContainsKey(v))
          {
            localVarToLayerRange[impl.OutParams[i]] = localVarToLayerRange[v];
          }
        }
      }

      // Also add parameters of atomic actions to localVarToLayerRange,
      // assigning to them the layer range of the action.
      foreach (var a in procToAtomicAction.Values)
      {
        foreach (var v in a.proc.InParams.Union(a.proc.OutParams).Union(a.impl.InParams).Union(a.impl.OutParams))
        {
          localVarToLayerRange[v] = a.layerRange;
        }
      }
    }

    #region Helpers for attribute parsing

    public bool IsYieldingProcedure(Procedure proc)
    {
      return proc.HasAttribute(CivlAttributes.YIELDS);
    }

    public bool IsAction(Procedure proc)
    {
      return !proc.HasAttribute(CivlAttributes.YIELDS) &&
             (GetMoverType(proc) != null ||
              proc.HasAttribute(CivlAttributes.INTRO) ||
              proc.HasAttribute(CivlAttributes.IS_INVARIANT) ||
              proc.HasAttribute(CivlAttributes.IS_ABSTRACTION));
    }

    public bool IsLemmaProcedure(Procedure proc)
    {
      return !proc.HasAttribute(CivlAttributes.YIELDS) && proc.HasAttribute(CivlAttributes.LEMMA);
    }

    public bool IsYieldInvariant(Procedure proc)
    {
      return proc.HasAttribute(CivlAttributes.YIELD_INVARIANT);
    }

    private MoverType GetActionMoverType(Procedure proc)
    {
      if (proc.HasAttribute(CivlAttributes.IS_INVARIANT) || proc.HasAttribute(CivlAttributes.IS_ABSTRACTION))
      {
        return MoverType.Non;
      }
      else
      {
        return GetMoverType(proc).Value;
      }
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
          {
            x = MoverType.Non;
          }
          else if (kv.Key == CivlAttributes.RIGHT)
          {
            x = MoverType.Right;
          }
          else if (kv.Key == CivlAttributes.LEFT)
          {
            x = MoverType.Left;
          }
          else if (kv.Key == CivlAttributes.BOTH)
          {
            x = MoverType.Both;
          }

          if (x.HasValue)
          {
            if (moverType.HasValue)
            {
              checkingContext.Warning(kv, "Ignoring duplicate mover type declaration ({0})", kv.Key);
            }
            else
            {
              moverType = x;
            }
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
        if (kv.Key != CivlAttributes.LAYER)
        {
          continue;
        }

        foreach (var o in kv.Params)
        {
          var layerNum = TypeCheckLayer(kv, o);
          if (layerNum.HasValue)
          {
            layers.Add(layerNum.Value);
          }
        }
      }

      return layers;
    }

    private int? TypeCheckLayer(QKeyValue kv, object o)
    {
      if (o is LiteralExpr l && l.isBigNum)
      {
        var n = l.asBigNum;
        if (n.IsNegative)
        {
          Error(kv, "Layer must be non-negative");
        }
        else if (!n.InInt32)
        {
          Error(kv, "Layer is too large (max value is Int32.MaxValue)");
        }
        else
        {
          return l.asBigNum.ToIntSafe;
        }
      }
      else
      {
        Error(kv, "Layer must be a non-negative integer");
      }

      return null;
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
        Error(decl,
          "Hidden layer of local variable cannot be greater than the disappearing layer of enclosing procedure");
      }

      return layerRange;
    }

    #endregion

    #region Public access methods

    public bool IsYieldingLoopHeader(Block block, int layerNum)
    {
      if (!yieldingLoops.ContainsKey(block))
      {
        return false;
      }

      return yieldingLoops[block].layers.Contains(layerNum);
    }

    public bool IsCooperatingLoopHeader(Block block, int layerNum)
    {
      if (!cooperatingLoopHeaders.ContainsKey(block))
      {
        return false;
      }

      return cooperatingLoopHeaders[block].Contains(layerNum);
    }

    public bool IsCooperatingProcedure(Procedure proc)
    {
      return cooperatingProcedures.Contains(proc);
    }

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

    public InvariantAction FindIsInvariant(string name)
    {
      return procToIsInvariant.Values.FirstOrDefault(a => a.proc.Name == name);
    }

    public IEnumerable<AtomicAction> AllAtomicActions => procToAtomicAction.Values.Concat(procToIsAbstraction.Values);

    public void Error(Absy node, string message)
    {
      checkingContext.Error(node, message);
    }

    public bool Require(bool condition, Absy node, string message)
    {
      if (!condition)
      {
        Error(node, message);
      }

      return condition;
    }

    #endregion

    private class ActionImplVisitor : ReadOnlyVisitor
    {
      private CivlTypeChecker civlTypeChecker;
      private Dictionary<Procedure, LayerRange> actionProcToLayerRange;
      private Dictionary<Procedure, HashSet<string>> actionProcToCreates;
      private Graph<Procedure> callGraph;
      private Procedure proc;

      public ActionImplVisitor(CivlTypeChecker civlTypeChecker,
        Dictionary<Procedure, LayerRange> actionProcToLayerRange,
        Dictionary<Procedure, HashSet<string>> actionProcToCreates)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.actionProcToLayerRange = actionProcToLayerRange;
        this.actionProcToCreates = actionProcToCreates;
        this.callGraph = new Graph<Procedure>();
      }

      public override Procedure VisitProcedure(Procedure node)
      {
        // This visitor only has to check the body of action specifications
        return node;
      }

      public override Implementation VisitImplementation(Implementation node)
      {
        this.proc = node.Proc;
        return base.VisitImplementation(node);
      }
      
      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        var layerRange = actionProcToLayerRange[proc];
        if (node.Decl is GlobalVariable)
        {
          var globalVarLayerRange = civlTypeChecker.GlobalVariableLayerRange(node.Decl);
          if (!layerRange.Subset(globalVarLayerRange) ||
              globalVarLayerRange.lowerLayerNum == layerRange.lowerLayerNum && !proc.HasAttribute(CivlAttributes.INTRO))
            // a global variable introduced at layer n is visible to an atomic action only at layer n+1 or higher
            // thus, a global variable with layer range [n,n] is not accessible by an atomic action
            // however, an introduction action may access the global variable at layer n
          {
            civlTypeChecker.checkingContext.Error(node, "Global variable {0} is not available in action specification",
              node.Decl.Name);
          }
        }
        return base.VisitIdentifierExpr(node);
      }

      public override Cmd VisitCallCmd(CallCmd node)
      {
        var originalProc = (Procedure)this.civlTypeChecker.program.monomorphizer.GetOriginalDecl(node.Proc);
        if (originalProc.Name == "create_async" ||
            originalProc.Name == "create_asyncs" ||
            originalProc.Name == "create_multi_asyncs" ||
            originalProc.Name == "set_choice")
        {
          var type = civlTypeChecker.program.monomorphizer.GetTypeInstantiation(node.Proc)["T"];
          if (type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
          {
            if (!actionProcToCreates[proc].Contains(datatypeTypeCtorDecl.Name))
            {
              civlTypeChecker.Error(node,
                $"Primitive creates a pending async that is not in the enclosing procedure's creates clause: {datatypeTypeCtorDecl.Name}");
            }
          }
          else
          {
            civlTypeChecker.Error(node, $"Type parameter to primitive call must be instantiated with a pending async type");
          }
        }
        else if (!actionProcToCreates[node.Proc].IsSubsetOf(actionProcToCreates[proc]))
        {
          civlTypeChecker.Error(node, $"Callee creates a pending async that is not in the enclosing procedure's creates clause");
        }
        else if (!actionProcToLayerRange.ContainsKey(node.Proc))
        {
          civlTypeChecker.Error(node, "An atomic action can only call other atomic actions");
        }
        else if (!actionProcToLayerRange[proc].Subset(actionProcToLayerRange[node.Proc]))
        {
          civlTypeChecker.Error(node, "Caller layer range must be subset of callee layer range");
        }
        else if (actionProcToLayerRange[proc].lowerLayerNum == actionProcToLayerRange[node.Proc].lowerLayerNum &&
                 node.Proc.HasAttribute(CivlAttributes.INTRO) && 
                 !proc.HasAttribute(CivlAttributes.INTRO))
        {
          civlTypeChecker.Error(node, "Lower layer of caller must be greater that lower layer of callee");
        }
        else
        {
          callGraph.AddEdge(proc, node.Proc);
        }
        return base.VisitCallCmd(node);
      }

      public bool IsCallGraphAcyclic()
      {
        return Graph<Procedure>.Acyclic(callGraph);
      }
    }
    
    private class LemmaProcedureVisitor : ReadOnlyVisitor
    {
      private CivlTypeChecker civlTypeChecker;

      public LemmaProcedureVisitor(CivlTypeChecker civlTypeChecker)
      {
        this.civlTypeChecker = civlTypeChecker;
      }

      public override Cmd VisitCallCmd(CallCmd callCmd)
      {
        if (!civlTypeChecker.procToLemmaProc.ContainsKey(callCmd.Proc))
        {
          civlTypeChecker.Error(callCmd, "Lemma procedure can only call a lemma procedure");
          return callCmd;
        }

        return base.VisitCallCmd(callCmd);
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        if (node.Decl is GlobalVariable)
        {
          civlTypeChecker.Error(node, "Global variable is not accessible in lemma procedure");
        }

        return node;
      }
    }

    private class YieldInvariantVisitor : ReadOnlyVisitor
    {
      private CivlTypeChecker civlTypeChecker;
      private int layerNum;

      public YieldInvariantVisitor(CivlTypeChecker civlTypeChecker, int layerNum)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.layerNum = layerNum;
      }

      public override Procedure VisitProcedure(Procedure node)
      {
        base.VisitRequiresSeq(node.Requires);
        civlTypeChecker.Require(node.Modifies.Count == 0, node, "Modifies clause of yield invariant must be empty");
        civlTypeChecker.Require(node.Ensures.Count == 0, node, "Postcondition not allowed on a yield invariant");
        return node;
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        if (node.Decl is GlobalVariable)
        {
          civlTypeChecker.Require(civlTypeChecker.GlobalVariableLayerRange(node.Decl).Contains(layerNum),
            node, $"Global variable not available at layer {layerNum}");
        }

        return base.VisitIdentifierExpr(node);
      }
    }

    private class YieldRequiresVisitor : ReadOnlyVisitor
    {
      private CivlTypeChecker civlTypeChecker;
      HashSet<Variable> outs;

      public YieldRequiresVisitor(CivlTypeChecker civlTypeChecker, Procedure proc)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.outs = new HashSet<Variable>(proc.OutParams);
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        if (outs.Contains(node.Decl))
        {
          civlTypeChecker.Error(node, "Output parameter cannot be accessed");
        }

        return base.VisitIdentifierExpr(node);
      }
    }

    class YieldInvariantCallChecker : ReadOnlyVisitor
    {
      private CivlTypeChecker civlTypeChecker;
      private int insideOldExpr;
      private int initialErrorCount;
      private QKeyValue attr;
      private CallCmd callCmd;
      private ISet<Variable> availableLinearVars;

      private bool ShouldAbort => callCmd == null || civlTypeChecker.checkingContext.ErrorCount != initialErrorCount;

      static List<LinearKind> RequiresAvailable = new List<LinearKind> { LinearKind.LINEAR, LinearKind.LINEAR_IN };
      static List<LinearKind> EnsuresAvailable = new List<LinearKind> { LinearKind.LINEAR, LinearKind.LINEAR_OUT };
      static List<LinearKind> PreservesAvailable = new List<LinearKind> { LinearKind.LINEAR };

      private ConcurrencyOptions Options => civlTypeChecker.Options;

      public static CallCmd CheckRequires(CivlTypeChecker civlTypeChecker, QKeyValue attr, Procedure caller)
      {
        var v = new YieldInvariantCallChecker(civlTypeChecker, attr, caller, RequiresAvailable);
        return v.callCmd;
      }

      public static CallCmd CheckEnsures(CivlTypeChecker civlTypeChecker, QKeyValue attr, Procedure caller)
      {
        var v = new YieldInvariantCallChecker(civlTypeChecker, attr, caller, EnsuresAvailable);
        return v.callCmd;
      }

      public static CallCmd CheckPreserves(CivlTypeChecker civlTypeChecker, QKeyValue attr, Procedure caller)
      {
        var v = new YieldInvariantCallChecker(civlTypeChecker, attr, caller, PreservesAvailable);
        return v.callCmd;
      }

      public static CallCmd CheckLoop(CivlTypeChecker civlTypeChecker, QKeyValue attr, Block loopHeader)
      {
        var availableLinearVars = civlTypeChecker.linearTypeChecker.AvailableLinearVars(loopHeader);
        var v = new YieldInvariantCallChecker(civlTypeChecker, attr, availableLinearVars);
        return v.callCmd;
      }

      private YieldInvariantCallChecker(CivlTypeChecker civlTypeChecker, QKeyValue attr, ISet<Variable> availableLinearVars)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.attr = attr;
        this.availableLinearVars = availableLinearVars;
        this.insideOldExpr = 0;
        this.initialErrorCount = civlTypeChecker.checkingContext.ErrorCount;
        this.callCmd = null;

        Check();
      }

      private YieldInvariantCallChecker(CivlTypeChecker civlTypeChecker, QKeyValue attr, Procedure caller, List<LinearKind> kinds)
        : this(civlTypeChecker, attr,
            new HashSet<Variable>(
              caller.InParams.Union(caller.OutParams).Where(p => kinds.Contains(LinearDomainCollector.FindLinearKind(p)))
            )
          ) {}

      private void Check()
      {
        ParseAttribute();
        if (ShouldAbort) { callCmd = null; return; }
        civlTypeChecker.linearTypeChecker.VisitCallCmd(callCmd);
        if (ShouldAbort) { callCmd = null; return; }
        Visit(callCmd);
        if (ShouldAbort) { callCmd = null; return; }
        CheckLinearParameters();
        if (ShouldAbort) { callCmd = null; return; }
      }

      private void ParseAttribute()
      {
        if (attr.Params.Count == 0)
        {
          civlTypeChecker.Error(attr, "A yield invariant name must be provided");
          return;
        }

        if (!(attr.Params[0] is string yieldInvariantProcName))
        {
          civlTypeChecker.Error(attr, $"Illegal yield invariant name: {attr.Params[0]}");
          return;
        }

        var yieldingProc =
          civlTypeChecker.procToYieldInvariant.Keys.FirstOrDefault(proc => proc.Name == yieldInvariantProcName);
        if (yieldingProc == null)
        {
          civlTypeChecker.Error(attr, $"Yield invariant {yieldInvariantProcName} does not exist");
          return;
        }

        var exprs = new List<Expr>();
        for (int i = 1; i < attr.Params.Count; i++)
        {
          if (attr.Params[i] is Expr expr)
          {
            exprs.Add(expr);
          }
          else
          {
            civlTypeChecker.Error(attr, $"Illegal expression: {attr.Params[i]}");
          }
        }

        if (exprs.Count + 1 != attr.Params.Count)
        {
          // Error added in the loop above
          return;
        }

        if (exprs.Count != yieldingProc.InParams.Count)
        {
          civlTypeChecker.Error(attr, $"Incorrect number of arguments to yield invariant {yieldingProc.Name}");
          return;
        }

        callCmd = new CallCmd(attr.tok, yieldingProc.Name, exprs, new List<IdentifierExpr>()) { Proc = yieldingProc };

        if (CivlUtil.ResolveAndTypecheck(Options, callCmd) != 0)
        {
          callCmd = null;
        }
      }

      public override Expr VisitOldExpr(OldExpr node)
      {
        insideOldExpr++;
        base.VisitOldExpr(node);
        insideOldExpr--;
        return node;
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        if (node.Decl is GlobalVariable && insideOldExpr == 0)
        {
          civlTypeChecker.Error(node, "Global variable must be wrapped inside old expression");
        }

        return node;
      }

      private void CheckLinearParameters()
      {
        foreach (var (actual, formal) in callCmd.Ins.Zip(callCmd.Proc.InParams))
        {
          if (LinearDomainCollector.FindLinearKind(formal) != LinearKind.ORDINARY)
          {
            var decl = ((IdentifierExpr) actual).Decl;
            if (!availableLinearVars.Contains(decl))
            {
              civlTypeChecker.Error(actual, "Argument must be available");
            }
          }
        }
      }
    }

    private class YieldingProcVisitor : ReadOnlyVisitor
    {
      CivlTypeChecker civlTypeChecker;
      List<CallCmd> yieldRequires;
      List<CallCmd> yieldEnsures;
      YieldingProc yieldingProc;
      List<IdentifierExpr> globalVariableAccesses;
      List<IdentifierExpr> localVariableAccesses;

      public YieldingProcVisitor(CivlTypeChecker civlTypeChecker)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.yieldRequires = null;
        this.yieldEnsures = null;
        this.yieldingProc = null;
        this.globalVariableAccesses = null;
        this.localVariableAccesses = null;
      }

      public YieldingProcVisitor(CivlTypeChecker civlTypeChecker, List<CallCmd> yieldRequires,
        List<CallCmd> yieldEnsures)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.yieldRequires = yieldRequires;
        this.yieldEnsures = yieldEnsures;
        this.yieldingProc = null;
        this.globalVariableAccesses = null;
        this.localVariableAccesses = null;
      }

      public override Implementation VisitImplementation(Implementation node)
      {
        Debug.Assert(yieldingProc == null);
        yieldingProc = civlTypeChecker.procToYieldingProc[node.Proc];
        var ret = base.VisitImplementation(node);
        if (civlTypeChecker.checkingContext.ErrorCount == 0)
        {
          CheckMoverProcModifiesClause(node);
        }

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

        yieldingProc = civlTypeChecker.procToYieldingProc[node];

        // Visit procedure except for modifies clause
        VisitEnsuresSeq(node.Ensures);
        VisitVariableSeq(node.InParams);
        VisitVariableSeq(node.OutParams);
        VisitRequiresSeq(node.Requires);
        var yieldRequiresVisitor = new YieldRequiresVisitor(civlTypeChecker, node);
        foreach (var callCmd in yieldRequires)
        {
          yieldRequiresVisitor.Visit(callCmd);
          VisitYieldInvariantCallCmd(callCmd, yieldingProc.upperLayer,
            civlTypeChecker.procToYieldInvariant[callCmd.Proc].LayerNum);
        }

        foreach (var callCmd in yieldEnsures)
        {
          VisitYieldInvariantCallCmd(callCmd, yieldingProc.upperLayer,
            civlTypeChecker.procToYieldInvariant[callCmd.Proc].LayerNum);
        }

        yieldingProc = null;
        return node;
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        if (node.Decl is GlobalVariable)
        {
          if (globalVariableAccesses != null)
          {
            globalVariableAccesses.Add(node);
          }
          else
          {
            civlTypeChecker.Error(node, "Global variables cannot be accessed in this context");
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
        if (!localVariableAccesses.TrueForAll(x =>
          civlTypeChecker.LocalVariableLayerRange(x.Decl).Equals(fullLayerRange)))
        {
          civlTypeChecker.checkingContext.Error(node,
            "Local variables accessed in assume command must be available at all layers where the enclosing procedure exists");
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
            var lhsLayerRange = civlTypeChecker.LocalVariableLayerRange(lhsLocalVariable);
            localVariableAccesses = new List<IdentifierExpr>();
            base.Visit(node.Rhss[i]);
            if (!localVariableAccesses.TrueForAll(x =>
              lhsLayerRange.Subset(civlTypeChecker.LocalVariableLayerRange(x.Decl))))
            {
              civlTypeChecker.checkingContext.Error(node,
                $"Variables accessed in the source of assignment to {lhs} must exist at all layers where {lhs} exists");
            }
            localVariableAccesses = null;
          }
        }
        return cmd;
      }

      public override Cmd VisitUnpackCmd(UnpackCmd node)
      {
        var cmd = base.VisitUnpackCmd(node);
        localVariableAccesses = new List<IdentifierExpr>();
        base.Visit(node.Rhs);
        node.UnpackedLhs.Select(ie => ie.Decl).OfType<LocalVariable>().Iter(lhs =>
        {
          var lhsLayerRange = civlTypeChecker.LocalVariableLayerRange(lhs);
          if (!localVariableAccesses.TrueForAll(x =>
                lhsLayerRange.Subset(civlTypeChecker.LocalVariableLayerRange(x.Decl))))
          {
            civlTypeChecker.checkingContext.Error(node,
              $"Variables accessed in the unpacked expression must exist at all layers where {lhs} exists");
          }
        });
        localVariableAccesses = null;
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
        var specLayers = civlTypeChecker.FindLayers(node.Attributes).Distinct().OrderBy(l => l).ToList();
        if (specLayers.Count == 0)
        {
          civlTypeChecker.Error(node, "Specification layer(s) not present");
          return;
        }

        civlTypeChecker.absyToLayerNums[node] = new HashSet<int>(specLayers);

        foreach (var layer in specLayers)
        {
          if (layer > yieldingProc.upperLayer)
          {
            civlTypeChecker.checkingContext.Error(node,
              "Specification layer {0} is greater than enclosing procedure layer {1}", layer, yieldingProc.upperLayer);
          }

          foreach (var ie in globalVariableAccesses)
          {
            if (!civlTypeChecker.GlobalVariableLayerRange(ie.Decl).Contains(layer))
            {
              civlTypeChecker.checkingContext.Error(ie, "Global variable {0} is not available at layer {1}", ie.Name,
                layer);
            }
          }

          foreach (var ie in localVariableAccesses)
          {
            if (!civlTypeChecker.LocalVariableLayerRange(ie.Decl).Contains(layer))
            {
              civlTypeChecker.checkingContext.Error(ie, "Local variable {0} is not available at layer {1}", ie.Name,
                layer);
            }
          }
        }

        globalVariableAccesses = null;
        localVariableAccesses = null;
      }

      public override Cmd VisitParCallCmd(ParCallCmd node)
      {
        Require(node.CallCmds.Count(callCmd => callCmd.HasAttribute(CivlAttributes.REFINES)) <= 1, node,
          "At most one arm of a parallel call can refine the specification action");
        
        HashSet<Variable> parallelCallInvars = new HashSet<Variable>();
        foreach (CallCmd callCmd in node.CallCmds.Where(callCmd => !civlTypeChecker.procToYieldInvariant.ContainsKey(callCmd.Proc)))
        {
          for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
          {
            if (LinearDomainCollector.FindLinearKind(callCmd.Proc.InParams[i]) == LinearKind.ORDINARY)
            {
              continue;
            }
            IdentifierExpr actual = callCmd.Ins[i] as IdentifierExpr;
            if (parallelCallInvars.Contains(actual.Decl))
            {
              civlTypeChecker.Error(node,
                $"Linear variable {actual.Decl.Name} can occur only once as an input parameter of a parallel call");
            }
            else
            {
              parallelCallInvars.Add(actual.Decl);
            }
          }
        }

        foreach (CallCmd callCmd in node.CallCmds.Where(callCmd => civlTypeChecker.procToYieldInvariant.ContainsKey(callCmd.Proc)))
        {
          for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
          {
            if (LinearDomainCollector.FindLinearKind(callCmd.Proc.InParams[i]) == LinearKind.ORDINARY)
            {
              continue;
            }
            IdentifierExpr actual = callCmd.Ins[i] as IdentifierExpr;
            if (parallelCallInvars.Contains(actual.Decl))
            {
              civlTypeChecker.Error(node,
                $"Linear variable {actual.Decl.Name} cannot be an input parameter to both a yield invariant and a procedure in a parallel call");
            }
          }
        }
        
        return base.VisitParCallCmd(node);
      }

      public override Cmd VisitCallCmd(CallCmd call)
      {
        YieldingProc callerProc = yieldingProc;

        if (civlTypeChecker.procToYieldingProc.ContainsKey(call.Proc))
        {
          VisitYieldingProcCallCmd(call, callerProc, civlTypeChecker.procToYieldingProc[call.Proc]);
        }
        else if (civlTypeChecker.procToYieldInvariant.ContainsKey(call.Proc))
        {
          VisitYieldInvariantCallCmd(call, callerProc.upperLayer,
            civlTypeChecker.procToYieldInvariant[call.Proc].LayerNum);
        }
        else if (civlTypeChecker.procToLemmaProc.ContainsKey(call.Proc))
        {
          VisitLemmaProcCallCmd(call, callerProc.upperLayer);
        }
        else if (civlTypeChecker.procToIntroductionAction.ContainsKey(call.Proc))
        {
          VisitIntroductionActionCallCmd(call, callerProc.upperLayer,
            civlTypeChecker.procToIntroductionAction[call.Proc]);
        }
        else
        {
          civlTypeChecker.Error(call,
            "A yielding procedure can only call yielding procedures, lemma procedures, or introduction actions");
        }

        return call;
      }

      private bool Require(bool condition, Absy absy, string errorMessage)
      {
        return civlTypeChecker.Require(condition, absy, errorMessage);
      }

      private void VisitYieldingProcCallCmd(CallCmd call, YieldingProc callerProc, YieldingProc calleeProc)
      {
        if (callerProc.upperLayer < calleeProc.upperLayer)
        {
          civlTypeChecker.Error(call, "This call cannot have a callee with higher layer than the caller");
          return;
        }

        if (calleeProc is ActionProc calleeActionProc)
        {
          if (call.IsAsync)
          {
            if (call.HasAttribute(CivlAttributes.SYNC))
            {
              Require(callerProc.upperLayer > calleeProc.upperLayer, call,
                "Called procedure in synchronized call must disappear at lower layer than caller");
              Require(calleeProc.IsLeftMover, call, "Synchronized call must be a left mover");
            }
            else
            {
              Require(callerProc is ActionProc, call, "Caller must be an action procedure");
              var highestRefinedAction = calleeActionProc.RefinedActionAtLayer(callerProc.upperLayer + 1);
              if (highestRefinedAction == null)
              {
                civlTypeChecker.Error(call, $"Called action is not available at layer {callerProc.upperLayer + 1}");
              }
              else if (highestRefinedAction != civlTypeChecker.SkipAtomicAction)
              {
                Require(highestRefinedAction is AsyncAction, call,
                  $"No pending-async constructor available for the atomic action {highestRefinedAction.proc.Name}");
              }
            }
          }

          if (callerProc.upperLayer > calleeProc.upperLayer)
          {
            var highestRefinedAction = calleeActionProc.RefinedActionAtLayer(callerProc.upperLayer);
            if (highestRefinedAction == null)
            {
              civlTypeChecker.Error(call, $"Called action is not available at layer {callerProc.upperLayer}");
            }
            else if (highestRefinedAction.HasPendingAsyncs)
            {
              Require(callerProc is ActionProc, call, "Caller must be an action procedure");
            }
          }
          else // callerProc.upperLayer == calleeProc.upperLayer
          {
            Require(callerProc is ActionProc, call, "Caller must be an action procedure");
            ActionProc callerActionProc = (ActionProc) callerProc;
            Require(call.IsAsync || calleeActionProc.refinedAction.gate.Count == 0, call,
              "Atomic action refined by callee may not have a gate");
            HashSet<string> calleeOutputs = new HashSet<string>(call.Outs.Select(ie => ie.Decl.Name));
            HashSet<string> visibleCallerOutputsAtDisappearingLayer = new HashSet<string>(callerActionProc
              .proc.OutParams.Where(x => !callerActionProc.hiddenFormals.Contains(x))
              .Select(x => x.Name));
            Require(
              visibleCallerOutputsAtDisappearingLayer.IsSubsetOf(calleeOutputs) ||
              !visibleCallerOutputsAtDisappearingLayer.Overlaps(calleeOutputs), call,
              $"Visible outputs of caller at disappearing layer must be either included in or disjoint from call outputs");
          }
        }
        else if (calleeProc is MoverProc)
        {
          Require(callerProc.upperLayer == calleeProc.upperLayer, call,
            "The layer of the caller must be equal to the layer of the callee");
          if (call.IsAsync)
          {
            Require(call.HasAttribute(CivlAttributes.SYNC), call, "Async call to mover procedure must be synchronized");
            Require(calleeProc.IsLeftMover, call, "Synchronized call must be a left mover");
          }
        }
        else
        {
          Debug.Assert(false);
        }

        var hiddenFormals = new HashSet<Variable>();
        if (calleeProc is ActionProc actionProc)
        {
          hiddenFormals = actionProc.hiddenFormals;
        }

        for (int i = 0; i < call.Ins.Count; i++)
        {
          // Visitor checks for global variable accesses and collects accessed local variables
          localVariableAccesses = new List<IdentifierExpr>();
          Visit(call.Ins[i]);

          var formal = call.Proc.InParams[i];
          var formalLayerRange = civlTypeChecker.LocalVariableLayerRange(formal);
          if (!hiddenFormals.Contains(formal) && calleeProc is ActionProc)
          {
            formalLayerRange = new LayerRange(formalLayerRange.lowerLayerNum, callerProc.upperLayer);
          }

          foreach (var ie in localVariableAccesses)
          {
            var actualLayerRange = civlTypeChecker.LocalVariableLayerRange(ie.Decl);
            if (formalLayerRange.Subset(actualLayerRange))
            {
              continue;
            }

            civlTypeChecker.checkingContext.Error(ie,
              "Variable {0} cannot be used to compute the argument for formal parameter {1}", ie.Decl.Name,
              formal.Name);
          }

          localVariableAccesses = null;
        }

        for (int i = 0; i < call.Outs.Count; i++)
        {
          IdentifierExpr actualIdentifierExpr = call.Outs[i];
          // Visitor only called to check for global variable accesses
          Visit(actualIdentifierExpr);

          var actualLayerRange = civlTypeChecker.LocalVariableLayerRange(actualIdentifierExpr.Decl);
          var formal = call.Proc.OutParams[i];
          var formalLayerRange = civlTypeChecker.LocalVariableLayerRange(formal);
          if (!hiddenFormals.Contains(formal) && calleeProc is ActionProc)
          {
            formalLayerRange = new LayerRange(formalLayerRange.lowerLayerNum, callerProc.upperLayer);
          }

          if (actualLayerRange.Subset(formalLayerRange))
          {
            continue;
          }

          civlTypeChecker.Error(actualIdentifierExpr,
            "Formal return parameter of call available at fewer layers than the corresponding actual parameter");
        }
      }

      private void VisitYieldInvariantCallCmd(CallCmd call, int callerProcUpperLayer, int calleeLayerNum)
      {
        Require(calleeLayerNum <= callerProcUpperLayer, call,
          "The layer of the callee must be no more than the disappearing layer of the caller");
        CheckCallInputs(call, calleeLayerNum);
      }

      private void VisitLemmaProcCallCmd(CallCmd call, int callerProcUpperLayer)
      {
        var calledLayers = civlTypeChecker.FindLayers(call.Attributes);
        if (calledLayers.Count != 1)
        {
          civlTypeChecker.checkingContext.Error(call, "Call to lemma procedure must be annotated with a layer");
          return;
        }

        var layerNum = calledLayers[0];
        VisitYieldInvariantCallCmd(call, callerProcUpperLayer, layerNum);
        CheckCallOutputs(call, callerProcUpperLayer, layerNum);
      }

      private void VisitIntroductionActionCallCmd(CallCmd call, int callerProcUpperLayer,
        IntroductionAction introductionAction)
      {
        var calleeLayerNum = introductionAction.LayerNum;
        VisitYieldInvariantCallCmd(call, callerProcUpperLayer, calleeLayerNum);
        CheckCallOutputs(call, callerProcUpperLayer, calleeLayerNum);
        Require(callerProcUpperLayer == calleeLayerNum ||
                introductionAction.modifiedGlobalVars.All(v =>
                  civlTypeChecker.GlobalVariableLayerRange(v).upperLayerNum == calleeLayerNum),
          call, $"All modified variables of callee must be hidden at layer {calleeLayerNum}");
      }

      private void CheckCallInputs(CallCmd call, int calleeLayerNum)
      {
        globalVariableAccesses = new List<IdentifierExpr>();
        localVariableAccesses = new List<IdentifierExpr>();
        foreach (var e in call.Ins)
        {
          Visit(e);
        }

        Require(
          globalVariableAccesses.All(ie => civlTypeChecker.globalVarToLayerRange[ie.Decl].Contains(calleeLayerNum)),
          call,
          $"A global variable used in input to the call not available at layer {calleeLayerNum}");
        Require(localVariableAccesses.All(ie => civlTypeChecker.localVarToLayerRange[ie.Decl].Contains(calleeLayerNum)),
          call,
          $"A local variable used in input to the call not available at layer {calleeLayerNum}");
        localVariableAccesses = null;
        globalVariableAccesses = null;
      }

      private void CheckCallOutputs(CallCmd call, int callerProcUpperLayer, int calleeLayerNum)
      {
        Require(call.Outs.All(ie => civlTypeChecker.LocalVariableLayerRange(ie.Decl).lowerLayerNum == calleeLayerNum),
          call,
          $"All output variables must be introduced at layer {calleeLayerNum}");
        Require(callerProcUpperLayer == calleeLayerNum ||
                call.Outs.All(ie => civlTypeChecker.LocalVariableLayerRange(ie.Decl).upperLayerNum == calleeLayerNum),
          call, $"All output variables of call must be hidden at layer {calleeLayerNum}");
      }

      private void CheckMoverProcModifiesClause(Implementation impl)
      {
        if (yieldingProc is MoverProc caller)
        {
          foreach (var callCmd in impl.Blocks.SelectMany(b => b.Cmds).OfType<CallCmd>())
          {
            IEnumerable<Variable> mods = Enumerable.Empty<Variable>();
            if (civlTypeChecker.procToYieldingProc.TryGetValue(callCmd.Proc, out YieldingProc callee))
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
                Debug.Assert(false);
              }
            }
            else if (civlTypeChecker.procToIntroductionAction.ContainsKey(callCmd.Proc))
            {
              var introductionAction = civlTypeChecker.procToIntroductionAction[callCmd.Proc];
              if (caller.upperLayer == introductionAction.LayerNum)
              {
                mods = new HashSet<Variable>(callCmd.Proc.Modifies.Select(ie => ie.Decl));
              }
            }
            else
            {
              Debug.Assert(civlTypeChecker.procToYieldInvariant.ContainsKey(callCmd.Proc) ||
                           civlTypeChecker.procToLemmaProc.ContainsKey(callCmd.Proc));
            }

            foreach (var mod in mods)
            {
              if (!caller.modifiedGlobalVars.Contains(mod))
              {
                civlTypeChecker.Error(callCmd,
                  $"Modified variable {mod.Name} does not appear in modifies clause of mover procedure");
              }
            }
          }
        }
      }
    }

    private class AttributeEraser : ReadOnlyVisitor
    {
      public static void Erase(CivlTypeChecker civlTypeChecker)
      {
        var attributeEraser = new AttributeEraser();
        attributeEraser.VisitProgram(civlTypeChecker.program);
        foreach (var action in civlTypeChecker.AllAtomicActions)
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
