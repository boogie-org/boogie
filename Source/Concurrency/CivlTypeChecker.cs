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
    private string namePrefix;

    public Dictionary<Block, YieldingLoop> yieldingLoops;

    public Dictionary<ActionDecl, AtomicAction> procToAtomicAction;
    private Dictionary<ActionDecl, InvariantAction> procToInvariantAction;
    public Dictionary<Procedure, YieldingProc> procToYieldingProc;

    public List<InductiveSequentialization> inductiveSequentializations;

    public Dictionary<Implementation, Dictionary<CtorType, Variable>> implToPendingAsyncCollector;
    
    // These collections are for convenience in later phases and are only initialized at the end of type checking.
    public List<int> allRefinementLayers;
    public IEnumerable<Variable> GlobalVariables => program.GlobalVariables;
    
    public LinearTypeChecker linearTypeChecker;

    public AtomicAction SkipAtomicAction;

    public CivlTypeChecker(ConcurrencyOptions options, Program program)
    {
      this.checkingContext = new CheckingContext(null);
      this.program = program;
      this.Options = options;
      this.linearTypeChecker = new LinearTypeChecker(this);

      this.yieldingLoops = new Dictionary<Block, YieldingLoop>();
      this.procToAtomicAction = new Dictionary<ActionDecl, AtomicAction>();
      this.procToInvariantAction = new Dictionary<ActionDecl, InvariantAction>();
      this.procToYieldingProc = new Dictionary<Procedure, YieldingProc>();
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

      var skipProcedure = new ActionDecl(Token.NoToken, AddNamePrefix("Skip"), MoverType.Both, ActionQualifier.None,
        new List<Variable>(), new List<Variable>(), new List<ActionDeclRef>(), null, null, new List<ElimDecl>(),
        new List<IdentifierExpr>(), null, null);
      skipProcedure.LayerRange = LayerRange.MinMax;
      var skipImplementation = DeclHelper.Implementation(
        skipProcedure,
        new List<Variable>(),
        new List<Variable>(),
        new List<Variable>(),
        new List<Block> { BlockHelper.Block("init", new List<Cmd>()) });
      SkipAtomicAction = new AtomicAction(skipImplementation, null, this);
      SkipAtomicAction.CompleteInitialization(this);
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
      allRefinementLayers = yieldingProcsWithImpls.Select(p => procToYieldingProc[p].Layer).OrderBy(l => l)
        .Distinct().ToList();

      var allInductiveSequentializationLayers =
        inductiveSequentializations.Select(x => x.invariantAction.LayerRange.upperLayerNum).ToList();

      var intersect = allRefinementLayers.Intersect(allInductiveSequentializationLayers).ToList();
      if (intersect.Any())
      {
        checkingContext.Error(Token.NoToken,
          "The following layers mix refinement with IS: " + string.Join(",", intersect));
      }

      foreach (var g in GlobalVariables)
      {
        var layerRange = g.layerRange;
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

    private void TypeCheckCreates(HashSet<ActionDecl> actionProcs)
    {
      actionProcs.Iter(proc =>
      {
        proc.Creates.Iter(actionDeclRef =>
        {
          var pendingAsync = actionDeclRef.ActionDecl;
          var actionLayerRange = proc.LayerRange;
          var pendingAsyncLayerRange = pendingAsync.LayerRange;
          if (!actionLayerRange.Subset(pendingAsyncLayerRange))
          {
            Error(proc, $"Pending async {pendingAsync.Name} is not available on all layers of {proc.Name}");
          }
        });
      }); 
    }
    
    private void TypeCheckLinkAction(ActionDecl proc)
    {
      if (proc.Modifies.Any(ie => ie.Decl.layerRange.lowerLayerNum != proc.LayerRange.lowerLayerNum))
      {
        Error(proc, "Link actions can modify a global variable only on its lower layer");
      }
    }

    private void TypeCheckActionRefinement(ActionDecl proc)
    {
      var layer = proc.LayerRange.upperLayerNum;
      var refinedProc = proc.RefinedAction.ActionDecl;
      if (!refinedProc.LayerRange.Contains(layer + 1))
      {
        Error(refinedProc, $"Refined action does not exist at layer {layer + 1}");
      }
      var invariantProc = proc.InvariantAction.ActionDecl;
      if (!invariantProc.LayerRange.Contains(layer))
      {
        Error(invariantProc, $"Invariant action does not exist at layer {layer}");
      }
      CheckInductiveSequentializationAbstractionSignature(proc, invariantProc);
      CheckInductiveSequentializationAbstractionSignature(proc, refinedProc);
      foreach (var elimDecl in proc.Eliminates)
      {
        var elimProc = elimDecl.Target.ActionDecl;
        if (!elimProc.LayerRange.Contains(layer))
        {
          Error(elimDecl, $"Action {elimProc.Name} does not exist at layer {layer}");
        }
        var absProc = elimDecl.Abstraction.ActionDecl;
        if (!absProc.LayerRange.Contains(layer))
        {
          Error(elimDecl, $"Action {absProc.Name} does not exist at layer {layer}");
        }
        CheckInductiveSequentializationAbstractionSignature(elimProc, absProc);
      }
    }

    private void TypeCheckActions()
    {
      var actionProcs = program.Procedures.OfType<ActionDecl>().ToHashSet();

      // type check creates lists
      TypeCheckCreates(actionProcs);
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      
      // type check link actions
      actionProcs.Where(proc => proc.ActionQualifier == ActionQualifier.Link).Iter(proc =>
      {
        TypeCheckLinkAction(proc);
      });

      // type check action refinements
      actionProcs.Where(proc => proc.RefinedAction != null).Iter(proc =>
      {
        TypeCheckActionRefinement(proc);
      });
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      
      // Type check action bodies
      var actionImplVisitor = new ActionImplVisitor(this);
      foreach (var proc in actionProcs)
      {
        actionImplVisitor.VisitImplementation(proc.Impl);
      }
      if (!actionImplVisitor.IsCallGraphAcyclic())
      {
        Error(program, "Call graph over atomic actions must be acyclic");
      }
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      // Four-step initialization process for actions:
      // First, initialize all action decls so that all the pending async machinery is set up.
      // Second, create all actions which also desugars set_choice and variations of create_async.
      // Third, inline actions. This step must be done after the desugaring.
      // Fourth, construct the transition and input-output relation for all actions.
      
      // Initialize ActionDecls
      actionProcs.Iter(proc => proc.Initialize(program.monomorphizer));
      
      // Create all actions
      foreach (var proc in actionProcs.Where(proc => proc.RefinedAction == null))
      {
        // In this loop, we create all link, invariant, and abstraction actions,
        // but only those atomic actions (pending async or otherwise) that do not refine
        // another action.
        Implementation impl = proc.Impl;
        if (proc.ActionQualifier == ActionQualifier.Link)
        {
          procToAtomicAction[proc] = new AtomicAction(impl, null, this);
        }
        else if (proc.ActionQualifier == ActionQualifier.Invariant)
        {
          procToInvariantAction[proc] = new InvariantAction(impl, this);
        }
        else if (proc.ActionQualifier == ActionQualifier.Abstract)
        {
          procToAtomicAction[proc] = new AtomicAction(impl, null, this);
        }
        else if (proc.ActionQualifier == ActionQualifier.Async)
        {
          procToAtomicAction[proc] = new AtomicAction(impl, null, this);
        }
        else
        {
          procToAtomicAction[proc] = new AtomicAction(impl, null, this);
        }
      }
      // Now we create all atomic actions that refine other actions via an inductive sequentialization.
      // Earlier type checking guarantees that each such action is not a pending async action.
      // Therefore, only the type AtomicAction will be created now.
      actionProcs.Where(proc => proc.RefinedAction != null).Iter(proc =>
      {
        CreateActionsThatRefineAnotherAction(proc);
      });

      // Inline atomic actions
      CivlUtil.AddInlineAttribute(SkipAtomicAction.ActionDecl);
      actionProcs.Iter(proc =>
      {
        CivlAttributes.RemoveAttributes(proc, new HashSet<string> { "inline" });
        CivlUtil.AddInlineAttribute(proc);
      });
      actionProcs.Iter(proc =>
      {
        var impl = proc.Impl;
        impl.OriginalBlocks = impl.Blocks;
        impl.OriginalLocVars = impl.LocVars;
      });
      actionProcs.Iter(proc =>
      {
        Inliner.ProcessImplementation(Options, program, proc.Impl);
      });
      actionProcs.Iter(proc =>
      {
        var impl = proc.Impl;
        impl.OriginalBlocks = null;
        impl.OriginalLocVars = null;
      });
      
      // Construct transition and input-output relation.
      procToAtomicAction.Values.Iter(action =>
      {
        action.CompleteInitialization(this, true);
      });
      procToInvariantAction.Values.Iter(action =>
      {
        action.CompleteInitialization(this, true);
      });
      
      // Construct inductive sequentializations
      actionProcs.Where(proc => proc.RefinedAction != null).Iter(proc =>
      {
        var action = procToAtomicAction[proc];
        var invariantProc = proc.InvariantAction.ActionDecl;
        var invariantAction = procToInvariantAction[invariantProc];
        var elim = new Dictionary<AtomicAction, AtomicAction>(proc.EliminationMap().Select(x =>
          KeyValuePair.Create(procToAtomicAction[x.Key], procToAtomicAction[x.Value])));
        inductiveSequentializations.Add(new InductiveSequentialization(this, action, invariantAction, elim));
      });
    }

    void CreateActionsThatRefineAnotherAction(ActionDecl proc)
    {
      if (procToAtomicAction.ContainsKey(proc))
      {
        return;
      }
      var refinedProc = proc.RefinedAction.ActionDecl;
      CreateActionsThatRefineAnotherAction(refinedProc);
      var refinedAction = procToAtomicAction[refinedProc];
      Implementation impl = proc.Impl;
      LayerRange layerRange = proc.LayerRange;
      procToAtomicAction[proc] = new AtomicAction(impl, refinedAction, this);
    }

    private void TypeCheckYieldInvariants()
    {
      foreach (var yieldInvariant in program.TopLevelDeclarations.OfType<YieldInvariantDecl>())
      {
        var visitor = new YieldInvariantVisitor(this, yieldInvariant.Layer);
        visitor.VisitProcedure(yieldInvariant);
        foreach (var param in yieldInvariant.InParams)
        {
          var linearKind = LinearDomainCollector.FindLinearKind(param);
          if (linearKind == LinearKind.LINEAR_IN || linearKind == LinearKind.LINEAR_OUT)
          {
            Error(param, "Parameter to yield invariant can only be :linear");
          }
        }
      }
    }

    private void TypeCheckYieldingPrePostDecls(YieldProcedureDecl proc,
      out List<CallCmd> yieldRequires,
      out List<CallCmd> yieldEnsures)
    {
      yieldRequires = new List<CallCmd>();
      yieldEnsures = new List<CallCmd>();
      
      foreach (var callCmd in proc.YieldRequires)
      {
        if (YieldInvariantCallChecker.CheckRequires(this, callCmd, proc))
        {
          yieldRequires.Add(StripOld(callCmd));
        }
      }

      foreach (var callCmd in proc.YieldEnsures)
      {
        if (YieldInvariantCallChecker.CheckEnsures(this, callCmd, proc))
        {
          yieldEnsures.Add(callCmd);
        }
      }

      foreach (var callCmd in proc.YieldPreserves)
      {
        if (YieldInvariantCallChecker.CheckPreserves(this, callCmd, proc))
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
      foreach (var proc in program.Procedures.OfType<YieldProcedureDecl>())
      {
        int upperLayer = proc.Layer;
        MoverType moverType = proc.MoverType;

        TypeCheckYieldingPrePostDecls(proc, out var yieldRequires, out var yieldEnsures);

        if (proc.RefinedAction != null) // proc is an action procedure
        {
          AtomicAction refinedAction = procToAtomicAction[proc.RefinedAction.ActionDecl];
          if (!refinedAction.LayerRange.Contains(upperLayer + 1))
          {
            checkingContext.Error(proc, "Refined atomic action must be available at layer {0}", upperLayer + 1);
            continue;
          }
          var hiddenFormals =
            new HashSet<Variable>(proc.InParams.Concat(proc.OutParams).Where(x => x.HasAttribute(CivlAttributes.HIDE)));
          var actionProc = new ActionProc(proc, refinedAction, hiddenFormals, yieldRequires, yieldEnsures);
          CheckRefinementSignature(actionProc);
          procToYieldingProc[proc] = actionProc;
        }
        else if (moverType != MoverType.None) // proc is a mover procedure
        {
          if (!proc.Modifies.All(ie => ie.Decl.layerRange.Contains(upperLayer)))
          {
            Error(proc,
              $"All variables in the modifies clause of a mover procedure must be available at its disappearing layer");
            continue;
          }
          procToYieldingProc[proc] = new MoverProc(proc, yieldRequires, yieldEnsures);
        }
        else // proc refines the skip action
        {
          if (!procToAtomicAction.ContainsKey(SkipAtomicAction.ActionDecl))
          {
            procToAtomicAction[SkipAtomicAction.ActionDecl] = SkipAtomicAction;
          }
          var hiddenFormals = new HashSet<Variable>(proc.InParams.Concat(proc.OutParams)
            .Where(x => x.layerRange.upperLayerNum == upperLayer));
          var actionProc = new ActionProc(proc, SkipAtomicAction, hiddenFormals, yieldRequires, yieldEnsures);
          procToYieldingProc[proc] = actionProc;
        }

        YieldingProcVisitor visitor = new YieldingProcVisitor(this, yieldRequires, yieldEnsures);
        visitor.VisitProcedure(proc);
      }

      if (procToAtomicAction.ContainsKey(SkipAtomicAction.ActionDecl))
      {
        program.AddTopLevelDeclaration(SkipAtomicAction.ActionDecl);
        program.AddTopLevelDeclaration(SkipAtomicAction.Impl);
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
          int yieldingLayer = procToYieldingProc[impl.Proc].Layer;
          var yieldCmd = (PredicateCmd)header.Cmds.FirstOrDefault(cmd =>
            cmd is PredicateCmd predCmd && predCmd.HasAttribute(CivlAttributes.YIELDS));
          if (yieldCmd == null)
          {
            yieldingLayer = int.MinValue;
          }
          else
          {
            var layers = yieldCmd.Layers;
            header.Cmds.Remove(yieldCmd);
            if (layers.Any())
            {
              if (layers.Count > 1)
              {
                Error(header, "Expected layer attribute to indicate the highest yielding layer of this loop");
                continue;
              }
              if (layers[0] > yieldingLayer)
              {
                Error(header,
                  "Yielding layer of loop must not be more than the disappearing layer of enclosing procedure");
                continue;
              }
              yieldingLayer = layers[0];
            }
          }
          var yieldInvariants = header.Cmds
            .TakeWhile(cmd => cmd is CallCmd callCmd && callCmd.Proc is YieldInvariantDecl).OfType<CallCmd>()
            .ToList();
          header.Cmds.RemoveRange(0, yieldInvariants.Count);
          if (yieldInvariants.Any() && yieldCmd == null)
          {
            Error(header, "Expected :yields attribute on this loop");
          }
          foreach (var callCmd in yieldInvariants.Where(callCmd => YieldInvariantCallChecker.CheckLoop(this, callCmd, header)))
          {
            var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
            var calleeLayerNum = yieldInvariant.Layer;
            if (calleeLayerNum > yieldingLayer)
            {
              Error(callCmd, $"Loop must yield at layer {calleeLayerNum} of the called yield invariant");
            }
          }
          yieldingLoops[header] = new YieldingLoop(yieldingLayer, yieldInvariants);

          foreach (PredicateCmd predCmd in header.Cmds.TakeWhile(cmd => cmd is PredicateCmd))
          {
            if (predCmd.Layers.Min() <= yieldingLayer &&
                VariableCollector.Collect(predCmd, true).OfType<GlobalVariable>().Any())
            {
              Error(predCmd,
                "This invariant may not access a global variable since one of its layers is a yielding layer of its loop");
            }
          }
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
      var signatureMatcher = new SignatureMatcher(actionProc.Proc, actionProc.RefinedAction.ActionDecl, checkingContext);
      Func<Variable, bool> isRemainingVariable = x =>
        x.layerRange.upperLayerNum == actionProc.Layer &&
        !actionProc.HiddenFormals.Contains(x);
      var procInParams = actionProc.Proc.InParams.Where(isRemainingVariable).ToList();
      var procOutParams = actionProc.Proc.OutParams.Where(isRemainingVariable).ToList();
      var actionInParams = actionProc.RefinedAction.ActionDecl.InParams;
      var actionOutParams = actionProc.RefinedAction.ActionDecl.OutParams
        .SkipEnd(actionProc.RefinedAction.PendingAsyncs.Count).ToList();
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
      var pendingAsyncProcs = program.TopLevelDeclarations.OfType<ActionDecl>()
        .Where(proc => proc.ActionQualifier == ActionQualifier.Async).Select(proc => proc.Name).ToHashSet();
      var pendingAsyncMultisetTypes = program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>()
        .Where(decl => pendingAsyncProcs.Contains(decl.Name)).Select(decl =>
          TypeHelper.MapType(TypeHelper.CtorType(decl), Type.Int)).ToHashSet();
      foreach (Implementation impl in program.Implementations.Where(i => procToYieldingProc.ContainsKey(i.Proc)))
      {
        // then we collect the layers of local variables in implementations
        implToPendingAsyncCollector[impl] = new Dictionary<CtorType, Variable>();
        foreach (Variable v in impl.LocVars)
        {
          int upperLayer = procToYieldingProc[impl.Proc].Layer;
          var layer = v.layerRange.lowerLayerNum;
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
          impl.InParams[i].layerRange = impl.Proc.InParams[i].layerRange;
        }

        for (int i = 0; i < impl.Proc.OutParams.Count; i++)
        {
          impl.OutParams[i].layerRange = impl.Proc.OutParams[i].layerRange;
        }
      }

      // Also copy the layer range of each action to its parameters
      foreach (var a in procToAtomicAction.Values)
      {
        foreach (var v in a.ActionDecl.InParams.Union(a.ActionDecl.OutParams).Union(a.Impl.InParams).Union(a.Impl.OutParams))
        {
          v.layerRange = a.LayerRange;
        }
      }
    }

    #region Public access methods

    public bool IsYieldingLoopHeader(Block block, int layerNum)
    {
      if (!yieldingLoops.ContainsKey(block))
      {
        return false;
      }
      return layerNum <= yieldingLoops[block].Layer;
    }

    public bool FormalRemainsInAction(ActionProc actionProc, Variable param)
    {
      return param.layerRange.Contains(actionProc.Layer) && !actionProc.HiddenFormals.Contains(param);
    }

    public IEnumerable<AtomicAction> LinkActions =>
      procToAtomicAction.Values.Where(action => action.ActionDecl.ActionQualifier == ActionQualifier.Link);

    public IEnumerable<AtomicAction> MoverActions => procToAtomicAction.Values.Where(action =>
      action.ActionDecl.ActionQualifier != ActionQualifier.Abstract && action.ActionDecl.ActionQualifier != ActionQualifier.Link);

    public IEnumerable<AtomicAction> AtomicActions => procToAtomicAction.Values;

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
      private Graph<Procedure> callGraph;
      private ActionDecl proc;

      public ActionImplVisitor(CivlTypeChecker civlTypeChecker)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.callGraph = new Graph<Procedure>();
      }

      public override Procedure VisitProcedure(Procedure node)
      {
        // This visitor only has to check the body of action specifications
        return node;
      }

      public override Implementation VisitImplementation(Implementation node)
      {
        this.proc = (ActionDecl)node.Proc;
        return base.VisitImplementation(node);
      }
      
      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        var layerRange = proc.LayerRange;
        if (node.Decl is GlobalVariable)
        {
          var globalVarLayerRange = node.Decl.layerRange;
          if (!layerRange.Subset(globalVarLayerRange) ||
              globalVarLayerRange.lowerLayerNum == layerRange.lowerLayerNum && proc.ActionQualifier != ActionQualifier.Link)
            // a global variable introduced at layer n is visible to an atomic action only at layer n+1 or higher
            // thus, a global variable with layer range [n,n] is not accessible by an atomic action
            // however, a link action may access the global variable at layer n
          {
            civlTypeChecker.checkingContext.Error(node, "Global variable {0} is not available in action specification",
              node.Decl.Name);
          }
        }
        return base.VisitIdentifierExpr(node);
      }

      public override Cmd VisitCallCmd(CallCmd node)
      {
        if (node.Proc is ActionDecl actionDecl)
        {
          if (!proc.LayerRange.Subset(actionDecl.LayerRange))
          {
            civlTypeChecker.Error(node, "Caller layer range must be subset of callee layer range");
          }
          else if (proc.LayerRange.lowerLayerNum == actionDecl.LayerRange.lowerLayerNum &&
                   actionDecl.ActionQualifier == ActionQualifier.Link &&
                   proc.ActionQualifier != ActionQualifier.Link)
          {
            civlTypeChecker.Error(node, "Lower layer of caller must be greater that lower layer of callee");
          }
          else
          {
            callGraph.AddEdge(proc, node.Proc);
          }
        }
        return base.VisitCallCmd(node);
      }

      public bool IsCallGraphAcyclic()
      {
        return Graph<Procedure>.Acyclic(callGraph);
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
        return node;
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        if (node.Decl is GlobalVariable)
        {
          civlTypeChecker.Require(node.Decl.layerRange.Contains(layerNum),
            node, $"Global variable not available at layer {layerNum}");
        }

        return base.VisitIdentifierExpr(node);
      }
    }

    class YieldInvariantCallChecker : ReadOnlyVisitor
    {
      private CivlTypeChecker civlTypeChecker;
      private int insideOldExpr;
      private int initialErrorCount;
      private CallCmd callCmd;
      private ISet<Variable> availableLinearVars;

      private bool ShouldAbort => civlTypeChecker.checkingContext.ErrorCount != initialErrorCount;

      static List<LinearKind> RequiresAvailable = new List<LinearKind> { LinearKind.LINEAR, LinearKind.LINEAR_IN };
      static List<LinearKind> EnsuresAvailable = new List<LinearKind> { LinearKind.LINEAR, LinearKind.LINEAR_OUT };
      static List<LinearKind> PreservesAvailable = new List<LinearKind> { LinearKind.LINEAR };

      private ConcurrencyOptions Options => civlTypeChecker.Options;

      public static bool CheckRequires(CivlTypeChecker civlTypeChecker, CallCmd callCmd, Procedure caller)
      {
        var v = new YieldInvariantCallChecker(civlTypeChecker, callCmd, caller, RequiresAvailable);
        return !v.ShouldAbort;
      }

      public static bool CheckEnsures(CivlTypeChecker civlTypeChecker, CallCmd callCmd, Procedure caller)
      {
        var v = new YieldInvariantCallChecker(civlTypeChecker, callCmd, caller, EnsuresAvailable);
        return !v.ShouldAbort;
      }

      public static bool CheckPreserves(CivlTypeChecker civlTypeChecker, CallCmd callCmd, Procedure caller)
      {
        var v = new YieldInvariantCallChecker(civlTypeChecker, callCmd, caller, PreservesAvailable);
        return !v.ShouldAbort;
      }

      public static bool CheckLoop(CivlTypeChecker civlTypeChecker, CallCmd callCmd, Block loopHeader)
      {
        var availableLinearVars = civlTypeChecker.linearTypeChecker.AvailableLinearVars(loopHeader);
        var v = new YieldInvariantCallChecker(civlTypeChecker, callCmd, availableLinearVars);
        return !v.ShouldAbort;
      }

      private YieldInvariantCallChecker(CivlTypeChecker civlTypeChecker, CallCmd callCmd, ISet<Variable> availableLinearVars)
      {
        this.civlTypeChecker = civlTypeChecker;
        this.callCmd = callCmd;
        this.availableLinearVars = availableLinearVars;
        this.insideOldExpr = 0;
        this.initialErrorCount = civlTypeChecker.checkingContext.ErrorCount;
        Check();
      }

      private YieldInvariantCallChecker(CivlTypeChecker civlTypeChecker, CallCmd callCmd, Procedure caller, List<LinearKind> kinds)
        : this(civlTypeChecker, callCmd,
            new HashSet<Variable>(
              caller.InParams.Union(caller.OutParams).Where(p => kinds.Contains(LinearDomainCollector.FindLinearKind(p)))
            )
          ) {}

      private void Check()
      {
        civlTypeChecker.linearTypeChecker.VisitCallCmd(callCmd);
        if (ShouldAbort) { return; }
        Visit(callCmd);
        if (ShouldAbort) { return; }
        CheckLinearParameters();
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

      public YieldingProcVisitor(CivlTypeChecker civlTypeChecker, List<CallCmd> yieldRequires, List<CallCmd> yieldEnsures)
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
        foreach (var callCmd in yieldRequires)
        {
          VisitYieldInvariantCallCmd(callCmd, yieldingProc.Layer,
            ((YieldInvariantDecl)callCmd.Proc).Layer);
        }

        foreach (var callCmd in yieldEnsures)
        {
          VisitYieldInvariantCallCmd(callCmd, yieldingProc.Layer,
            ((YieldInvariantDecl)callCmd.Proc).Layer);
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
        if (!(yieldingProc is MoverProc && ensures.Layers.All(x => x == yieldingProc.Layer)))
        {
          CheckAccessToGlobalVariables(ensures);
        }
        return ensures;
      }

      public override Requires VisitRequires(Requires requires)
      {
        VisitSpecPre();
        base.VisitRequires(requires);
        VisitSpecPost(requires);
        if (!(yieldingProc is MoverProc && requires.Layers.All(x => x == yieldingProc.Layer)))
        {
          CheckAccessToGlobalVariables(requires);
        }
        return requires;
      }

      private void CheckAccessToGlobalVariables(Absy absy)
      {
        if (VariableCollector.Collect(absy, true).OfType<GlobalVariable>().Any())
        {
          civlTypeChecker.Error(absy,
            "This specification may not access a global variable since one of its layers is a yielding layer of its procedure");
        }
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
        var fullLayerRange = new LayerRange(LayerRange.Min, yieldingProc.Layer);
        if (!localVariableAccesses.TrueForAll(x => x.Decl.layerRange.Equals(fullLayerRange)))
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
            var lhsLayerRange = lhsLocalVariable.layerRange;
            localVariableAccesses = new List<IdentifierExpr>();
            base.Visit(node.Rhss[i]);
            if (!localVariableAccesses.TrueForAll(x => lhsLayerRange.Subset(x.Decl.layerRange)))
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
          var lhsLayerRange = lhs.layerRange;
          if (!localVariableAccesses.TrueForAll(x => lhsLayerRange.Subset(x.Decl.layerRange)))
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
        if (node.HasAttribute(CivlAttributes.YIELDS))
        {
          return;
        }
        var specLayers = node.FindLayers();
        if (specLayers.Count == 0)
        {
          civlTypeChecker.Error(node, "Specification layer(s) not present");
          return;
        }

        foreach (var layer in specLayers)
        {
          if (layer > yieldingProc.Layer)
          {
            civlTypeChecker.checkingContext.Error(node,
              "Specification layer {0} is greater than enclosing procedure layer {1}", layer, yieldingProc.Layer);
          }

          foreach (var ie in globalVariableAccesses)
          {
            if (!ie.Decl.layerRange.Contains(layer))
            {
              civlTypeChecker.checkingContext.Error(ie, "Global variable {0} is not available at layer {1}", ie.Name,
                layer);
            }
          }

          foreach (var ie in localVariableAccesses)
          {
            if (!ie.Decl.layerRange.Contains(layer))
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
        Require(node.CallCmds.Count(CivlAttributes.IsCallMarked) <= 1, node,
          "At most one arm of a parallel call can refine the specification action");
        
        HashSet<Variable> parallelCallInvars = new HashSet<Variable>();
        foreach (CallCmd callCmd in node.CallCmds.Where(callCmd => callCmd.Proc is not YieldInvariantDecl))
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

        foreach (CallCmd callCmd in node.CallCmds.Where(callCmd => callCmd.Proc is YieldInvariantDecl))
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
        else if (call.Proc is YieldInvariantDecl yieldInvariant)
        {
          VisitYieldInvariantCallCmd(call, callerProc.Layer, yieldInvariant.Layer);
        }
        else if (call.Proc.IsPure)
        {
          VisitPureProcCallCmd(call, callerProc.Layer);
        }
        else if (call.Proc is ActionDecl { ActionQualifier: ActionQualifier.Link } actionDecl)
        {
          VisitLinkActionCallCmd(call, callerProc.Layer, civlTypeChecker.procToAtomicAction[actionDecl]);
        }
        else
        {
          Debug.Assert(false);
        }
        return call;
      }

      private bool Require(bool condition, Absy absy, string errorMessage)
      {
        return civlTypeChecker.Require(condition, absy, errorMessage);
      }

      private void VisitYieldingProcCallCmd(CallCmd call, YieldingProc callerProc, YieldingProc calleeProc)
      {
        if (callerProc.Layer < calleeProc.Layer)
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
              Require(callerProc.Layer > calleeProc.Layer, call,
                "Called procedure in synchronized call must disappear at lower layer than caller");
              Require(calleeProc.IsLeftMover, call, "Synchronized call must be a left mover");
            }
            else
            {
              Require(callerProc is ActionProc, call, "Caller must be an action procedure");
              var highestRefinedAction = calleeActionProc.RefinedActionAtLayer(callerProc.Layer + 1);
              if (highestRefinedAction == null)
              {
                civlTypeChecker.Error(call, $"Called action is not available at layer {callerProc.Layer + 1}");
              }
              else if (highestRefinedAction != civlTypeChecker.SkipAtomicAction)
              {
                Require(highestRefinedAction.ActionDecl.ActionQualifier == ActionQualifier.Async, call,
                  $"No pending-async constructor available for the atomic action {highestRefinedAction.ActionDecl.Name}");
              }
            }
          }

          if (callerProc.Layer > calleeProc.Layer)
          {
            var highestRefinedAction = calleeActionProc.RefinedActionAtLayer(callerProc.Layer);
            if (highestRefinedAction == null)
            {
              civlTypeChecker.Error(call, $"Called action is not available at layer {callerProc.Layer}");
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
            Require(call.IsAsync || calleeActionProc.RefinedAction.Gate.Count == 0, call,
              "Atomic action refined by callee may not have a gate");
            HashSet<string> calleeOutputs = new HashSet<string>(call.Outs.Select(ie => ie.Decl.Name));
            HashSet<string> visibleCallerOutputsAtDisappearingLayer = new HashSet<string>(callerActionProc
              .Proc.OutParams.Where(x => !callerActionProc.HiddenFormals.Contains(x))
              .Select(x => x.Name));
            Require(
              visibleCallerOutputsAtDisappearingLayer.IsSubsetOf(calleeOutputs) ||
              !visibleCallerOutputsAtDisappearingLayer.Overlaps(calleeOutputs), call,
              $"Visible outputs of caller at disappearing layer must be either included in or disjoint from call outputs");
          }
        }
        else if (calleeProc is MoverProc)
        {
          Require(callerProc.Layer == calleeProc.Layer, call,
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
          hiddenFormals = actionProc.HiddenFormals;
        }

        for (int i = 0; i < call.Ins.Count; i++)
        {
          // Visitor checks for global variable accesses and collects accessed local variables
          localVariableAccesses = new List<IdentifierExpr>();
          Visit(call.Ins[i]);

          var formal = call.Proc.InParams[i];
          var formalLayerRange = formal.layerRange;
          if (!hiddenFormals.Contains(formal) && calleeProc is ActionProc)
          {
            formalLayerRange = new LayerRange(formalLayerRange.lowerLayerNum, callerProc.Layer);
          }

          foreach (var ie in localVariableAccesses)
          {
            var actualLayerRange = ie.Decl.layerRange;
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

          var actualLayerRange = actualIdentifierExpr.Decl.layerRange;
          var formal = call.Proc.OutParams[i];
          var formalLayerRange = formal.layerRange;
          if (!hiddenFormals.Contains(formal) && calleeProc is ActionProc)
          {
            formalLayerRange = new LayerRange(formalLayerRange.lowerLayerNum, callerProc.Layer);
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

      private void VisitPureProcCallCmd(CallCmd call, int callerProcUpperLayer)
      {
        var calledLayers = call.Layers;
        if (calledLayers.Count != 1)
        {
          civlTypeChecker.checkingContext.Error(call, "Call to pure procedure must be annotated with a layer");
          return;
        }
        var layerNum = calledLayers[0];
        VisitYieldInvariantCallCmd(call, callerProcUpperLayer, layerNum);
        CheckCallOutputs(call, callerProcUpperLayer, layerNum);
      }

      private void VisitLinkActionCallCmd(CallCmd call, int callerProcUpperLayer, AtomicAction linkAction)
      {
        var calleeLayerNum = linkAction.LowerLayer;
        VisitYieldInvariantCallCmd(call, callerProcUpperLayer, calleeLayerNum);
        CheckCallOutputs(call, callerProcUpperLayer, calleeLayerNum);
        Require(callerProcUpperLayer == calleeLayerNum ||
                linkAction.ModifiedGlobalVars.All(v => v.layerRange.upperLayerNum == calleeLayerNum),
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
          globalVariableAccesses.All(ie => ie.Decl.layerRange.Contains(calleeLayerNum)),
          call,
          $"A global variable used in input to the call not available at layer {calleeLayerNum}");
        Require(localVariableAccesses.All(ie => ie.Decl.layerRange.Contains(calleeLayerNum)),
          call,
          $"A local variable used in input to the call not available at layer {calleeLayerNum}");
        localVariableAccesses = null;
        globalVariableAccesses = null;
      }

      private void CheckCallOutputs(CallCmd call, int callerProcUpperLayer, int calleeLayerNum)
      {
        Require(call.Outs.All(ie => ie.Decl.layerRange.lowerLayerNum == calleeLayerNum),
          call,
          $"All output variables must be introduced at layer {calleeLayerNum}");
        Require(callerProcUpperLayer == calleeLayerNum ||
                call.Outs.All(ie => ie.Decl.layerRange.upperLayerNum == calleeLayerNum),
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
                mods = actionProc.RefinedActionAtLayer(caller.Layer).ModifiedGlobalVars;
              }
              else if (callee is MoverProc moverProc)
              {
                mods = moverProc.ModifiedGlobalVars;
              }
              else
              {
                Debug.Assert(false);
              }
            }
            else if (callCmd.Proc is ActionDecl { ActionQualifier: ActionQualifier.Link } actionDecl)
            {
              var linkAction = civlTypeChecker.procToAtomicAction[actionDecl];
              if (caller.Layer == linkAction.LowerLayer)
              {
                mods = new HashSet<Variable>(callCmd.Proc.Modifies.Select(ie => ie.Decl));
              }
            }
            else
            {
              Debug.Assert(callCmd.Proc is YieldInvariantDecl || callCmd.Proc.IsPure);
            }

            foreach (var mod in mods)
            {
              if (!caller.ModifiedGlobalVars.Contains(mod))
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
        foreach (var action in civlTypeChecker.AtomicActions)
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
        Visit(action.FirstImpl);
        Visit(action.SecondImpl);
      }
    }
  }
}
