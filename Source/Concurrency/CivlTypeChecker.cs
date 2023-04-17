using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class CivlTypeChecker
  {
    public ConcurrencyOptions Options { get; }
    public CheckingContext checkingContext;
    public Program program;
    public LinearTypeChecker linearTypeChecker;
    public List<int> allRefinementLayers;
    public AtomicAction SkipAtomicAction;

    public Dictionary<Block, YieldingLoop> yieldingLoops;
    public Dictionary<ActionDecl, AtomicAction> procToAtomicAction;
    private Dictionary<ActionDecl, InvariantAction> procToInvariantAction;
    public Dictionary<Procedure, YieldingProc> procToYieldingProc;
    public List<InductiveSequentialization> inductiveSequentializations;
    public Dictionary<Implementation, Dictionary<CtorType, Variable>> implToPendingAsyncCollector;
    
    private string namePrefix;

    public IEnumerable<Variable> GlobalVariables => program.GlobalVariables;

    public CivlTypeChecker(ConcurrencyOptions options, Program program)
    {
      this.checkingContext = new CheckingContext(null);
      this.program = program;
      this.Options = options;
      this.linearTypeChecker = new LinearTypeChecker(this);
      this.allRefinementLayers = program.TopLevelDeclarations.OfType<Implementation>()
        .Where(impl => impl.Proc is YieldProcedureDecl)
        .Select(decl => ((YieldProcedureDecl)decl.Proc).Layer)
        .OrderBy(layer => layer).Distinct().ToList();

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
      var skipImplementation = DeclHelper.Implementation(
        skipProcedure,
        new List<Variable>(),
        new List<Variable>(),
        new List<Variable>(),
        new List<Block> { BlockHelper.Block("init", new List<Cmd>()) });
      skipProcedure.LayerRange = LayerRange.MinMax;
      skipProcedure.Impl = skipImplementation;
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
      
      TypeCheckActions();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      TypeCheckYieldingProcedureDecls();
      TypeCheckLocalPendingAsyncCollectors();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      
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
      var allInductiveSequentializationLayers =
        inductiveSequentializations.Select(x => x.invariantAction.LayerRange.UpperLayer).ToList();
      var intersect = allRefinementLayers.Intersect(allInductiveSequentializationLayers).ToList();
      if (intersect.Any())
      {
        checkingContext.Error(Token.NoToken,
          $"procedure refinement and action refinement layers must be disjoint but the following layers mix the two: {string.Join(",", intersect)}");
      }
      foreach (var g in GlobalVariables)
      {
        var layerRange = g.LayerRange;
        if (allInductiveSequentializationLayers.Contains(layerRange.LowerLayer))
        {
          Error(g, $"global variable {g.Name} cannot be introduced at action refinement layer");
        }
        if (allInductiveSequentializationLayers.Contains(layerRange.UpperLayer))
        {
          Error(g, $"global variable {g.Name} cannot be hidden at action refinement layer");
        }
      }
    }

    private void TypeCheckActionRefinement(ActionDecl proc)
    {
      var refinedProc = proc.RefinedAction.ActionDecl;
      var invariantProc = proc.InvariantAction.ActionDecl;
      CheckInductiveSequentializationAbstractionSignature(proc, invariantProc);
      CheckInductiveSequentializationAbstractionSignature(proc, refinedProc);
      foreach (var elimDecl in proc.Eliminates)
      {
        var targetProc = elimDecl.Target.ActionDecl;
        var absProc = elimDecl.Abstraction.ActionDecl;
        CheckInductiveSequentializationAbstractionSignature(targetProc, absProc);
      }
    }

    private void TypeCheckActions()
    {
      var actionDecls = program.Procedures.OfType<ActionDecl>().ToHashSet();
      var callGraph = new Graph<Procedure>();
      foreach (var actionDecl in actionDecls)
      {
        foreach (var block in actionDecl.Impl.Blocks)
        {
          foreach (var callCmd in block.Cmds.OfType<CallCmd>())
          {
            callGraph.AddEdge(actionDecl, callCmd.Proc);
          }
        }
      }
      if (!Graph<Procedure>.Acyclic(callGraph))
      {
        Error(program, "call graph over atomic actions must be acyclic");
      }
      actionDecls.Where(proc => proc.RefinedAction != null).Iter(TypeCheckActionRefinement);
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
      actionDecls.Iter(proc => proc.Initialize(program.monomorphizer));
      
      // Create all actions
      foreach (var proc in actionDecls.Where(proc => proc.RefinedAction == null))
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
      actionDecls.Where(proc => proc.RefinedAction != null).Iter(proc =>
      {
        CreateActionsThatRefineAnotherAction(proc);
      });

      // Inline atomic actions
      CivlUtil.AddInlineAttribute(SkipAtomicAction.ActionDecl);
      actionDecls.Iter(proc =>
      {
        CivlAttributes.RemoveAttributes(proc, new HashSet<string> { "inline" });
        CivlUtil.AddInlineAttribute(proc);
      });
      actionDecls.Iter(proc =>
      {
        var impl = proc.Impl;
        impl.OriginalBlocks = impl.Blocks;
        impl.OriginalLocVars = impl.LocVars;
      });
      actionDecls.Iter(proc =>
      {
        Inliner.ProcessImplementation(Options, program, proc.Impl);
      });
      actionDecls.Iter(proc =>
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
      actionDecls.Where(proc => proc.RefinedAction != null).Iter(proc =>
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
      procToAtomicAction[proc] = new AtomicAction(impl, refinedAction, this);
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
        var yieldRequires = new List<CallCmd>();
        var yieldEnsures = new List<CallCmd>();
        foreach (var callCmd in proc.YieldRequires)
        {
          yieldRequires.Add(StripOld(callCmd));
        }
        foreach (var callCmd in proc.YieldEnsures)
        {
          yieldEnsures.Add(callCmd);
        }
        foreach (var callCmd in proc.YieldPreserves)
        {
          yieldRequires.Add(StripOld(callCmd));
          yieldEnsures.Add(callCmd);
        }
        
        if (proc.RefinedAction != null) // proc is an action procedure
        {
          AtomicAction refinedAction = procToAtomicAction[proc.RefinedAction.ActionDecl];
          var actionProc = new ActionProc(proc, yieldRequires, yieldEnsures, refinedAction);
          CheckRefinementSignature(actionProc);
          procToYieldingProc[proc] = actionProc;
        }
        else if (proc.MoverType != MoverType.None) // proc is a mover procedure
        {
          procToYieldingProc[proc] = new MoverProc(proc, yieldRequires, yieldEnsures);
        }
        else // proc refines the skip action
        {
          if (!procToAtomicAction.ContainsKey(SkipAtomicAction.ActionDecl))
          {
            procToAtomicAction[SkipAtomicAction.ActionDecl] = SkipAtomicAction;
          }
          var actionProc = new ActionProc(proc, yieldRequires, yieldEnsures, SkipAtomicAction);
          procToYieldingProc[proc] = actionProc;
        }
      }

      if (procToAtomicAction.ContainsKey(SkipAtomicAction.ActionDecl))
      {
        program.AddTopLevelDeclaration(SkipAtomicAction.ActionDecl);
        program.AddTopLevelDeclaration(SkipAtomicAction.Impl);
      }
    }
    
    private void TypeCheckLoopAnnotations()
    {
      foreach (var impl in program.Implementations.Where(impl => procToYieldingProc.ContainsKey(impl.Proc)))
      {
        var graph = Program.GraphFromImpl(impl);
        graph.ComputeLoops();
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
                Error(header, "expected layer attribute to indicate the highest yielding layer of this loop");
                continue;
              }
              if (layers[0] > yieldingLayer)
              {
                Error(header,
                  "yielding layer of loop must not be more than the disappearing layer of enclosing procedure");
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
            Error(header, "expected :yields attribute on this loop");
          }

          var availableLinearVarsAtHeader = new HashSet<Variable>(linearTypeChecker.AvailableLinearVars(header));
          foreach (var callCmd in yieldInvariants.Where(callCmd =>
                     linearTypeChecker.CheckLinearParameters(callCmd, availableLinearVarsAtHeader) == 0))
          {
            var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
            var calleeLayerNum = yieldInvariant.Layer;
            if (calleeLayerNum > yieldingLayer)
            {
              Error(callCmd, $"loop must yield at layer {calleeLayerNum} of the called yield invariant");
            }
          }

          yieldingLoops[header] = new YieldingLoop(yieldingLayer, yieldInvariants);

          foreach (PredicateCmd predCmd in header.Cmds.TakeWhile(cmd => cmd is PredicateCmd))
          {
            if (predCmd.Layers.Min() <= yieldingLayer &&
                VariableCollector.Collect(predCmd, true).OfType<GlobalVariable>().Any())
            {
              Error(predCmd,
                "invariant may not access a global variable since one of its layers is a yielding layer of its loop");
            }
          }
        }
      }
    }

    private class SignatureMatcher
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
        x.LayerRange.UpperLayer == actionProc.Layer &&
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

    private void TypeCheckLocalPendingAsyncCollectors()
    {
      var pendingAsyncProcs = program.TopLevelDeclarations.OfType<ActionDecl>()
        .Where(proc => proc.ActionQualifier == ActionQualifier.Async).Select(proc => proc.Name).ToHashSet();
      var pendingAsyncMultisetTypes = program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>()
        .Where(decl => pendingAsyncProcs.Contains(decl.Name)).Select(decl =>
          TypeHelper.MapType(TypeHelper.CtorType(decl), Type.Int)).ToHashSet();
      foreach (Implementation impl in program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl))
      {
        var proc = (YieldProcedureDecl)impl.Proc;
        implToPendingAsyncCollector[impl] = new Dictionary<CtorType, Variable>();
        foreach (Variable v in impl.LocVars.Where(v => v.HasAttribute(CivlAttributes.PENDING_ASYNC)))
        {
          if (!pendingAsyncMultisetTypes.Contains(v.TypedIdent.Type))
          {
            Error(v, "pending async collector is of incorrect type");
          }
          else if (v.LayerRange.LowerLayer != proc.Layer)
          {
            Error(v, "pending async collector must be introduced at the layer of the enclosing procedure");
          }
          else
          {
            var mapType = (MapType)v.TypedIdent.Type;
            var ctorType = (CtorType)mapType.Arguments[0];
            if (implToPendingAsyncCollector[impl].ContainsKey(ctorType))
            {
              Error(v, "duplicate pending async collector");
            }
            else
            {
              implToPendingAsyncCollector[impl][ctorType] = v;
            }
          }
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
      return param.LayerRange.Contains(actionProc.Layer) && !actionProc.HiddenFormals.Contains(param);
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

    #endregion

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
