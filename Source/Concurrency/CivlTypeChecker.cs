using System;
using System.Collections.Generic;
using System.Linq;
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
    private string namePrefix;

    public Dictionary<Block, YieldingLoop> yieldingLoops;
    public Dictionary<Block, HashSet<int>> cooperatingLoopHeaders;
    public HashSet<Procedure> cooperatingProcedures;

    public Dictionary<Procedure, AtomicAction> procToAtomicAction;
    public Dictionary<Procedure, AtomicAction> procToIsInvariant;
    public Dictionary<Procedure, AtomicAction> procToIsAbstraction;
    public Dictionary<Procedure, YieldingProc> procToYieldingProc;
    public Dictionary<Procedure, LemmaProc> procToLemmaProc;
    public Dictionary<Procedure, IntroductionAction> procToIntroductionAction;
    public Dictionary<Procedure, YieldInvariant> procToYieldInvariant;
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

    public AtomicAction SkipAtomicAction;

    public CivlTypeChecker(Program program)
    {
      this.checkingContext = new CheckingContext(null);
      this.program = program;
      this.linearTypeChecker = new LinearTypeChecker(this);

      this.globalVarToLayerRange = new Dictionary<Variable, LayerRange>();
      this.localVarToLayerRange = new Dictionary<Variable, LayerRange>();
      this.yieldingLoops = new Dictionary<Block, YieldingLoop>();
      this.cooperatingLoopHeaders = new Dictionary<Block, HashSet<int>>();
      this.cooperatingProcedures = new HashSet<Procedure>();
      this.absyToLayerNums = new Dictionary<Absy, HashSet<int>>();
      this.procToAtomicAction = new Dictionary<Procedure, AtomicAction>();
      this.procToIsInvariant = new Dictionary<Procedure, AtomicAction>();
      this.procToIsAbstraction = new Dictionary<Procedure, AtomicAction>();
      this.procToYieldingProc = new Dictionary<Procedure, YieldingProc>();
      this.procToLemmaProc = new Dictionary<Procedure, LemmaProc>();
      this.procToIntroductionAction = new Dictionary<Procedure, IntroductionAction>();
      this.procToYieldInvariant = new Dictionary<Procedure, YieldInvariant>();
      this.implToPendingAsyncCollector = new Dictionary<Implementation, Variable>();
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
        new List<Block> {BlockHelper.Block("init", new List<Cmd>())});
      SkipAtomicAction = new AtomicAction(skipProcedure, skipImplementation, LayerRange.MinMax, MoverType.Both);
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
      TypeCheckGlobalVariables();
      TypeCheckLemmaProcedures();
      TypeCheckYieldInvariants();

      TypeCheckActionDecls();
      TypeCheckPendingAsyncMachinery();

      if (checkingContext.ErrorCount > 0)
        return;

      linearTypeChecker.TypeCheck();
      if (checkingContext.ErrorCount > 0)
        return;

      TypeCheckInductiveSequentializations();
      TypeCheckYieldingProcedureDecls();
      TypeCheckLocalVariables();

      if (checkingContext.ErrorCount > 0)
        return;

      TypeCheckActionImpls();
      TypeCheckYieldingProcedureImpls();

      if (checkingContext.ErrorCount > 0)
        return;

      TypeCheckLoopAnnotations();

      TypeCheckRefinementLayers();

      TypeCheckCommutativityHints();

      AttributeEraser.Erase(this);

      if (checkingContext.ErrorCount > 0)
        return;

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
        inductiveSequentializations.Select(x => x.inputAction.layerRange.upperLayerNum).ToList();

      var intersect = allRefinementLayers.Intersect(allInductiveSequentializationLayers).ToList();
      if (intersect.Any())
        checkingContext.Error(Token.NoToken,
          "The following layers mix refinement with IS: " + string.Join(",", intersect));

      foreach (var g in GlobalVariables)
      {
        var layerRange = GlobalVariableLayerRange(g);
        if (allInductiveSequentializationLayers.Contains(layerRange.lowerLayerNum))
          Error(g, $"Global variable {g.Name} cannot be introduced at layer with IS");
        if (allInductiveSequentializationLayers.Contains(layerRange.upperLayerNum))
          Error(g, $"Global variable {g.Name} cannot be hidden at layer with IS");
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
            Error(proc, "Layer range of an introduction action should be singleton");
          }
          else if (proc.Modifies.Any(ie => GlobalVariableLayerRange(ie.Decl).lowerLayerNum != layerRange.lowerLayerNum))
          {
            Error(proc, "Introduction actions can modify a global variable only on its introduction layer");
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
      foreach (var action in Enumerable.Concat<Action>(AllAtomicActions, procToIntroductionAction.Values))
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
              string actionName = (string) kv.Params[0];
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
                string abstractionName = (string) kv.Params[1];
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
          if (checkingContext.ErrorCount == 0)
          {
            inductiveSequentializations.Add(
              new InductiveSequentialization(this, action, action.refinedAction, invariantAction, elim));
          }
        }
      }
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

      if (checkingContext.ErrorCount > 0) return;
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
          var linearKind = linearTypeChecker.FindLinearKind(param);
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
      var emptySubst = Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>());
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

        List<CallCmd> yieldRequires, yieldEnsures;
        TypeCheckYieldingPrePostDecls(proc, out yieldRequires, out yieldEnsures);

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
              if (callCmd == null) continue;
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
              checkingContext.Error(formals1[i],
                $"mismatched linearity type of {inout}-parameter in {decl2.Name}: {msg}");
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
        .SkipEnd(actionProc.refinedAction.HasPendingAsyncs ? 1 : 0).ToList();
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
      var refinedActionOutParams = action.refinedAction.proc.OutParams
        .SkipEnd(action.refinedAction.HasPendingAsyncs ? 1 : 0).ToList();

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
              Error(v,
                "Pending async collector must be introduced at the disappearing layer of the enclosing procedure");
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

    private void TypeCheckPendingAsyncMachinery()
    {
      foreach (var datatypeTypeCtorDecl in program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>())
      {
        if (datatypeTypeCtorDecl.HasAttribute(CivlAttributes.PENDING_ASYNC))
        {
          if (pendingAsyncType == null)
          {
            pendingAsyncType = new CtorType(datatypeTypeCtorDecl.tok, datatypeTypeCtorDecl, new List<Type>());
            pendingAsyncMultisetType = new MapType(Token.NoToken, new List<TypeVariable>(),
              new List<Type> {pendingAsyncType}, Type.Int);
          }
          else
          {
            Error(datatypeTypeCtorDecl, $"Duplicate pending async type {datatypeTypeCtorDecl.Name}");
          }
        }
      }

      if (pendingAsyncType != null)
      {
        pendingAsyncAdd = program.monomorphizer.Monomorphize("MapAdd",
          new Dictionary<string, Type>() { {"T", pendingAsyncType} });

        var pendingAsyncDatatypeTypeCtorDecl = pendingAsyncType.Decl as DatatypeTypeCtorDecl; 
        foreach (var ctor in pendingAsyncDatatypeTypeCtorDecl.Constructors)
        {
          string actionName = QKeyValue.FindStringAttribute(ctor.Attributes, CivlAttributes.PENDING_ASYNC);
          if (actionName != null)
          {
            AtomicAction action = FindAtomicAction(actionName);
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

        if (!action.HasPendingAsyncs)
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
      return !proc.HasAttribute(CivlAttributes.YIELDS) &&
             (GetMoverType(proc) != null ||
              proc.HasAttribute(CivlAttributes.INTRO) ||
              proc.HasAttribute(CivlAttributes.IS_INVARIANT) ||
              proc.HasAttribute(CivlAttributes.IS_ABSTRACTION));
    }

    private bool IsLemmaProcedure(Procedure proc)
    {
      return !proc.HasAttribute(CivlAttributes.YIELDS) && proc.HasAttribute(CivlAttributes.LEMMA);
    }

    private bool IsYieldInvariant(Procedure proc)
    {
      return proc.HasAttribute(CivlAttributes.YIELD_INVARIANT);
    }

    private MoverType GetActionMoverType(Procedure proc)
    {
      if (proc.HasAttribute(CivlAttributes.IS_INVARIANT))
        return MoverType.Non;
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
            x = MoverType.Non;
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

    public IEnumerable<AtomicAction> AllAtomicActions =>
      procToAtomicAction.Union(procToIsInvariant).Union(procToIsAbstraction)
        .Select(x => x.Value);

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

    private class ActionVisitor : ReadOnlyVisitor
    {
      private CivlTypeChecker civlTypeChecker;
      private Action action;

      public ActionVisitor(CivlTypeChecker civlTypeChecker)
      {
        this.civlTypeChecker = civlTypeChecker;
      }

      internal void VisitAction(Action action)
      {
        this.action = action;
        foreach (var g in action.gate)
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
          var globalVarLayerRange = civlTypeChecker.GlobalVariableLayerRange(node.Decl);
          if (!action.layerRange.Subset(globalVarLayerRange) ||
              (globalVarLayerRange.lowerLayerNum == action.layerRange.lowerLayerNum &&
               action is AtomicAction))
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
        civlTypeChecker.Error(node, "Call command not allowed inside an atomic action");
        return base.VisitCallCmd(node);
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
              caller.InParams.Union(caller.OutParams).Where(p => kinds.Contains(civlTypeChecker.linearTypeChecker.FindLinearKind(p)))
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
          civlTypeChecker.Error(attr, "Name of a yield invariant must be provided at position 1");
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
            civlTypeChecker.Error(attr, $"Illegal expression at position {i}");
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

        if (CivlUtil.ResolveAndTypecheck(callCmd) != 0)
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
          if (civlTypeChecker.linearTypeChecker.FindDomainName(formal) != null)
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
                "Layer range mismatch at position {0}: local variables accessed in rhs must be available at all layers where the lhs exists",
                i);
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
        Require(node.CallCmds.Where(callCmd => callCmd.HasAttribute(CivlAttributes.REFINES)).Count() <= 1, node,
          "At most one arm of a parallel call can refine the specification action");
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
                Require(highestRefinedAction.pendingAsyncCtor != null, call,
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

      public override YieldCmd VisitYieldCmd(YieldCmd node)
      {
        if (yieldingProc is MoverProc)
        {
          civlTypeChecker.Error(node, "A mover procedure cannot contain explicit yield statements");
        }

        return base.VisitYieldCmd(node);
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
