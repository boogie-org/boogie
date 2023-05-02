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
    public ActionDecl SkipActionDecl;
    
    public Dictionary<ActionDecl, Action> procToAtomicAction;
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
      
      this.procToAtomicAction = new Dictionary<ActionDecl, Action>();
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

      SkipActionDecl = new ActionDecl(Token.NoToken, AddNamePrefix("Skip"), MoverType.Both, ActionQualifier.None,
        new List<Variable>(), new List<Variable>(), new List<ActionDeclRef>(), null, null, new List<ElimDecl>(),
        new List<IdentifierExpr>(), null, null);
      var skipImplementation = DeclHelper.Implementation(
        SkipActionDecl,
        new List<Variable>(),
        new List<Variable>(),
        new List<Variable>(),
        new List<Block> { BlockHelper.Block("init", new List<Cmd>()) });
      SkipActionDecl.LayerRange = LayerRange.MinMax;
      SkipActionDecl.Impl = skipImplementation;
      if (program.TopLevelDeclarations.OfType<YieldProcedureDecl>().Any())
      {
        program.AddTopLevelDeclaration(SkipActionDecl);
        program.AddTopLevelDeclaration(skipImplementation);
      }
      program.TopLevelDeclarations.OfType<YieldProcedureDecl>()
        .Where(decl => !decl.HasMoverType && decl.RefinedAction == null).Iter(decl =>
        {
          decl.RefinedAction = new ActionDeclRef(Token.NoToken, SkipActionDecl.Name)
          {
            ActionDecl = SkipActionDecl
          };
        });
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
      
      var actionDecls = TypeCheckActions();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      TypeCheckYieldingProcedures();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      InlineAtomicActions(actionDecls);
      CreateAtomicActions(actionDecls);
      CreateInductiveSequentializations(actionDecls);
      AttributeEraser.Erase(this);
      YieldSufficiencyTypeChecker.TypeCheck(this);
    }

    private HashSet<ActionDecl> TypeCheckActions()
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
      actionDecls.Where(proc => proc.RefinedAction != null).Iter(proc =>
      {
        var refinedProc = proc.RefinedAction.ActionDecl;
        var invariantProc = proc.InvariantAction.ActionDecl;
        SignatureMatcher.CheckInductiveSequentializationAbstractionSignature(proc, invariantProc, checkingContext);
        SignatureMatcher.CheckInductiveSequentializationAbstractionSignature(proc, refinedProc, checkingContext);
        foreach (var elimDecl in proc.Eliminates)
        {
          var targetProc = elimDecl.Target.ActionDecl;
          var absProc = elimDecl.Abstraction.ActionDecl;
          SignatureMatcher.CheckInductiveSequentializationAbstractionSignature(targetProc, absProc, checkingContext);
        }
      });
      return actionDecls;
    }

    private void TypeCheckYieldingProcedures()
    {
      foreach (var yieldingProc in program.Procedures.OfType<YieldProcedureDecl>())
      {
        foreach (var (header, yieldingLoop) in yieldingProc.YieldingLoops)
        {
          var availableLinearVarsAtHeader = new HashSet<Variable>(linearTypeChecker.AvailableLinearVars(header));
          yieldingLoop.YieldInvariants.Iter(callCmd => linearTypeChecker.CheckLinearParameters(callCmd, availableLinearVarsAtHeader));
        }
        if (yieldingProc.RefinedAction != null)
        {
          SignatureMatcher.CheckRefinementSignature(yieldingProc, checkingContext);
        }
      }
      
      // local collectors for pending asyncs
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
    
    private void InlineAtomicActions(HashSet<ActionDecl> actionDecls)
    {
      CivlUtil.AddInlineAttribute(SkipActionDecl);
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
    }

    private void CreateAtomicActions(HashSet<ActionDecl> actionDecls)
    {
      var invariantActionDecls = actionDecls.Where(decl => decl.InvariantAction != null)
        .Select(decl => decl.InvariantAction.ActionDecl).ToHashSet();

      // Initialize ActionDecls so that all the pending async machinery is set up.
      actionDecls.Iter(proc => proc.Initialize(program.monomorphizer));

      // Create all actions that do not refine another action.
      foreach (var actionDecl in actionDecls.Where(proc => proc.RefinedAction == null))
      {
        procToAtomicAction[actionDecl] = new Action(this, actionDecl, null, invariantActionDecls.Contains(actionDecl));
      }
      
      // Create all atomic actions that refine other actions via an inductive sequentialization.
      actionDecls.Where(proc => proc.RefinedAction != null)
        .Iter(decl => CreateActionsThatRefineAnotherAction(decl, invariantActionDecls));
    }
    
    private void CreateActionsThatRefineAnotherAction(ActionDecl actionDecl, HashSet<ActionDecl> invariantActionDecls)
    {
      if (procToAtomicAction.ContainsKey(actionDecl))
      {
        return;
      }
      var refinedProc = actionDecl.RefinedAction.ActionDecl;
      CreateActionsThatRefineAnotherAction(refinedProc, invariantActionDecls);
      var refinedAction = procToAtomicAction[refinedProc];
      procToAtomicAction[actionDecl] =
        new Action(this, actionDecl, refinedAction, invariantActionDecls.Contains(actionDecl));
    }

    private void CreateInductiveSequentializations(HashSet<ActionDecl> actionDecls)
    {
      actionDecls.Where(proc => proc.RefinedAction != null).Iter(proc =>
      {
        var action = procToAtomicAction[proc];
        var invariantProc = proc.InvariantAction.ActionDecl;
        var invariantAction = procToAtomicAction[invariantProc];
        var elim = new Dictionary<Action, Action>(proc.EliminationMap().Select(x =>
          KeyValuePair.Create(procToAtomicAction[x.Key], procToAtomicAction[x.Value])));
        inductiveSequentializations.Add(new InductiveSequentialization(this, action, invariantAction, elim));
      });
    }

    private class SignatureMatcher
    {
      public static void CheckRefinementSignature(YieldProcedureDecl proc, CheckingContext checkingContext)
      {
        var refinedActionDecl = proc.RefinedAction.ActionDecl;
        var signatureMatcher = new SignatureMatcher(proc, refinedActionDecl, checkingContext);
        var procInParams = proc.InParams.Where(x => proc.VisibleFormals.Contains(x)).ToList();
        var procOutParams = proc.OutParams.Where(x => proc.VisibleFormals.Contains(x)).ToList();
        var actionInParams = refinedActionDecl.InParams;
        var actionOutParams = refinedActionDecl.OutParams.SkipEnd(refinedActionDecl.Creates.Count).ToList();
        signatureMatcher.MatchFormals(procInParams, actionInParams, SignatureMatcher.IN);
        signatureMatcher.MatchFormals(procOutParams, actionOutParams, SignatureMatcher.OUT);
      }

      public static void CheckInductiveSequentializationAbstractionSignature(Procedure original, Procedure abstraction,
        CheckingContext checkingContext)
      {
        // Input and output parameters have to match exactly
        var signatureMatcher = new SignatureMatcher(original, abstraction, checkingContext);
        signatureMatcher.MatchFormals(original.InParams, abstraction.InParams, SignatureMatcher.IN);
        signatureMatcher.MatchFormals(original.OutParams, abstraction.OutParams, SignatureMatcher.OUT);
      }

      private static string IN = "in";
      private static string OUT = "out";
      private DeclWithFormals decl1;
      private DeclWithFormals decl2;
      private CheckingContext checkingContext;

      private SignatureMatcher(DeclWithFormals decl1, DeclWithFormals decl2, CheckingContext checkingContext)
      {
        this.decl1 = decl1;
        this.decl2 = decl2;
        this.checkingContext = checkingContext;
      }

      private void MatchFormals(List<Variable> formals1, List<Variable> formals2,
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
    
    #region Public access methods
    
    public IEnumerable<Action> LinkActions =>
      procToAtomicAction.Values.Where(action => action.ActionDecl.ActionQualifier == ActionQualifier.Link);

    public IEnumerable<Action> MoverActions => procToAtomicAction.Keys
      .Where(actionDecl => actionDecl.HasMoverType).Select(actionDecl => procToAtomicAction[actionDecl]);

    public IEnumerable<Action> AtomicActions => procToAtomicAction.Values;

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

      public void VisitAtomicAction(Action action)
      {
        Visit(action.FirstImpl);
        Visit(action.SecondImpl);
      }
    }
  }
}
