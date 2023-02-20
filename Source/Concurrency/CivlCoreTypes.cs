using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public enum MoverType
  {
    Non,
    Right,
    Left,
    Both
  }

  public class LayerRange
  {
    public static int Min = 0;
    public static int Max = int.MaxValue;
    public static LayerRange MinMax = new LayerRange(Min, Max);

    public int lowerLayerNum;
    public int upperLayerNum;

    public LayerRange(int layer) : this(layer, layer)
    {
    }

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

    public bool OverlapsWith(LayerRange other)
    {
      return lowerLayerNum <= other.upperLayerNum && other.lowerLayerNum <= upperLayerNum;
    }

    public override string ToString()
    {
      return $"[{lowerLayerNum}, {upperLayerNum}]";
    }

    public override bool Equals(object obj)
    {
      LayerRange other = obj as LayerRange;
      if (obj == null)
      {
        return false;
      }

      return lowerLayerNum == other.lowerLayerNum && upperLayerNum == other.upperLayerNum;
    }

    public override int GetHashCode()
    {
      return (23 * 31 + lowerLayerNum) * 31 + upperLayerNum;
    }
  }

  public abstract class Action
  {
    public Procedure proc;
    public Implementation impl;
    public LayerRange layerRange;
    public List<AssertCmd> gate;
    public HashSet<Variable> gateUsedGlobalVars;
    public HashSet<Variable> actionUsedGlobalVars;
    public HashSet<Variable> modifiedGlobalVars;

    public int pendingAsyncStartIndex;
    public List<AsyncAction> pendingAsyncs;
    public Function inputOutputRelation;

    protected Action(Procedure proc, Implementation impl, LayerRange layerRange)
    {
      this.proc = proc;
      this.impl = impl;
      this.layerRange = layerRange;

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

    public void CompleteInitialization(CivlTypeChecker civlTypeChecker, IEnumerable<AsyncAction> pendingAsyncs)
    {
      this.pendingAsyncs = new List<AsyncAction>(pendingAsyncs);
      var lhss = new List<IdentifierExpr>();
      var rhss = new List<Expr>();
      pendingAsyncs.Iter(action =>
      {
        var pa = civlTypeChecker.Formal($"PAs_{action.impl.Name}", action.pendingAsyncMultisetType, false);
        impl.OutParams.Add(pa);
        proc.OutParams.Add(pa);
        lhss.Add(Expr.Ident(pa));
        rhss.Add(ExprHelper.FunctionCall(action.pendingAsyncConst, Expr.Literal(0)));
      });
      if (pendingAsyncs.Any())
      {
        var tc = new TypecheckingContext(null, civlTypeChecker.Options);
        var assignCmd = CmdHelper.AssignCmd(lhss, rhss);
        assignCmd.Typecheck(tc);
        impl.Blocks[0].Cmds.Insert(0, assignCmd);
      }
      
      DesugarCreateAsyncs(civlTypeChecker);
      
      gate = HoistAsserts(impl, civlTypeChecker.Options);
      gateUsedGlobalVars = new HashSet<Variable>(VariableCollector.Collect(gate).Where(x => x is GlobalVariable));
      actionUsedGlobalVars = new HashSet<Variable>(VariableCollector.Collect(impl).Where(x => x is GlobalVariable));
      modifiedGlobalVars = new HashSet<Variable>(proc.Modifies.Select(x => x.Decl));
    }
    
    public bool HasPendingAsyncs => pendingAsyncs.Count > 0;

    public Variable PAs(CtorType pendingAsyncType)
    {
      var pendingAsyncMultisetType = TypeHelper.MapType(pendingAsyncType, Type.Int);
      return impl.OutParams.Skip(this.pendingAsyncStartIndex).First(v => v.TypedIdent.Type.Equals(pendingAsyncMultisetType));
    }
    
    public bool HasAssumeCmd => impl.Blocks.Any(b => b.Cmds.Any(c => c is AssumeCmd));

    public void InitializeInputOutputRelation(CivlTypeChecker civlTypeChecker)
    {
      if (inputOutputRelation != null)
      {
        return;
      }
      var alwaysMap = new Dictionary<Variable, Expr>();
      var foroldMap = new Dictionary<Variable, Expr>();
      civlTypeChecker.program.GlobalVariables.Iter(g =>
      {
        alwaysMap[g] = Expr.Ident(civlTypeChecker.BoundVariable(g.Name, g.TypedIdent.Type));
        foroldMap[g] = Expr.Ident(civlTypeChecker.BoundVariable($"old_{g.Name}", g.TypedIdent.Type));
      });
      impl.InParams.Concat(impl.OutParams).Iter(v =>
      {
        alwaysMap[v] = Expr.Ident(VarHelper.Formal(v.Name, v.TypedIdent.Type, true));
      });
      var always = Substituter.SubstitutionFromDictionary(alwaysMap);
      var forold = Substituter.SubstitutionFromDictionary(foroldMap);
      var transitionRelationExpr =
        Substituter.ApplyReplacingOldExprs(always, forold,
          TransitionRelationComputation.Refinement(civlTypeChecker, this, new HashSet<Variable>(modifiedGlobalVars)));
      var gateExprs = gate.Select(assertCmd =>
        Substituter.ApplyReplacingOldExprs(always, forold, ExprHelper.Old(assertCmd.Expr)));
      var transitionRelationInputs = impl.InParams.Concat(impl.OutParams)
        .Select(key => alwaysMap[key]).OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList();
      inputOutputRelation = new Function(Token.NoToken, $"Civl_InputOutputRelation_{proc.Name}", new List<TypeVariable>(),
        transitionRelationInputs, VarHelper.Formal(TypedIdent.NoName, Type.Bool, false), null,
        new QKeyValue(Token.NoToken, "inline", new List<object>(), null));
      var existsVars = foroldMap.Values
        .Concat(alwaysMap.Keys.Where(key => key is GlobalVariable).Select(key => alwaysMap[key]))
        .OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList();
      inputOutputRelation.Body =
        ExprHelper.ExistsExpr(existsVars, Expr.And(gateExprs.Append(transitionRelationExpr)));
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, inputOutputRelation.Body);
      civlTypeChecker.program.AddTopLevelDeclaration(inputOutputRelation);
    }

    private void DesugarCreateAsyncs(CivlTypeChecker civlTypeChecker)
    {
      impl.Blocks.Iter(block =>
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd)
          {
            var originalProc = (Procedure)civlTypeChecker.program.monomorphizer.GetOriginalDecl(callCmd.Proc);
            if (originalProc.Name == "create_async" ||
                originalProc.Name == "create_asyncs" ||
                originalProc.Name == "create_multi_asyncs" ||
                originalProc.Name == "set_choice")
            {
              var pendingAsyncType = (CtorType)civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
              var pendingAsync = pendingAsyncs.First(action => action.pendingAsyncType.Equals(pendingAsyncType));
              var tc = new TypecheckingContext(null, civlTypeChecker.Options);
              if (originalProc.Name == "create_async" || originalProc.Name == "create_asyncs" || originalProc.Name == "create_multi_asyncs")
              {
                var pendingAsyncMultiset = originalProc.Name == "create_async"
                  ?
                  Expr.Store(ExprHelper.FunctionCall(pendingAsync.pendingAsyncConst, Expr.Literal(0)), callCmd.Ins[0],
                    Expr.Literal(1))
                  : originalProc.Name == "create_asyncs"
                    ? ExprHelper.FunctionCall(pendingAsync.pendingAsyncIte, callCmd.Ins[0],
                      ExprHelper.FunctionCall(pendingAsync.pendingAsyncConst, Expr.Literal(1)),
                      ExprHelper.FunctionCall(pendingAsync.pendingAsyncConst, Expr.Literal(0)))
                    : callCmd.Ins[0];
                var assignCmd = CmdHelper.AssignCmd(PAs(pendingAsyncType),
                  ExprHelper.FunctionCall(pendingAsync.pendingAsyncAdd, Expr.Ident(PAs(pendingAsyncType)),
                    pendingAsyncMultiset));
                assignCmd.Typecheck(tc);
                newCmds.Add(assignCmd);
              }
              else
              {
                // originalProc.Name == "set_choice"
                var emptyExpr = Expr.Eq(Expr.Ident(PAs(pendingAsyncType)),
                  ExprHelper.FunctionCall(pendingAsync.pendingAsyncConst, Expr.Literal(0)));
                var memberExpr = Expr.Gt(Expr.Select(Expr.Ident(PAs(pendingAsyncType)), callCmd.Ins[0]),
                  Expr.Literal(0));
                var assertCmd = CmdHelper.AssertCmd(cmd.tok, Expr.Or(emptyExpr, memberExpr),
                  "Choice is not a created pending async");
                assertCmd.Typecheck(tc);
                newCmds.Add(assertCmd);
              }
              continue;
            }
          }
          newCmds.Add(cmd);
        }
        block.Cmds = newCmds;
      });
    }
    
    /*
     * HoistAsserts computes the weakest liberal precondition (wlp) of the body
     * of impl as a collection of AssertCmd's. As a side effect, all AssertCmd's
     * in any block of impl are removed.
     *
     * HoistAsserts assumes that the body of impl does not contain any loops or
     * calls. The blocks in impl are sorted from entry to exit and processed in
     * reverse order, thus ensuring that a block is processed only once the wlp
     * of all its successors has been computed.
     */
    private List<AssertCmd> HoistAsserts(Implementation impl, ConcurrencyOptions options)
    {
      Dictionary<Block, List<AssertCmd>> wlps = new Dictionary<Block, List<AssertCmd>>();
      Graph<Block> dag = Program.GraphFromBlocks(impl.Blocks, false);
      foreach (var block in dag.TopologicalSort())
      {
        if (block.TransferCmd is ReturnCmd)
        {
          var wlp = HoistAsserts(block.Cmds, new List<AssertCmd>(), options);
          wlps.Add(block, wlp);
        }
        else if (block.TransferCmd is GotoCmd gotoCmd)
        {
          var wlp =
            HoistAsserts(block.Cmds, gotoCmd.labelTargets.SelectMany(b => wlps[b]).ToList(), options);
          wlps.Add(block, wlp);
        }
        else
        {
          throw new cce.UnreachableException();
        }
      }
      return wlps[impl.Blocks[0]].Select(assertCmd => Forall(impl.LocVars.Union(impl.OutParams), assertCmd)).ToList();
    }

    private List<AssertCmd> HoistAsserts(List<Cmd> cmds, List<AssertCmd> postconditions, ConcurrencyOptions options)
    {
      for (int i = cmds.Count - 1; i >= 0; i--)
      {
        var cmd = cmds[i];
        if (cmd is AssertCmd assertCmd)
        {
          postconditions.Add(assertCmd);
        } 
        else if (cmd is AssumeCmd assumeCmd)
        {
          postconditions = postconditions
            .Select(assertCmd => new AssertCmd(assertCmd.tok, Expr.Imp(assumeCmd.Expr, assertCmd.Expr))).ToList();
        }
        else if (cmd is AssignCmd assignCmd)
        {
          var varToExpr = new Dictionary<Variable, Expr>();
          var simpleAssignCmd = assignCmd.AsSimpleAssignCmd;
          for (var j = 0; j < simpleAssignCmd.Lhss.Count; j++)
          {
            var lhs = simpleAssignCmd.Lhss[j];
            var rhs = simpleAssignCmd.Rhss[j];
            varToExpr.Add(lhs.DeepAssignedVariable, rhs);
          }
          postconditions = postconditions.Select(assertCmd =>
            new AssertCmd(assertCmd.tok, SubstitutionHelper.Apply(varToExpr, assertCmd.Expr))).ToList();
        }
        else if (cmd is HavocCmd havocCmd)
        {
          postconditions = postconditions.Select(assertCmd => Forall(havocCmd.Vars.Select(ie => ie.Decl), assertCmd))
            .ToList();
        }
        else if (cmd is UnpackCmd unpackCmd)
        {
          var desugaredCmd = (StateCmd) unpackCmd.GetDesugaring(options);
          postconditions = HoistAsserts(desugaredCmd.Cmds, postconditions, options); // removes precondition assert from desugaredCmd.Cmds
        }
        else
        {
          throw new cce.UnreachableException();
        }
      }
      cmds.RemoveAll(cmd => cmd is AssertCmd);
      return postconditions;
    }
    
    private static AssertCmd Forall(IEnumerable<Variable> vars, AssertCmd assertCmd)
    {
      var freeObjects = new GSet<object>();
      assertCmd.Expr.ComputeFreeVariables(freeObjects);
      var quantifiedVars = freeObjects.OfType<Variable>().Intersect(vars);
      if (quantifiedVars.Count() == 0)
      {
        return assertCmd;
      }
      var varMapping = quantifiedVars.ToDictionary(v => v,
        v => (Variable) VarHelper.BoundVariable(v.Name, v.TypedIdent.Type));
      return new AssertCmd(assertCmd.tok,
        ExprHelper.ForallExpr(varMapping.Values.ToList(), SubstitutionHelper.Apply(varMapping, assertCmd.Expr)));
    }
  }

    /*
     * An introduction action may have a layer range which allows it to be called
     * from other atomic actions. But its lower layer is special because the variables
     * it can modify must have been introduced at that layer.
     */
  public class IntroductionAction : Action
  {
    public IntroductionAction(Procedure proc, Implementation impl, LayerRange layerRange) : base(proc, impl, layerRange)
    {
    }

    public int LayerNum => layerRange.lowerLayerNum;
  }

  public class AtomicAction : Action
  {
    public MoverType moverType;
    public AtomicAction refinedAction;

    public List<AssertCmd> firstGate;
    public Implementation firstImpl;
    public List<AssertCmd> secondGate;
    public Implementation secondImpl;
    
    public Dictionary<Variable, Function> triggerFunctions;

    public AtomicAction(Procedure proc, Implementation impl, LayerRange layerRange, MoverType moverType, AtomicAction refinedAction) : 
      base(proc, impl, layerRange)
    {
      this.moverType = moverType;
      this.refinedAction = refinedAction;
      pendingAsyncStartIndex = impl.OutParams.Count;
    }

    public new void CompleteInitialization(CivlTypeChecker civlTypeChecker, IEnumerable<AsyncAction> pendingAsyncs)
    {
      base.CompleteInitialization(civlTypeChecker, pendingAsyncs);

      AtomicActionDuplicator.SetupCopy(this, ref firstGate, ref firstImpl, "first_");
      AtomicActionDuplicator.SetupCopy(this, ref secondGate, ref secondImpl, "second_");
      DeclareTriggerFunctions();
    }

    public bool IsRightMover
    {
      get { return moverType == MoverType.Right || moverType == MoverType.Both; }
    }

    public bool IsLeftMover
    {
      get { return moverType == MoverType.Left || moverType == MoverType.Both; }
    }

    public bool TriviallyCommutesWith(AtomicAction other)
    {
      return !this.modifiedGlobalVars.Intersect(other.actionUsedGlobalVars).Any() &&
             !this.actionUsedGlobalVars.Intersect(other.modifiedGlobalVars).Any();
    }

    private void DeclareTriggerFunctions()
    {
      triggerFunctions = new Dictionary<Variable, Function>();
      foreach (var v in impl.LocVars)
      {
        List<Variable> args = new List<Variable> {VarHelper.Formal(v.Name, v.TypedIdent.Type, true)};
        Variable result = VarHelper.Formal("r", Type.Bool, false);
        triggerFunctions[v] = new Function(Token.NoToken, $"Trigger_{impl.Name}_{v.Name}", args, result);
      }

      for (int i = 0; i < impl.LocVars.Count; i++)
      {
        triggerFunctions[firstImpl.LocVars[i]] = triggerFunctions[impl.LocVars[i]];
        triggerFunctions[secondImpl.LocVars[i]] = triggerFunctions[impl.LocVars[i]];
      }
    }

    /*
     * This method adds triggers for each local variable at the beginning of the atomic
     * action and after every havoc of the variable.
     * As an optimization, the injection of the trigger is performed only if the variable
     * is live at the point of injection.
     */
    public void AddTriggerAssumes(Program program, ConcurrencyOptions options)
    {
      var liveVariableAnalysis = new AtomicActionLiveVariableAnalysis(impl, options);
      liveVariableAnalysis.Compute();
      foreach (Variable v in impl.LocVars)
      {
        var f = triggerFunctions[v];
        program.AddTopLevelDeclaration(f);
        if (liveVariableAnalysis.IsLiveBefore(v, impl.Blocks[0]))
        {
          var assume = CmdHelper.AssumeCmd(ExprHelper.FunctionCall(f, Expr.Ident(v)));
          impl.Blocks[0].Cmds.Insert(0, assume);
        }
      }
      impl.Blocks.Iter(block =>
      {
        block.Cmds = block.Cmds.SelectMany(cmd =>
        {
          var newCmds = new List<Cmd> { cmd };
          if (cmd is HavocCmd havocCmd)
          {
            var liveHavocVars = new HashSet<Variable>(havocCmd.Vars.Select(x => x.Decl)
              .Where(v => liveVariableAnalysis.IsLiveAfter(v, havocCmd)));
            impl.LocVars.Intersect(liveHavocVars).Iter(v =>
            {
              newCmds.Add(CmdHelper.AssumeCmd(ExprHelper.FunctionCall(triggerFunctions[v], Expr.Ident(v))));
            });
          }
          return newCmds;
        }).ToList();
      });
    }
  }

  public class AsyncAction : AtomicAction
  {
    public DatatypeConstructor pendingAsyncCtor;
    public CtorType pendingAsyncType;
    public MapType pendingAsyncMultisetType;
    public Function pendingAsyncAdd;
    public Function pendingAsyncConst;
    public Function pendingAsyncIte;

    public AsyncAction(CivlTypeChecker civlTypeChecker, Procedure proc, Implementation impl, LayerRange layerRange,
      MoverType moverType) :
      base(proc, impl, layerRange, moverType, null)
    {
      var pendingAsyncCtorDecl = civlTypeChecker.program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>()
        .First(x => x.Name == proc.Name);
      pendingAsyncCtor = pendingAsyncCtorDecl.GetConstructor(proc.Name);
      pendingAsyncType = new CtorType(pendingAsyncCtorDecl.tok, pendingAsyncCtorDecl, new List<Type>());
      pendingAsyncMultisetType = TypeHelper.MapType(pendingAsyncType, Type.Int);
      pendingAsyncAdd = civlTypeChecker.program.monomorphizer.InstantiateFunction("MapAdd",
        new Dictionary<string, Type>() { { "T", pendingAsyncType } });
      pendingAsyncConst = civlTypeChecker.program.monomorphizer.InstantiateFunction("MapConst",
        new Dictionary<string, Type>() { { "T", pendingAsyncType }, { "U", Type.Int } });
      pendingAsyncIte = civlTypeChecker.program.monomorphizer.InstantiateFunction("MapIte",
        new Dictionary<string, Type>() { { "T", pendingAsyncType }, { "U", Type.Int } });
    }
  }

  public class InvariantAction : Action
  {
    public DatatypeTypeCtorDecl choiceDatatypeTypeCtorDecl;

    public InvariantAction(Procedure proc, Implementation impl, LayerRange layerRange) : base(proc, impl, layerRange)
    {
    }

    public DatatypeConstructor ChoiceConstructor(CtorType pendingAsyncType)
    {
      return choiceDatatypeTypeCtorDecl.Constructors.First(x => x.InParams[0].TypedIdent.Type.Equals(pendingAsyncType));
    }

    public void CompleteInitialization(CivlTypeChecker civlTypeChecker, IEnumerable<AsyncAction> pendingAsyncs,
      IEnumerable<AsyncAction> elimPendingAsyncs)
    {
      var choiceDatatypeName = $"Choice_{impl.Name}";
      choiceDatatypeTypeCtorDecl =
        new DatatypeTypeCtorDecl(Token.NoToken, choiceDatatypeName, new List<TypeVariable>(), null);
      elimPendingAsyncs.Iter(elim =>
      {
        var field = new TypedIdent(Token.NoToken, elim.impl.Name, elim.pendingAsyncType);
        choiceDatatypeTypeCtorDecl.AddConstructor(Token.NoToken, $"{choiceDatatypeName}_{elim.impl.Name}",
          new List<TypedIdent>() { field });
      });
      civlTypeChecker.program.AddTopLevelDeclaration(choiceDatatypeTypeCtorDecl);

      var choice = VarHelper.Formal("choice", TypeHelper.CtorType(choiceDatatypeTypeCtorDecl), false);
      DesugarSetChoice(civlTypeChecker, choice);

      base.CompleteInitialization(civlTypeChecker, pendingAsyncs);

      impl.OutParams.Add(choice);
      proc.OutParams.Add(choice);
    }

    private void DesugarSetChoice(CivlTypeChecker civlTypeChecker, Variable choice)
    {
      impl.Blocks.Iter(block =>
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          newCmds.Add(cmd);
          if (cmd is CallCmd callCmd)
          {
            var originalProc = (Procedure)civlTypeChecker.program.monomorphizer.GetOriginalDecl(callCmd.Proc);
            if (originalProc.Name == "set_choice")
            {
              var pendingAsyncType = (CtorType)civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
              var tc = new TypecheckingContext(null, civlTypeChecker.Options);
              var lhs = CmdHelper.FieldAssignLhs(Expr.Ident(choice), pendingAsyncType.Decl.Name);
              var assignCmd = CmdHelper.AssignCmd(lhs, callCmd.Ins[0]);
              assignCmd.Typecheck(tc);
              newCmds.Add(assignCmd);
            }
          }
        }
        block.Cmds = newCmds;
      });
    }
  }
  
  public class YieldInvariant
  {
    public Procedure proc;
    private int layer;

    public YieldInvariant(Procedure proc, int layer)
    {
      this.proc = proc;
      this.layer = layer;
      this.proc.Ensures.AddRange(this.proc.Requires.Select(requires =>
        new Ensures(requires.tok, false, requires.Condition, null)));
    }

    public int LayerNum => layer;
  }

  public class YieldingLoop
  {
    public HashSet<int> layers;
    public List<CallCmd> yieldInvariants;

    public YieldingLoop(HashSet<int> layers, List<CallCmd> yieldInvariants)
    {
      this.layers = layers;
      this.yieldInvariants = yieldInvariants;
    }
  }

  public abstract class YieldingProc
  {
    public Procedure proc;
    public MoverType moverType;
    public int upperLayer;
    public List<CallCmd> yieldRequires;
    public List<CallCmd> yieldEnsures;

    public YieldingProc(Procedure proc, MoverType moverType, int upperLayer,
      List<CallCmd> yieldRequires,
      List<CallCmd> yieldEnsures)
    {
      this.proc = proc;
      this.moverType = moverType;
      this.upperLayer = upperLayer;
      this.yieldRequires = yieldRequires;
      this.yieldEnsures = yieldEnsures;
    }

    public bool IsRightMover
    {
      get { return moverType == MoverType.Right || moverType == MoverType.Both; }
    }

    public bool IsLeftMover
    {
      get { return moverType == MoverType.Left || moverType == MoverType.Both; }
    }
  }

  public class MoverProc : YieldingProc
  {
    public HashSet<Variable> modifiedGlobalVars;

    public MoverProc(Procedure proc, MoverType moverType, int upperLayer,
      List<CallCmd> yieldRequires,
      List<CallCmd> yieldEnsures)
      : base(proc, moverType, upperLayer, yieldRequires, yieldEnsures)
    {
      modifiedGlobalVars = new HashSet<Variable>(proc.Modifies.Select(ie => ie.Decl));
    }
  }

  public class ActionProc : YieldingProc
  {
    public AtomicAction refinedAction;
    public HashSet<Variable> hiddenFormals;

    public ActionProc(Procedure proc, AtomicAction refinedAction, int upperLayer, HashSet<Variable> hiddenFormals,
      List<CallCmd> yieldRequires,
      List<CallCmd> yieldEnsures)
      : base(proc, refinedAction.moverType, upperLayer, yieldRequires, yieldEnsures)
    {
      this.refinedAction = refinedAction;
      this.hiddenFormals = hiddenFormals;
    }

    public AtomicAction RefinedActionAtLayer(int layer)
    {
      Debug.Assert(layer >= upperLayer);
      var action = refinedAction;
      while (action != null)
      {
        if (layer <= action.layerRange.upperLayerNum)
        {
          return action;
        }

        action = action.refinedAction;
      }

      return null;
    }
  }

  public class LemmaProc
  {
    public Procedure proc;

    public LemmaProc(Procedure proc)
    {
      this.proc = proc;
    }
  }

  /// <summary>
  /// Creates first/second copies of atomic actions used in commutativity checks
  /// (i.e., all non-global variables are prefixed with first_ resp. second_).
  /// Note that we also rename bound variables.
  /// </summary>
  class AtomicActionDuplicator : Duplicator
  {
    private readonly string prefix;
    private Dictionary<Variable, Expr> subst;
    private Dictionary<Variable, Expr> bound;
    private List<Variable> inParamsCopy;
    private List<Variable> outParamsCopy;
    private List<Variable> localsCopy;

    public static void SetupCopy(AtomicAction action, ref List<AssertCmd> gateCopy, ref Implementation implCopy,
      string prefix)
    {
      var aad = new AtomicActionDuplicator(prefix, action);

      gateCopy = new List<AssertCmd>();
      foreach (AssertCmd assertCmd in action.gate)
      {
        gateCopy.Add((AssertCmd) aad.Visit(assertCmd));
      }

      implCopy = aad.VisitImplementation(action.impl);
    }

    private AtomicActionDuplicator(string prefix, AtomicAction action)
    {
      this.prefix = prefix;
      subst = new Dictionary<Variable, Expr>();
      bound = new Dictionary<Variable, Expr>();

      inParamsCopy = new List<Variable>();
      outParamsCopy = new List<Variable>();
      localsCopy = new List<Variable>();


      foreach (Variable x in action.impl.InParams)
      {
        Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          true, x.Attributes);
        inParamsCopy.Add(xCopy);
        subst[x] = Expr.Ident(xCopy);
      }

      foreach (Variable x in action.impl.OutParams)
      {
        Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          false, x.Attributes);
        outParamsCopy.Add(xCopy);
        subst[x] = Expr.Ident(xCopy);
      }

      foreach (Variable x in action.impl.LocVars)
      {
        Variable xCopy = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), x.Attributes);
        subst[x] = Expr.Ident(xCopy);
        localsCopy.Add(xCopy);
      }
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      node = base.VisitImplementation(node);
      node.InParams = inParamsCopy;
      node.OutParams = outParamsCopy;
      node.LocVars = localsCopy;
      return node;
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
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          x.Attributes));

      foreach (var x in node.Dummies)
      {
        bound.Add(x, Expr.Ident(oldToNew[x]));
      }

      var expr = (BinderExpr)base.VisitBinderExpr(node);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();

      // We process triggers of quantifier expressions here, because otherwise the
      // substitutions for bound variables have to be leaked outside this procedure.
      if (node is QuantifierExpr quantifierExpr)
      {
        if (quantifierExpr.Triggers != null)
        {
          ((QuantifierExpr) expr).Triggers = this.VisitTrigger(quantifierExpr.Triggers);
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
      return (QuantifierExpr) this.VisitBinderExpr(node);
    }
  }
}