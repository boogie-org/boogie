using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class Action
  {
    public ActionDecl ActionDecl;
    public Action RefinedAction;
    public Implementation Impl;
    public List<AssertCmd> Gate;
    public HashSet<Variable> UsedGlobalVarsInGate;
    public HashSet<Variable> UsedGlobalVarsInAction;
    public HashSet<Variable> ModifiedGlobalVars;
    public Function InputOutputRelation;

    public List<AssertCmd> FirstGate;
    public Implementation FirstImpl;
    public List<AssertCmd> SecondGate;
    public Implementation SecondImpl;
    public Dictionary<Variable, Function> TriggerFunctions;

    public Action(CivlTypeChecker civlTypeChecker, ActionDecl actionDecl, Action refinedAction)
    {
      ActionDecl = actionDecl;
      RefinedAction = refinedAction;
      Impl = CreateDuplicateImplementation(actionDecl.Impl, actionDecl.Name);

      AddGateSufficiencyCheckerAndHoistAsserts(civlTypeChecker);

      ModifiedGlobalVars = new HashSet<Variable>(Impl.Proc.Modifies.Select(x => x.Decl));
      UsedGlobalVarsInGate = new HashSet<Variable>(VariableCollector.Collect(Gate).Where(x => x is GlobalVariable));
      UsedGlobalVarsInAction = new HashSet<Variable>(VariableCollector.Collect(Impl).Where(x => x is GlobalVariable));

      InputOutputRelation = ComputeInputOutputRelation(civlTypeChecker, Impl);

      AtomicActionDuplicator.SetupCopy(this, ref FirstGate, ref FirstImpl, "first_");
      AtomicActionDuplicator.SetupCopy(this, ref SecondGate, ref SecondImpl, "second_");
      DeclareTriggerFunctions();
    }

    public IEnumerable<Variable> UsedGlobalVars => UsedGlobalVarsInGate.Union(UsedGlobalVarsInAction);

    public IToken tok => ActionDecl.tok;

    public string Name => ActionDecl.Name;

    public LayerRange LayerRange => ActionDecl.LayerRange;

    public bool IsRightMover => ActionDecl.MoverType == MoverType.Right || ActionDecl.MoverType == MoverType.Both;

    public bool IsLeftMover => ActionDecl.MoverType == MoverType.Left || ActionDecl.MoverType == MoverType.Both;

    public bool IsConditionalLeftMover => IsLeftMover && ActionDecl.HasPreconditions;

    public bool IsUnconditionalLeftMover => IsLeftMover && !ActionDecl.HasPreconditions;

    public bool TriviallyCommutesWith(Action other)
    {
      return !this.ModifiedGlobalVars.Intersect(other.UsedGlobalVarsInAction).Any() &&
             !this.UsedGlobalVarsInAction.Intersect(other.ModifiedGlobalVars).Any();
    }

    public bool HasAssumeCmd => Impl.Blocks.Any(b => b.Cmds.Any(c => c is AssumeCmd));

    public IEnumerable<AssertCmd> GetGateAsserts(Substitution subst, string msg)
    {
      foreach (var gate in Gate)
      {
        AssertCmd cmd = subst != null ? (AssertCmd) Substituter.Apply(subst, gate) : new AssertCmd(gate.tok, gate.Expr);
        cmd.Description = new FailureOnlyDescription(msg);
        yield return cmd;
      }
    }

    public Expr GetTransitionRelation(CivlTypeChecker civlTypeChecker, HashSet<Variable> frame)
    {
      return TransitionRelationComputation.Refinement(civlTypeChecker, Impl, frame);
    }

    public IEnumerable<AssertCmd> Preconditions(int layerNum, Substitution subst)
    {
      var errorMessage = $"this precondition of {Name} could not be proved";
      var cmds = new List<AssertCmd>();
      ActionDecl.Requires.Where(req => req.Layers.Contains(layerNum)).ForEach(req =>
      {
        cmds.Add(CmdHelper.AssertCmd(req.tok, Substituter.Apply(subst, req.Condition), errorMessage));
      });
      foreach (var callCmd in ActionDecl.YieldRequires)
      {
        var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
        if (layerNum == yieldInvariant.Layer)
        {
          Substitution callFormalsToActuals = Substituter.SubstitutionFromDictionary(yieldInvariant.InParams
              .Zip(callCmd.Ins)
              .ToDictionary(x => x.Item1, x => x.Item2));
          yieldInvariant.Preserves.ForEach(req =>
            cmds.Add(CmdHelper.AssertCmd(req.tok,
                  Substituter.Apply(subst, Substituter.Apply(callFormalsToActuals, req.Condition)), errorMessage)));
        }
      }
      return cmds;
    }

    public static Implementation CreateDuplicateImplementation(Implementation impl, string name)
    {
      var duplicateImpl = new Duplicator().VisitImplementation(impl);
      var proc = duplicateImpl.Proc;
      duplicateImpl.Name = name;
      duplicateImpl.Attributes = null;
      // in case impl.Proc is ActionDecl, convert to Procedure
      duplicateImpl.Proc = new Procedure(proc.tok, name, proc.TypeParameters, proc.InParams,
        proc.OutParams, proc.IsPure, new List<Requires>(), new List<Requires>(), new List<Ensures>(), proc.Modifies);
      CivlUtil.AddInlineAttribute(duplicateImpl.Proc);
      return duplicateImpl;
    }

    public static void AddGateSufficiencyCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      decls.AddRange(gateSufficiencyCheckerDecls);
    }

    private static List<Declaration> gateSufficiencyCheckerDecls = new List<Declaration>();

    private void AddGateSufficiencyCheckerAndHoistAsserts(CivlTypeChecker civlTypeChecker)
    {
      if (ActionDecl.Asserts.Count == 0)
      {
        Gate = Wlp.HoistAsserts(Impl, civlTypeChecker.Options);
        return;
      }

      var gateSubst = Substituter.SubstitutionFromDictionary(ActionDecl.InParams
            .Zip(Impl.InParams)
            .ToDictionary(x => x.Item1, x => (Expr)Expr.Ident(x.Item2)));

      var checkerName = $"{Name}_GateSufficiencyChecker";
      var checkerImpl = new Duplicator().VisitImplementation(Impl);
      checkerImpl.Name = checkerName;
      checkerImpl.Attributes = null;

      var requires = new List<Requires>();
      var globalScope = VariableCollector.Collect(ActionDecl).Union(VariableCollector.Collect(ActionDecl.Impl)).OfType<GlobalVariable>();
      var scope = globalScope.Union(ActionDecl.InParams);
      var assumeExprs = civlTypeChecker.linearTypeChecker.DisjointnessExprForEachDomain(scope)
        .Union(civlTypeChecker.linearTypeChecker.MapWellFormedExpressions(scope));
      requires.AddRange(assumeExprs.Select(assumeExpr => new Requires(false, Substituter.Apply(gateSubst, assumeExpr))));
      requires.AddRange(ActionDecl.Asserts.Select(assertCmd =>
        new Requires(assertCmd.tok, false, Substituter.Apply(gateSubst, assertCmd.Expr),
                    null, CivlAttributes.ApplySubstitutionToPoolHints(gateSubst, assertCmd.Attributes))));

      var proc = checkerImpl.Proc;
      checkerImpl.Proc = new Procedure(proc.tok, checkerName, proc.TypeParameters, proc.InParams,
        proc.OutParams, proc.IsPure, requires, new List<Requires>(), new List<Ensures>(), proc.Modifies);
      gateSufficiencyCheckerDecls.AddRange(new Declaration[] { checkerImpl.Proc, checkerImpl });

      Wlp.HoistAsserts(Impl, civlTypeChecker.Options);
      
      Gate = ActionDecl.Asserts.Select(
        assertCmd => new AssertCmd(assertCmd.tok, Substituter.Apply(gateSubst, assertCmd.Expr),
                                  CivlAttributes.ApplySubstitutionToPoolHints(gateSubst, assertCmd.Attributes))).ToList();
    }

    private Function ComputeInputOutputRelation(CivlTypeChecker civlTypeChecker, Implementation impl)
    {
      var alwaysMap = new Dictionary<Variable, Expr>();
      var foroldMap = new Dictionary<Variable, Expr>();
      civlTypeChecker.program.GlobalVariables.ForEach(g =>
      {
        alwaysMap[g] = Expr.Ident(civlTypeChecker.BoundVariable(g.Name, g.TypedIdent.Type));
        foroldMap[g] = Expr.Ident(civlTypeChecker.BoundVariable($"old_{g.Name}", g.TypedIdent.Type));
      });
      impl.InParams.Concat(impl.OutParams).ForEach(v =>
      {
        alwaysMap[v] = Expr.Ident(VarHelper.Formal(v.Name, v.TypedIdent.Type, true));
      });
      var always = Substituter.SubstitutionFromDictionary(alwaysMap);
      var forold = Substituter.SubstitutionFromDictionary(foroldMap);
      var transitionRelationExpr =
        Substituter.ApplyReplacingOldExprs(always, forold,
          TransitionRelationComputation.Refinement(civlTypeChecker, impl, new HashSet<Variable>(ModifiedGlobalVars)));
      var gateExprs = Gate.Select(assertCmd =>
        Substituter.ApplyReplacingOldExprs(always, forold, ExprHelper.Old(assertCmd.Expr)));
      var transitionRelationInputs = impl.InParams.Concat(impl.OutParams)
        .Select(key => alwaysMap[key]).OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList();
      var inputOutputRelation = new Function(Token.NoToken, $"Civl_InputOutputRelation_{impl.Name}",
        new List<TypeVariable>(),
        transitionRelationInputs, VarHelper.Formal(TypedIdent.NoName, Type.Bool, false), null,
        new QKeyValue(Token.NoToken, "inline", new List<object>(), null));
      var existsVars = foroldMap.Values
        .Concat(alwaysMap.Keys.Where(key => key is GlobalVariable).Select(key => alwaysMap[key]))
        .OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList();
      var expr = Expr.And(gateExprs.Append(transitionRelationExpr));
      inputOutputRelation.Body = existsVars.Any() ? ExprHelper.ExistsExpr(existsVars, expr) : expr;
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, inputOutputRelation.Body);
      return inputOutputRelation;
    }
        
    private void DeclareTriggerFunctions()
    {
      TriggerFunctions = new Dictionary<Variable, Function>();
      foreach (var v in Impl.LocVars)
      {
        List<Variable> args = new List<Variable> {VarHelper.Formal(v.Name, v.TypedIdent.Type, true)};
        Variable result = VarHelper.Formal("r", Type.Bool, false);
        TriggerFunctions[v] = new Function(Token.NoToken, $"Trigger_{Impl.Name}_{v.Name}", args, result);
      }

      for (int i = 0; i < Impl.LocVars.Count; i++)
      {
        TriggerFunctions[FirstImpl.LocVars[i]] = TriggerFunctions[Impl.LocVars[i]];
        TriggerFunctions[SecondImpl.LocVars[i]] = TriggerFunctions[Impl.LocVars[i]];
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
      var liveVariableAnalysis = new AtomicActionLiveVariableAnalysis(Impl, options);
      liveVariableAnalysis.Compute();
      foreach (Variable v in Impl.LocVars)
      {
        var f = TriggerFunctions[v];
        program.AddTopLevelDeclaration(f);
        if (liveVariableAnalysis.IsLiveBefore(v, Impl.Blocks[0]))
        {
          var assume = CmdHelper.AssumeCmd(ExprHelper.FunctionCall(f, Expr.Ident(v)));
          Impl.Blocks[0].Cmds.Insert(0, assume);
        }
      }
      Impl.Blocks.ForEach(block =>
      {
        block.Cmds = block.Cmds.SelectMany(cmd =>
        {
          var newCmds = new List<Cmd> { cmd };
          if (cmd is HavocCmd havocCmd)
          {
            var liveHavocVars = new HashSet<Variable>(havocCmd.Vars.Select(x => x.Decl)
              .Where(v => liveVariableAnalysis.IsLiveAfter(v, havocCmd)));
            Impl.LocVars.Intersect(liveHavocVars).ForEach(v =>
            {
              newCmds.Add(CmdHelper.AssumeCmd(ExprHelper.FunctionCall(TriggerFunctions[v], Expr.Ident(v))));
            });
          }
          return newCmds;
        }).ToList();
      });
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

    public static void SetupCopy(Action action, ref List<AssertCmd> gateCopy, ref Implementation implCopy,
      string prefix)
    {
      var aad = new AtomicActionDuplicator(prefix, action);

      gateCopy = new List<AssertCmd>();
      foreach (AssertCmd assertCmd in action.Gate)
      {
        gateCopy.Add((AssertCmd) aad.Visit(assertCmd));
      }

      implCopy = aad.VisitImplementation(action.Impl);
    }

    private AtomicActionDuplicator(string prefix, Action action)
    {
      this.prefix = prefix;
      subst = new Dictionary<Variable, Expr>();
      bound = new Dictionary<Variable, Expr>();

      inParamsCopy = new List<Variable>();
      outParamsCopy = new List<Variable>();
      localsCopy = new List<Variable>();


      foreach (Variable x in action.Impl.InParams)
      {
        Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          true, x.Attributes);
        inParamsCopy.Add(xCopy);
        subst[x] = Expr.Ident(xCopy);
      }

      foreach (Variable x in action.Impl.OutParams)
      {
        Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          false, x.Attributes);
        outParamsCopy.Add(xCopy);
        subst[x] = Expr.Ident(xCopy);
      }

      foreach (Variable x in action.Impl.LocVars)
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

    public override Cmd VisitUnpackCmd(UnpackCmd node)
    {
      var retNode = (UnpackCmd)base.VisitUnpackCmd(node);
      retNode.ResetDesugaring();
      return retNode;
    }
  }
}