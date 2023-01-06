using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using System;

namespace Microsoft.Boogie
{
  public class TransitionRelationComputation
  {
    private CivlTypeChecker civlTypeChecker;
    private readonly Implementation first, second;
    private readonly Dictionary<Variable, Function> triggers;
    private readonly HashSet<Variable> frame;
    private readonly HashSet<Variable> allInParams, allOutParams, allLocVars;
    private readonly bool ignorePostState;

    private readonly string messagePrefix;
    private readonly CheckingContext checkingContext;

    private List<Cmd> path;
    private int transferIndex; // from first to second action

    private List<Expr> pathTranslations;

    private bool IsJoint => second != null;
    private ConcurrencyOptions Options => civlTypeChecker.Options;

    private IEnumerable<Variable> AllVariables =>
      frame.Union(allInParams).Union(allOutParams).Union(allLocVars).Distinct();

    private IEnumerable<Variable> PostStateVars => frame.Union(allOutParams).Distinct();

    private IEnumerable<Variable> PreStateVars => frame.Union(allInParams).Distinct();

    private TransitionRelationComputation(
      CivlTypeChecker civlTypeChecker,
      Implementation first, Implementation second,
      IEnumerable<Variable> frame, Dictionary<Variable, Function> triggers,
      bool ignorePostState,
      string messagePrefix)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.first = first;
      this.second = second;
      this.triggers = triggers;
      this.frame = new HashSet<Variable>(frame);
      this.ignorePostState = ignorePostState;

      allInParams = new HashSet<Variable>(first.InParams);
      allOutParams = new HashSet<Variable>(first.OutParams);
      allLocVars = new HashSet<Variable>(first.LocVars);
      if (IsJoint)
      {
        allInParams.UnionWith(second.InParams);
        allOutParams.UnionWith(second.OutParams);
        allLocVars.UnionWith(second.LocVars);
      }

      this.messagePrefix = messagePrefix;
      this.checkingContext = new CheckingContext(null);

      this.pathTranslations = new List<Expr>();
    }

    private static Expr ComputeTransitionRelation(
      CivlTypeChecker civlTypeChecker,
      Implementation first, Implementation second,
      IEnumerable<Variable> frame, Dictionary<Variable, Function> triggers,
      bool ignorePostState,
      string messagePrefix)
    {
      var trc = new TransitionRelationComputation(civlTypeChecker, first, second, frame, triggers, ignorePostState,
        messagePrefix);
      trc.EnumeratePaths();
      var transitionRelation = Expr.Or(trc.pathTranslations);
      transitionRelation.Resolve(new ResolutionContext(null, civlTypeChecker.Options) {StateMode = ResolutionContext.State.Two});
      transitionRelation.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
      return transitionRelation;
    }

    public static Expr Commutativity(
      CivlTypeChecker civlTypeChecker, 
      AtomicAction first, AtomicAction second,
      HashSet<Variable> frame)
    {
      var triggers = first.triggerFunctions.Union(second.triggerFunctions).ToDictionary(kv => kv.Key, kv => kv.Value);
      return ComputeTransitionRelation(
        civlTypeChecker,
        first.secondImpl, second.firstImpl,
        frame, triggers, false,
        string.Format("Transition relation of {0} ∘ {1}", first.proc.Name, second.proc.Name));
    }

    public static Expr Refinement(CivlTypeChecker civlTypeChecker, AtomicAction action, HashSet<Variable> frame)
    {
      return ComputeTransitionRelation(
        civlTypeChecker,
        action.impl, null,
        frame, null, false,
        string.Format("Transition relation of {0}", action.proc.Name));
    }

    public static Expr Cooperation(CivlTypeChecker civlTypeChecker, Action action, HashSet<Variable> frame)
    {
      return ComputeTransitionRelation(
        civlTypeChecker,
        action.impl, null,
        frame, null, true,
        string.Format("Cooperation expression of {0}", action.proc.Name));
    }

    private void EnumeratePaths()
    {
      path = new List<Cmd>();
      Debug.Assert(path.Count == 0);
      EnumeratePathsRec(first.Blocks[0], true);
      Debug.Assert(path.Count == 0);
    }

    private void EnumeratePathsRec(Block b, bool inFirst)
    {
      int pathSizeAtEntry = path.Count;

      foreach (Cmd cmd in b.Cmds)
      {
        if (cmd is UnpackCmd unpackCmd)
        {
          var stateCmd = (StateCmd)unpackCmd.GetDesugaring(civlTypeChecker.Options);
          path.AddRange(stateCmd.Cmds);
        }
        else 
        {
          path.Add(cmd);
        }
      }

      if (b.TransferCmd is ReturnCmd)
      {
        if (inFirst && IsJoint)
        {
          transferIndex = path.Count;
          EnumeratePathsRec(second.Blocks[0], false);
        }
        else
        {
          AddPath();
        }
      }
      else
      {
        GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
        foreach (Block target in gotoCmd.labelTargets)
        {
          EnumeratePathsRec(target, inFirst);
        }
      }

      Debug.Assert(path.Count >= pathSizeAtEntry);
      path.RemoveRange(pathSizeAtEntry, path.Count - pathSizeAtEntry);
    }

    private void AddPath()
    {
      var pathTranslation = new PathTranslation(this);
      pathTranslations.Add(pathTranslation.TransitionRelationExpr);

      if (civlTypeChecker.Options.WarnNotEliminatedVars)
      {
        var quantifiedVars = pathTranslation.GetQuantifiedOriginalVariables();
        if (quantifiedVars.Any())
        {
          checkingContext.Warning(Token.NoToken,
            string.Format("{0}: could not eliminate variables {{{1}}} on some path",
              messagePrefix, string.Join(", ", quantifiedVars)));
        }
      }
    }

    private class PathTranslation
    {
      private readonly TransitionRelationComputation trc;

      private List<Assignment> assignments;
      private List<Expr> assumes;

      private Dictionary<Variable, List<Variable>> varCopies;
      private Dictionary<Variable, Variable> copyToOriginalVar;
      private Dictionary<Variable, Expr> varToExpr;
      private List<Expr> pathExprs;

      private Dictionary<Variable, Variable> frameIntermediateCopy;

      private Dictionary<Variable, Variable> existsVarMap;

      public Expr TransitionRelationExpr;

      private const string copierFormat = "{0}#{1}";

      private ConcurrencyOptions Options => trc.Options;

      class Assignment
      {
        public Variable Var { get; set; }
        public Expr Expr { get; set; }

        public Assignment(Variable var, Expr expr)
        {
          Var = var;
          Expr = expr;
        }
      }

      public PathTranslation(TransitionRelationComputation trc)
      {
        this.trc = trc;

        SetupVarCopies();
        IntroduceIntermediateVars();
        SetDefinedVariables();
        EliminateIntermediateVariables();
        ComputeTransitionRelationExpr();
      }

      private void SetupVarCopies()
      {
        varCopies = new Dictionary<Variable, List<Variable>>();
        copyToOriginalVar = new Dictionary<Variable, Variable>();

        foreach (var v in trc.AllVariables)
        {
          varCopies[v] = new List<Variable>();
          MakeNewCopy(v);
        }
      }

      private void MakeNewCopy(Variable v)
      {
        int id = varCopies[v].Count;
        var copyVar = trc.civlTypeChecker.LocalVariable(string.Format(copierFormat, v.Name, id), v.TypedIdent.Type);
        copyVar.Attributes = v.Attributes;
        varCopies[v].Add(copyVar);
        copyToOriginalVar[copyVar] = v;
      }

      private IEnumerable<Variable> AllIntroducedVariables =>
        varCopies.SelectMany(x => x.Value);

      private Dictionary<Variable, Variable> LatestCopies(IEnumerable<Variable> vars)
      {
        return vars.ToDictionary(v => v, v => varCopies[v].Last());
      }

      private Dictionary<Variable, Variable> LatestCopies()
      {
        return LatestCopies(trc.AllVariables);
      }

      private void PopulateIntermediateFrameCopy()
      {
        frameIntermediateCopy = LatestCopies(trc.frame);
      }

      private void IntroduceIntermediateVars()
      {
        var oldSub = SubstitutionHelper.FromVariableMap(LatestCopies(trc.PreStateVars));
        assignments = new List<Assignment>();
        assumes = new List<Expr>();
        for (int k = 0; k < trc.path.Count; k++)
        {
          if (trc.IsJoint && k == trc.transferIndex)
          {
            PopulateIntermediateFrameCopy();
            oldSub = SubstitutionHelper.FromVariableMap(LatestCopies(trc.PreStateVars));
          }

          Cmd cmd = trc.path[k];
          if (cmd is AssignCmd assignCmd)
          {
            assignCmd = assignCmd.AsSimpleAssignCmd;
            var preState = LatestCopies();
            foreach (var v in assignCmd.Lhss)
            {
              MakeNewCopy(v.DeepAssignedVariable);
            }

            var postState = LatestCopies();

            if (QKeyValue.FindBoolAttribute(assignCmd.Attributes, CivlAttributes.BACKWARD))
            {
              var tmp = preState;
              preState = postState;
              postState = tmp;
            }

            var rhsSub = SubstitutionHelper.FromVariableMap(preState);

            for (int i = 0; i < assignCmd.Lhss.Count; i++)
            {
              var var = postState[assignCmd.Lhss[i].DeepAssignedVariable];
              var expr = Substituter.ApplyReplacingOldExprs(rhsSub, oldSub, assignCmd.Rhss[i]);
              assignments.Add(new Assignment(var, expr));
            }
          }
          else if (cmd is AssumeCmd assumeCmd)
          {
            var sub = SubstitutionHelper.FromVariableMap(LatestCopies());
            assumes.Add(Substituter.ApplyReplacingOldExprs(sub, oldSub, assumeCmd.Expr));
          }
          else if (cmd is HavocCmd havocCmd)
          {
            foreach (var v in havocCmd.Vars)
            {
              MakeNewCopy(v.Decl);
            }
          }
          else
          {
            Debug.Assert(false);
          }
        }

        // In case there were no commands from the second action
        if (trc.IsJoint && trc.path.Count == trc.transferIndex)
        {
          PopulateIntermediateFrameCopy();
        }
      }

      private void SetDefinedVariables()
      {
        varToExpr = new Dictionary<Variable, Expr>();
        foreach (var v in trc.PreStateVars)
        {
          var vFirst = varCopies[v][0];
          varToExpr[vFirst] = Expr.Ident(vFirst);
        }

        if (!trc.ignorePostState)
        {
          foreach (var v in trc.PostStateVars)
          {
            var vLast = varCopies[v].Last();
            varToExpr[vLast] = Expr.Ident(vLast);
          }
        }
      }

      private void EliminateIntermediateVariables()
      {
        TryElimination(Enumerable.Empty<Variable>());
        TryElimination(trc.allLocVars.Select(v => varCopies[v][0]));
        TryElimination(trc.allLocVars.Where(v => v.FindAttribute("pool") != null).SelectMany(v => varCopies[v]));

        if (trc.ignorePostState)
        {
          TryElimination(trc.PostStateVars);
        }
        else if (trc.IsJoint)
        {
          TryElimination(frameIntermediateCopy.Values.Except(varToExpr.Keys));
        }
      }

      private void TryElimination(IEnumerable<Variable> extraDefinedVariables)
      {
        bool Defined(Variable v) => varToExpr.ContainsKey(v) || extraDefinedVariables.Contains(v);
        bool changed;
        do
        {
          changed = false;
          var remainingAssignments = new List<Assignment>();
          foreach (var assignment in assignments)
          {
            if (!Defined(assignment.Var) &&
                VariableCollector.Collect(assignment.Expr).Intersect(AllIntroducedVariables).All(Defined))
            {
              varToExpr[assignment.Var] = SubstitutionHelper.Apply(varToExpr, assignment.Expr);
              changed = true;
            }
            else
            {
              remainingAssignments.Add(assignment);
            }
          }

          Substitution sub = Substituter.SubstitutionFromDictionary(varToExpr);
          foreach (var assignment in remainingAssignments)
          {
            assignment.Expr = Substituter.Apply(sub, assignment.Expr);
          }

          assignments = remainingAssignments;
          assumes = SubstitutionHelper.Apply(sub, assumes).ToList();
        } while (changed);
      }

      private void ComputeTransitionRelationExpr()
      {
        CalculatePathExpression();
        AddBoundVariablesForRemainingVars();
        ReplacePreOrPostStateVars();
        TransitionRelationExpr = Expr.And(pathExprs);

        if (existsVarMap.Any())
        {
          Trigger trigger = null;
          if (trc.IsJoint)
          {
            var exprs = new List<Expr>();
            foreach (var v in existsVarMap.Keys)
            {
              var orig = copyToOriginalVar[v];
              if (v == varCopies[orig].First() && trc.triggers.ContainsKey(orig))
              {
                var f = trc.triggers[orig];
                exprs.Add(ExprHelper.FunctionCall(f, Expr.Ident(existsVarMap[v])));
              }
            }

            if (exprs.Count == existsVarMap.Count)
            {
              trigger = new Trigger(Token.NoToken, true, exprs);
            }
          }

          TransitionRelationExpr = ExprHelper.ExistsExpr(
            existsVarMap.Values.ToList<Variable>(), trigger, TransitionRelationExpr);
        }
      }

      private void CalculatePathExpression()
      {
        pathExprs = new List<Expr>();
        foreach (var expr in assumes)
        {
          ExprHelper.FlattenAnd(expr, pathExprs);
        }

        foreach (var assignment in assignments)
        {
          // If a variable is forward and backward assigned, we might
          // have a substitution for the lhs here.
          if (!varToExpr.TryGetValue(assignment.Var, out Expr x))
          {
            x = Expr.Ident(assignment.Var);
          }

          pathExprs.Add(Expr.Eq(x, assignment.Expr));
        }
      }

      private IEnumerable<Variable> NotEliminatedVars =>
        pathExprs.SelectMany(x => VariableCollector.Collect(x)).Intersect(AllIntroducedVariables)
          .Except(varToExpr.Keys);

      private void AddBoundVariablesForRemainingVars()
      {
        existsVarMap = NotEliminatedVars.ToDictionary(v => v, v => (Variable) VarHelper.BoundVariable(v.Name, v.TypedIdent.Type));
        existsVarMap.Iter(kv =>
        {
          kv.Value.Attributes = copyToOriginalVar[kv.Key].Attributes;
        });
        pathExprs = SubstitutionHelper.Apply(existsVarMap, pathExprs).ToList();
      }

      private void ReplacePreOrPostStateVars()
      {
        var sub = new Dictionary<Variable, Expr>();

        foreach (var v in trc.allInParams)
        {
          sub[varCopies[v][0]] = Expr.Ident(v);
        }

        foreach (var v in trc.frame)
        {
          sub[varCopies[v][0]] = ExprHelper.Old(Expr.Ident(v));
        }

        if (!trc.ignorePostState)
        {
          foreach (var v in trc.PostStateVars)
          {
            var lastCopy = varCopies[v].Last();
            if (sub.ContainsKey(lastCopy))
            {
              Debug.Assert(trc.frame.Contains(v) && lastCopy == varCopies[v][0]);
              pathExprs.Add(Expr.Eq(Expr.Ident(v), sub[lastCopy]));
            }

            // In case of conflict we prefer "v" instead of "old(v)"
            sub[lastCopy] = Expr.Ident(v);
          }
        }

        pathExprs = SubstitutionHelper.Apply(sub, pathExprs).ToList();
      }

      public IEnumerable<Variable> GetQuantifiedOriginalVariables()
      {
        return existsVarMap.Keys.Select(x => copyToOriginalVar[x]).Distinct();
      }
    }
  }

  public static class BackwardAssignmentSubstituter
  {
    public static void SubstituteBackwardAssignments(IEnumerable<AtomicAction> actions)
    {
      foreach (var action in actions)
      {
        SubstituteBackwardAssignments(action);
      }
    }

    private static void SubstituteBackwardAssignments(AtomicAction action)
    {
      foreach (Block block in action.impl.Blocks)
      {
        List<Cmd> cmds = new List<Cmd>();
        foreach (Cmd cmd in block.cmds)
        {
          if (cmd is AssignCmd _assignCmd &&
              QKeyValue.FindBoolAttribute(_assignCmd.Attributes, CivlAttributes.BACKWARD))
          {
            AssignCmd assignCmd = _assignCmd.AsSimpleAssignCmd;
            var lhss = assignCmd.Lhss;
            var rhss = assignCmd.Rhss;
            var rhssVars = rhss.SelectMany(x => VariableCollector.Collect(x));
            var lhssVars = lhss.SelectMany(x => VariableCollector.Collect(x));
            if (rhssVars.Intersect(lhssVars).Any())
            {
              // TODO
              throw new NotImplementedException("Substitution of backward assignment where lhs appears on rhs");
            }
            else
            {
              List<Expr> assumeExprs = new List<Expr>();
              for (int k = 0; k < lhss.Count; k++)
              {
                assumeExprs.Add(Expr.Eq(lhss[k].AsExpr, rhss[k]));
              }

              cmds.Add(CmdHelper.AssumeCmd(Expr.And(assumeExprs)));
              cmds.Add(CmdHelper.HavocCmd(lhss.Select(x => x.DeepAssignedIdentifier).ToList()));
            }
          }
          else
          {
            cmds.Add(cmd);
          }
        }

        block.cmds = cmds;
      }
    }
  }
}