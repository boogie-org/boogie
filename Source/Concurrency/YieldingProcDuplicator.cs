using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Microsoft.Boogie
{
  public class YieldingProcDuplicator : Duplicator
  {
    /* This class creates duplicate copies of yielding procedures for a particular layer
     * rewriting calls to procedures that have been converted to atomic actions. 
     * Async calls are also rewritten so that the resulting copies are guaranteed not to
     * have any async calls.  The copy of yielding procedure X shares local variables of X.
     * This sharing is exploited when instrumenting the duplicates in the class
     * YieldingProcInstrumentation.
     */
    private CivlTypeChecker civlTypeChecker;
    private int layerNum;

    private Dictionary<Procedure, Procedure> procToDuplicate; /* Original -> Duplicate */
    private AbsyMap absyMap; /* Duplicate -> Original */
    private Dictionary<string, Procedure> asyncCallPreconditionCheckers;
    private Dictionary<string, Procedure> noRequiresPureProcedures;

    private LinearRewriter linearRewriter;

    private bool doRefinementCheck;

    public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, int layerNum, bool doRefinementCheck)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.layerNum = layerNum;
      this.procToDuplicate = [];
      this.absyMap = new AbsyMap();
      this.asyncCallPreconditionCheckers = [];
      this.noRequiresPureProcedures = [];
      this.linearRewriter = new LinearRewriter(civlTypeChecker);
      this.doRefinementCheck = doRefinementCheck;
    }

    #region Procedure duplication

    public override Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
    {
      if (!procToDuplicate.ContainsKey(node))
      {
        Debug.Assert(layerNum <= node.Layer);
        var procName = civlTypeChecker.AddNamePrefix($"{node.Name}_{layerNum}");
        if (doRefinementCheck)
        {
          procName = civlTypeChecker.AddNamePrefix($"{node.Name}_Refine_{layerNum}");
        }
        var requires = VisitRequiresSeq(node.Requires);
        var preserves = VisitRequiresSeq(node.Preserves);
        var ensures = VisitEnsuresSeq(node.Ensures);
        if (node.HasMoverType && layerNum == node.Layer && !doRefinementCheck)
        {
          requires = requires.Select(req => new Requires(req.tok, true, req.Condition, req.Comment, req.Attributes)).ToList();
          preserves = preserves.Select(req => new Requires(req.tok, true, req.Condition, req.Comment, req.Attributes)).ToList();
          ensures = ensures.Select(ens => new Ensures(ens.tok, true, ens.Condition, ens.Comment, ens.Attributes)).ToList();
        }
        requires.AddRange(preserves);
        ensures.AddRange(preserves.Select(req => new Ensures(req.tok, req.Free, req.Condition, req.Comment, req.Attributes)));
        var proc = new Procedure(
          node.tok,
          procName,
          [],
          VisitVariableSeq(node.InParams),
          VisitVariableSeq(node.OutParams),
          false,
          requires,
          [],
          ensures,
          (node.HasMoverType && node.Layer == layerNum
            ? node.ModifiedVars.Select(Expr.Ident)
            : civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v))).ToList()
          );
        procToDuplicate[node] = proc;
        absyMap[proc] = node;
      }
      return procToDuplicate[node];
    }

    public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
      requiresSeq = base.VisitRequiresSeq(requiresSeq);
      requiresSeq.RemoveAll(req => req.Condition.Equals(Expr.True));
      return requiresSeq;
    }

    public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
      ensuresSeq = base.VisitEnsuresSeq(ensuresSeq);
      ensuresSeq.RemoveAll(ens => ens.Condition.Equals(Expr.True));
      return ensuresSeq;
    }

    public override Requires VisitRequires(Requires node)
    {
      Requires requires = base.VisitRequires(node);
      if (node.Free)
      {
        return requires;
      }
      
      if (!node.Layers.Contains(layerNum))
      {
        requires.Condition = Expr.True;
      }

      return requires;
    }

    public override Ensures VisitEnsures(Ensures node)
    {
      Ensures ensures = base.VisitEnsures(node);
      if (node.Free)
      {
        return ensures;
      }
      
      if (!node.Layers.Contains(layerNum))
      {
        ensures.Condition = Expr.True;
      }

      return ensures;
    }

    #endregion

    #region Implementation duplication

    private YieldProcedureDecl enclosingYieldingProc;

    private List<Cmd> newCmdSeq;

    private Dictionary<string, Variable> addedLocalVariables;

    public override Implementation VisitImplementation(Implementation impl)
    {
      enclosingYieldingProc = (YieldProcedureDecl)impl.Proc;
      Debug.Assert(layerNum <= enclosingYieldingProc.Layer);

      addedLocalVariables = new Dictionary<string, Variable>();

      Implementation newImpl = base.VisitImplementation(impl);
      newImpl.Name = newImpl.Proc.Name;
      
      newImpl.LocVars.AddRange(addedLocalVariables.Values);

      absyMap[newImpl] = impl;
      return newImpl;
    }

    public override Block VisitBlock(Block node)
    {
      var block = base.VisitBlock(node);
      absyMap[block] = node;
      return block;
    }

    public override Cmd VisitAssertCmd(AssertCmd node)
    {
      var assertCmd = (AssertCmd)base.VisitAssertCmd(node);
      if (!node.Layers.Contains(layerNum))
      {
        assertCmd.Expr = Expr.True;
        return assertCmd;
      }
      return doRefinementCheck ? new AssumeCmd(node.tok, assertCmd.Expr, node.Attributes) : assertCmd;
    }

    public override Cmd VisitCallCmd(CallCmd call)
    {
      var newCall = (CallCmd) base.VisitCallCmd(call);
      absyMap[newCall] = call;
      return newCall;
    }

    public override Cmd VisitParCallCmd(ParCallCmd parCall)
    {
      var newParCall = (ParCallCmd) base.VisitParCallCmd(parCall);
      absyMap[newParCall] = parCall;
      foreach (var newCall in newParCall.CallCmds)
      {
        absyMap[newCall] = parCall;
      }
      return newParCall;
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      newCmdSeq = new List<Cmd>();
      foreach (var cmd in cmdSeq)
      {
        Cmd newCmd = (Cmd) Visit(cmd);
        if (newCmd is CallCmd)
        {
          ProcessCallCmd((CallCmd) newCmd);
        }
        else if (newCmd is ParCallCmd)
        {
          ProcessParCallCmd((ParCallCmd) newCmd);
        }
        else
        {
          newCmdSeq.Add(newCmd);
        }
      }
      return newCmdSeq;
    }

    private void AddParallelCall(List<CallCmd> callCmds, Absy absy)
    {
      var parCallCmd = new ParCallCmd(absy.tok, callCmds);
      absyMap[parCallCmd] = absyMap[absy];
      newCmdSeq.Add(parCallCmd);
    }

    private bool NeedsRefinementChecking(CallCmd callCmd)
    {
      if (callCmd.Proc is not YieldProcedureDecl yieldingProc)
      {
        return false;
      }
      if (layerNum != yieldingProc.Layer)
      {
        return false;
      }
      var visibleFormalNames = enclosingYieldingProc.VisibleFormals.Select(v =>v.Name);
      var visibleOutFormalNames = enclosingYieldingProc.OutParams.Select(v => v.Name).Intersect(visibleFormalNames);
      var callOutParamNames = callCmd.Outs.Select(ie => ie.Decl.Name);
      var isCallSkippable = yieldingProc.RefinedAction.ActionDecl == civlTypeChecker.SkipActionDecl &&
                            !visibleOutFormalNames.Intersect(callOutParamNames).Any();
      return !isCallSkippable;
    }

    // Create a duplicate of callCmd and update the outputs of callCmd to fresh local variables.
    // The duplicate call, returned by this method, is rewritten to call the refined action.
    // The original callCmd with rewritten outputs is used as normal in the parallel call that models
    // the yield after the call to the refined action.
    // Assumes constraining each output to the corresponding fresh output are added after the parallel call.
    private CallCmd PrepareCallCmd(CallCmd callCmd)
    {
      var copyCallCmd = (CallCmd)VisitCallCmd(callCmd);
      var freshOuts = new List<IdentifierExpr>();
      copyCallCmd.Outs.ForEach(ie => {
        if (!addedLocalVariables.TryGetValue(ie.Decl.Name, out Variable copyVar))
        {
          copyVar = civlTypeChecker.LocalVariable($"{ie.Decl.Name}_{callCmd.UniqueId}", ie.Type);
          addedLocalVariables[ie.Decl.Name] = copyVar;
        }
        freshOuts.Add(Expr.Ident(copyVar));
      });
      callCmd.Outs = freshOuts;
      return copyCallCmd;
    }

    private void ProcessCallCmd(CallCmd newCall)
    {
      if (newCall.Proc.IsPure)
      {
        var callLayerRange = newCall.LayerRange;
        if (callLayerRange.Contains(layerNum))
        {
          bool makeAssume = layerNum == enclosingYieldingProc.Layer && !doRefinementCheck;
          if (newCall.Proc is ActionDecl actionDecl)
          {
            var pureAction = civlTypeChecker.Action(actionDecl);
            newCall.Proc = pureAction.Impl.Proc;
            InjectGate(pureAction, newCall, makeAssume);
            newCmdSeq.Add(newCall);
          }
          else if (CivlPrimitives.IsPrimitive(newCall.Proc))
          {
            var cmds = linearRewriter.RewriteCallCmd(newCall).Select(cmd =>
              cmd is AssertCmd assertCmd && makeAssume
              ? new AssumeCmd(assertCmd.tok, assertCmd.Expr, assertCmd.Attributes)
              : cmd
            );
            newCmdSeq.AddRange(cmds);
          }
          else
          {
            DesugarPureCall(newCall);
          }
        }
        return;
      }

      if (newCall.Proc is YieldInvariantDecl yieldInvariant)
      {
        if (layerNum == yieldInvariant.Layer)
        {
          AddParallelCall([newCall], newCall);
        }
        return;
      }

      // handle calls to yielding procedures in the rest of this method
      var yieldingProc = (YieldProcedureDecl)newCall.Proc;

      if (newCall.IsAsync)
      {
        if (yieldingProc.Layer < layerNum)
        {
          Debug.Assert(!yieldingProc.HasMoverType);
          if (newCall.HasAttribute(CivlAttributes.SYNC))
          {
            // synchronize the called atomic action
            AddActionCall(newCall, yieldingProc);
          }
        }
        else
        {
          if (yieldingProc.HasMoverType && yieldingProc.Layer == layerNum)
          {
            // synchronize the called mover procedure
            AddDuplicateCall(newCall, false);
          }
          else if (doRefinementCheck)
          {
            Debug.Assert(!yieldingProc.HasMoverType);
          }
          else
          {
            DesugarAsyncCall(newCall);
          }
        }
        return;
      }

      // handle synchronous calls to yielding procedures
      if (yieldingProc.HasMoverType)
      {
        AddDuplicateCall(newCall, yieldingProc.Layer > layerNum);
      }
      else
      {
        if (yieldingProc.Layer < layerNum)
        {
          AddActionCall(newCall, yieldingProc);
        }
        else
        {
          if (doRefinementCheck && NeedsRefinementChecking(newCall))
          {
            AddParallelCall([], newCall);
            var copyCall = PrepareCallCmd(newCall);
            AddActionCall(copyCall, yieldingProc);
            AddDuplicateCall(newCall, true);
            newCmdSeq.AddRange(newCall.Outs.Zip(copyCall.Outs).Select(x => CmdHelper.AssumeCmd(Expr.Eq(x.First, x.Second))));
          }
          else
          {
            AddDuplicateCall(newCall, true);
          }
        }
        Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count);
      }
    }

    private void ProcessParCallCmd(ParCallCmd newParCall)
    {
      var callCmds = new List<CallCmd>();

      void AddParallelCallWrapper()
      {
        callCmds.Where(iter => iter.Proc is YieldProcedureDecl)
                .ForEach(iter => {
                  iter.Proc = procToDuplicate[iter.Proc];
                  iter.callee = iter.Proc.Name;
                });
        AddParallelCall(callCmds, newParCall);
      }

      void ProcessPendingCallCmds()
      {
        if (callCmds.Count == 0)
        {
          return;
        }
        CallCmd callCmd = doRefinementCheck ? callCmds.Find(NeedsRefinementChecking) : null;
        if (callCmd != null)
        {
          AddParallelCall([], callCmd);
          var copyCall = PrepareCallCmd(callCmd);
          AddActionCall(copyCall, (YieldProcedureDecl)callCmd.Proc);
          AddParallelCallWrapper();
          newCmdSeq.AddRange(callCmd.Outs.Zip(copyCall.Outs).Select(x => CmdHelper.AssumeCmd(Expr.Eq(x.First, x.Second))));
        }
        else
        {
          AddParallelCallWrapper();
        }
        callCmds = [];
      }

      foreach (var callCmd in newParCall.CallCmds)
      {
        if (callCmd.Proc is YieldProcedureDecl yieldingProc)
        {
          Debug.Assert(layerNum <= yieldingProc.Layer || !yieldingProc.HasMoverType);
          if (layerNum > yieldingProc.Layer || layerNum == yieldingProc.Layer && yieldingProc.HasMoverType)
          {
            ProcessPendingCallCmds();
            ProcessCallCmd(callCmd);
            continue;
          }
          callCmds.Add(callCmd);
        }
        else
        {
          var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
          if (layerNum == yieldInvariant.Layer)
          {
            callCmds.Add(callCmd);
          }
        }
      }

      ProcessPendingCallCmds();
    }

    private Action PrepareNewCall(CallCmd newCall, YieldProcedureDecl calleeActionProc)
    {
      var calleeRefinedAction = civlTypeChecker.Action(calleeActionProc.RefinedActionAtLayer(layerNum));

      newCall.IsAsync = false;
      newCall.Proc = calleeRefinedAction.Impl.Proc;
      newCall.callee = newCall.Proc.Name;

      // We drop the hidden parameters of the procedure from the call to the action.
      Debug.Assert(newCall.Ins.Count == calleeActionProc.InParams.Count);
      Debug.Assert(newCall.Outs.Count == calleeActionProc.OutParams.Count);
      var newIns = new List<Expr>();
      var newOuts = new List<IdentifierExpr>();
      for (int i = 0; i < calleeActionProc.InParams.Count; i++)
      {
        if (calleeActionProc.VisibleFormals.Contains(calleeActionProc.InParams[i]))
        {
          newIns.Add(newCall.Ins[i]);
        }
      }

      for (int i = 0; i < calleeActionProc.OutParams.Count; i++)
      {
        if (calleeActionProc.VisibleFormals.Contains(calleeActionProc.OutParams[i]))
        {
          newOuts.Add(newCall.Outs[i]);
        }
      }

      newCall.Ins = newIns;
      newCall.Outs = newOuts;

      return calleeRefinedAction;
    }

    private void AddActionCall(CallCmd newCall, YieldProcedureDecl calleeActionProc)
    {
      var calleeRefinedAction = PrepareNewCall(newCall, calleeActionProc);
      InjectPreconditions(calleeRefinedAction, newCall);
      InjectGate(calleeRefinedAction, newCall, !doRefinementCheck);
      newCmdSeq.Add(newCall);
    }

    private void InjectPreconditions(Action action, CallCmd callCmd)
    {
      if (!action.ActionDecl.HasPreconditions)
      {
        return;
      }
      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      for (int i = 0; i < action.ActionDecl.InParams.Count; i++)
      {
        map[action.ActionDecl.InParams[i]] = callCmd.Ins[i];
      }
      Substitution subst = Substituter.SubstitutionFromDictionary(map);
      newCmdSeq.AddRange(action.Preconditions(layerNum, subst));
    }

    private void InjectGate(Action action, CallCmd callCmd, bool assume)
    {
      if (action.Gate.Count == 0)
      {
        return;
      }

      Dictionary<Variable, Expr> map = [];
      for (int i = 0; i < action.Impl.InParams.Count; i++)
      {
        // Parameters come from the implementation that defines the action
        map[action.Impl.InParams[i]] = callCmd.Ins[i];
      }

      Substitution subst = Substituter.SubstitutionFromDictionary(map);

      // Important: Do not remove CommentCmd!
      // It separates the injected gate from yield assertions.
      newCmdSeq.Add(new CommentCmd("<<< injected gate"));
      foreach (AssertCmd assertCmd in action.Gate)
      {
        var expr = Substituter.Apply(subst, assertCmd.Expr);
        if (assume)
        {
          newCmdSeq.Add(new AssumeCmd(assertCmd.tok, expr));
        }
        else
        {
          newCmdSeq.Add(CmdHelper.AssertCmd(assertCmd.tok, expr,
            $"this gate of {action.Name} could not be proved"));
        }
      }

      newCmdSeq.Add(new CommentCmd("injected gate >>>"));
    }

    private void AddDuplicateCall(CallCmd newCall, bool makeParallel)
    {
      newCall.IsAsync = false;
      newCall.Proc = procToDuplicate[newCall.Proc];
      newCall.callee = newCall.Proc.Name;
      if (makeParallel)
      {
        AddParallelCall([newCall], newCall);
      }
      else
      {
        newCmdSeq.Add(newCall);
      }
    }

    private void DesugarAsyncCall(CallCmd newCall)
    {
      if (!asyncCallPreconditionCheckers.TryGetValue(newCall.Proc.Name, out Procedure checker))
      {
        checker = DeclHelper.Procedure(
          civlTypeChecker.AddNamePrefix($"AsyncCall_{newCall.Proc.Name}_{layerNum}"),
          newCall.Proc.InParams, newCall.Proc.OutParams,
          procToDuplicate[newCall.Proc].Requires, [], [], []);
        asyncCallPreconditionCheckers[newCall.Proc.Name] = checker;
      }
      newCall.IsAsync = false;
      newCall.Proc = checker;
      newCall.callee = newCall.Proc.Name;
      newCmdSeq.Add(newCall);
    }

    private void DesugarPureCall(CallCmd newCall)
    {
      if (doRefinementCheck)
      {
        if (!noRequiresPureProcedures.TryGetValue(newCall.Proc.Name, out Procedure checker))
        {
          checker = DeclHelper.Procedure(
            civlTypeChecker.AddNamePrefix($"NoRequires_{newCall.Proc.Name}_{layerNum}"),
            newCall.Proc.InParams, newCall.Proc.OutParams,
            [], [], new List<Ensures>(newCall.Proc.Ensures), []);
          noRequiresPureProcedures[newCall.Proc.Name] = checker;
        }
        newCall.IsAsync = false;
        newCall.Proc = checker;
        newCall.callee = newCall.Proc.Name;
      }
      newCmdSeq.Add(newCall);
    }

    #endregion

    public List<Declaration> Collect()
    {
      var decls = new List<Declaration>();
      decls.AddRange(procToDuplicate.Values);
      var newImpls = absyMap.Keys.OfType<Implementation>();
      decls.AddRange(newImpls);
      decls.AddRange(asyncCallPreconditionCheckers.Values);
      decls.AddRange(noRequiresPureProcedures.Values);
      decls.AddRange(YieldingProcInstrumentation.TransformImplementations(
        civlTypeChecker,
        layerNum,
        absyMap,
        doRefinementCheck));
      return decls;
    }
  }

  public class AbsyMap
  {
    private Dictionary<Absy, Absy> absyMap;

    public AbsyMap()
    {
      this.absyMap = [];
    }

    public Absy this[Absy absy]
    {
      get { return this.absyMap[absy]; }
      set { this.absyMap[absy] = value; }
    }

    public T Original<T>(T absy) where T : Absy
    {
      return (T)absyMap[absy];
    }

    public T OriginalOrInput<T>(T absy) where T : Absy
    {
      return absyMap.ContainsKey(absy) ? (T)absyMap[absy] : absy;
    }

    public IEnumerable<Absy> Keys
    {
      get { return absyMap.Keys; }
    }

    public bool ContainsKey(Absy key)
    {
      return absyMap.ContainsKey(key);
    }
  }
}