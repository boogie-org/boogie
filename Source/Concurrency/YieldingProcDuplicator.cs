using System;
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
     * YieldProcInstrumentation.
     */
    private CivlTypeChecker civlTypeChecker;
    private int layerNum;

    private Dictionary<Procedure, Procedure> procToDuplicate; /* Original -> Duplicate */
    private AbsyMap absyMap; /* Duplicate -> Original */
    private HashSet<Procedure> yieldingProcs;
    private Dictionary<string, Procedure> asyncCallPreconditionCheckers;

    private Dictionary<CallCmd, CallCmd> refinementCallCmds; // rewritten -> original
    private Dictionary<CallCmd, Block> refinementBlocks; // rewritten -> block

    private ConcurrencyOptions Options => civlTypeChecker.Options;

    public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, int layerNum)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.layerNum = layerNum;
      this.procToDuplicate = new Dictionary<Procedure, Procedure>();
      this.absyMap = new AbsyMap();
      this.yieldingProcs = new HashSet<Procedure>();
      this.asyncCallPreconditionCheckers = new Dictionary<string, Procedure>();
      this.refinementBlocks = new Dictionary<CallCmd, Block>();
    }

    #region Procedure duplication

    public override Procedure VisitProcedure(Procedure node)
    {
      Debug.Assert(civlTypeChecker.procToYieldingProc.ContainsKey(node));
      if (!procToDuplicate.ContainsKey(node))
      {
        YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[node];
        Debug.Assert(layerNum <= yieldingProc.upperLayer);

        Procedure proc = (Procedure) node.Clone();
        proc.Name = civlTypeChecker.AddNamePrefix($"{node.Name}_{layerNum}");
        proc.InParams = this.VisitVariableSeq(node.InParams);
        proc.OutParams = this.VisitVariableSeq(node.OutParams);
        proc.Requires = this.VisitRequiresSeq(node.Requires);
        proc.Ensures = this.VisitEnsuresSeq(node.Ensures);
        if (yieldingProc is MoverProc moverProc && yieldingProc.upperLayer == layerNum)
        {
          proc.Modifies = moverProc.modifiedGlobalVars.Select(g => Expr.Ident(g)).ToList();
        }
        else
        {
          proc.Modifies = civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList();
          yieldingProcs.Add(proc);
        }

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

      if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
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

      if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
      {
        ensures.Condition = Expr.True;
      }

      return ensures;
    }

    #endregion

    #region Implementation duplication

    private Implementation enclosingImpl;
    private YieldingProc enclosingYieldingProc;
    private bool IsRefinementLayer => layerNum == enclosingYieldingProc.upperLayer;
    private AtomicAction RefinedAction => ((ActionProc)enclosingYieldingProc).refinedAction;
    private List<Cmd> newCmdSeq;

    private Dictionary<CtorType, Variable> returnedPAs;

    private Variable ReturnedPAs(CtorType pendingAsyncType)
    {
      if (!returnedPAs.ContainsKey(pendingAsyncType))
      {
        returnedPAs[pendingAsyncType] = civlTypeChecker.LocalVariable($"returnedPAs_{pendingAsyncType.Decl.Name}",
          TypeHelper.MapType(pendingAsyncType, Type.Int));
      }
      return returnedPAs[pendingAsyncType];
    }

    private Variable CollectedPAs(CtorType pendingAsyncType)
    {
      if (!civlTypeChecker.implToPendingAsyncCollector[enclosingImpl].TryGetValue(pendingAsyncType, out var collectedPAs))
      {
        collectedPAs = civlTypeChecker.LocalVariable($"collectedPAs_{pendingAsyncType.Decl.Name}",
          TypeHelper.MapType(pendingAsyncType, Type.Int));
        civlTypeChecker.implToPendingAsyncCollector[enclosingImpl][pendingAsyncType] = collectedPAs;
      }
      return collectedPAs;
    }

    public override Implementation VisitImplementation(Implementation impl)
    {
      Debug.Assert(civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc));
      enclosingImpl = impl;
      enclosingYieldingProc = civlTypeChecker.procToYieldingProc[impl.Proc];
      Debug.Assert(layerNum <= enclosingYieldingProc.upperLayer);

      returnedPAs = new Dictionary<CtorType, Variable>();

      refinementCallCmds = new Dictionary<CallCmd, CallCmd>();
      Implementation newImpl = base.VisitImplementation(impl);
      newImpl.Name = newImpl.Proc.Name;

      foreach (var kv in refinementCallCmds)
      {
        var rewrittenCallCmd = kv.Key;
        var originalCallCmd = kv.Value;
        var actionProc = (ActionProc) civlTypeChecker.procToYieldingProc[originalCallCmd.Proc];
        newCmdSeq = new List<Cmd>();
        AddActionCall(originalCallCmd, actionProc);
        var block = BlockHelper.Block(
          civlTypeChecker.AddNamePrefix($"call_refinement_{refinementBlocks.Count}"),
          newCmdSeq,
          new List<Block>());
        refinementBlocks.Add(rewrittenCallCmd, block);
        newCmdSeq = null;
      }

      refinementCallCmds = null;
      
      newImpl.LocVars.AddRange(returnedPAs.Values);

      if (enclosingYieldingProc is ActionProc && RefinedAction.HasPendingAsyncs && IsRefinementLayer)
      {
        var assumeExpr = EmptyPendingAsyncMultisetExpr(CollectedPAs, RefinedAction.pendingAsyncs);
        newImpl.LocVars.AddRange(civlTypeChecker.implToPendingAsyncCollector[impl].Values.Except(impl.LocVars));
        newImpl.Blocks.First().Cmds.Insert(0, CmdHelper.AssumeCmd(assumeExpr));
      }

      absyMap[newImpl] = impl;
      return newImpl;
    }

    public override Block VisitBlock(Block node)
    {
      Block block = base.VisitBlock(node);
      absyMap[block] = node;
      return block;
    }

    public override Cmd VisitAssertCmd(AssertCmd node)
    {
      AssertCmd assertCmd = (AssertCmd) base.VisitAssertCmd(node);
      if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
      {
        assertCmd.Expr = Expr.True;
      }

      return assertCmd;
    }

    public override Cmd VisitCallCmd(CallCmd call)
    {
      CallCmd newCall = (CallCmd) base.VisitCallCmd(call);
      absyMap[newCall] = call;
      return newCall;
    }

    public override Cmd VisitParCallCmd(ParCallCmd parCall)
    {
      ParCallCmd newParCall = (ParCallCmd) base.VisitParCallCmd(parCall);
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

    private void ProcessCallCmd(CallCmd newCall)
    {
      if (civlTypeChecker.procToIntroductionAction.ContainsKey(newCall.Proc))
      {
        var introductionAction = civlTypeChecker.procToIntroductionAction[newCall.Proc];
        if (introductionAction.LayerNum == layerNum)
        {
          InjectGate(introductionAction, newCall);
          newCmdSeq.Add(newCall);
        }
        return;
      }

      if (civlTypeChecker.procToLemmaProc.ContainsKey(newCall.Proc))
      {
        if (civlTypeChecker.FindLayers(newCall.Attributes)[0] == layerNum)
        {
          newCmdSeq.Add(newCall);
        }
        return;
      }

      if (newCall.Proc is YieldInvariant yieldInvariant)
      {
        if (layerNum == yieldInvariant.LayerNum)
        {
          var parCallCmd = new ParCallCmd(newCall.tok, new List<CallCmd> {newCall});
          absyMap[parCallCmd] = absyMap[newCall];
          newCmdSeq.Add(parCallCmd);
        }
        return;
      }

      // handle calls to yielding procedures in the rest of this method
      YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[newCall.Proc];

      if (newCall.IsAsync)
      {
        if (yieldingProc.upperLayer < layerNum)
        {
          Debug.Assert(yieldingProc is ActionProc);
          var actionProc = (ActionProc)yieldingProc;
          if (newCall.HasAttribute(CivlAttributes.SYNC))
          {
            // synchronize the called atomic action
            AddActionCall(newCall, actionProc);
          }
          else if (IsRefinementLayer)
          {
            AddPendingAsync(newCall, actionProc);
          }
        }
        else
        {
          if (yieldingProc is MoverProc && yieldingProc.upperLayer == layerNum)
          {
            // synchronize the called mover procedure
            AddDuplicateCall(newCall, false);
          }
          else
          {
            DesugarAsyncCall(newCall);
            if (IsRefinementLayer)
            {
              Debug.Assert(yieldingProc is ActionProc);
              AddPendingAsync(newCall, (ActionProc)yieldingProc);
            }
          }
        }
        return;
      }

      // handle synchronous calls to yielding procedures
      if (yieldingProc is MoverProc moverProc)
      {
        AddDuplicateCall(newCall, moverProc.upperLayer > layerNum);
      }
      else if (yieldingProc is ActionProc actionProc)
      {
        if (actionProc.upperLayer < layerNum)
        {
          AddActionCall(newCall, actionProc);
        }
        else
        {
          if (IsRefinementLayer && layerNum == actionProc.upperLayer &&
              actionProc.RefinedActionAtLayer(layerNum) != civlTypeChecker.SkipAtomicAction)
          {
            refinementCallCmds[newCall] = (CallCmd) VisitCallCmd(newCall);
          }

          AddDuplicateCall(newCall, true);
        }

        Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count);
      }
      else
      {
        Debug.Assert(false);
      }
    }

    private void ProcessParCallCmd(ParCallCmd newParCall)
    {
      var callCmds = new List<CallCmd>();
      foreach (var callCmd in newParCall.CallCmds)
      {
        if (civlTypeChecker.procToYieldingProc.ContainsKey(callCmd.Proc))
        {
          var yieldingProc = civlTypeChecker.procToYieldingProc[callCmd.Proc];
          if (layerNum > yieldingProc.upperLayer && yieldingProc is ActionProc ||
              layerNum == yieldingProc.upperLayer && yieldingProc is MoverProc)
          {
            if (callCmds.Count > 0)
            {
              var parCallCmd = new ParCallCmd(newParCall.tok, callCmds);
              absyMap[parCallCmd] = absyMap[newParCall];
              newCmdSeq.Add(parCallCmd);
              callCmds = new List<CallCmd>();
            }

            ProcessCallCmd(callCmd);
            continue;
          }
        }

        if (procToDuplicate.ContainsKey(callCmd.Proc))
        {
          Debug.Assert(civlTypeChecker.procToYieldingProc.ContainsKey(callCmd.Proc));
          var yieldingProc = civlTypeChecker.procToYieldingProc[callCmd.Proc];
          if (yieldingProc is ActionProc actionProc)
          {
            if (IsRefinementLayer && layerNum == actionProc.upperLayer &&
                actionProc.RefinedActionAtLayer(layerNum) != civlTypeChecker.SkipAtomicAction)
            {
              refinementCallCmds[callCmd] = (CallCmd) VisitCallCmd(callCmd);
            }
          }

          callCmd.Proc = procToDuplicate[callCmd.Proc];
          callCmd.callee = callCmd.Proc.Name;
          callCmds.Add(callCmd);
        }
        else
        {
          var yieldInvariant = (YieldInvariant)callCmd.Proc;
          if (layerNum == yieldInvariant.LayerNum)
          {
            callCmds.Add(callCmd);
          }
        }
      }

      if (callCmds.Count > 0)
      {
        var parCallCmd = new ParCallCmd(newParCall.tok, callCmds);
        absyMap[parCallCmd] = absyMap[newParCall];
        newCmdSeq.Add(parCallCmd);
      }
    }

    private void AddActionCall(CallCmd newCall, ActionProc calleeActionProc)
    {
      var calleeRefinedAction = calleeActionProc.RefinedActionAtLayer(layerNum);

      newCall.IsAsync = false;
      newCall.Proc = calleeRefinedAction.proc;
      newCall.callee = newCall.Proc.Name;

      // We drop the hidden parameters of the procedure from the call to the action.
      Debug.Assert(newCall.Ins.Count == calleeActionProc.proc.InParams.Count);
      Debug.Assert(newCall.Outs.Count == calleeActionProc.proc.OutParams.Count);
      var newIns = new List<Expr>();
      var newOuts = new List<IdentifierExpr>();
      for (int i = 0; i < calleeActionProc.proc.InParams.Count; i++)
      {
        if (civlTypeChecker.FormalRemainsInAction(calleeActionProc, calleeActionProc.proc.InParams[i]))
        {
          newIns.Add(newCall.Ins[i]);
        }
      }

      for (int i = 0; i < calleeActionProc.proc.OutParams.Count; i++)
      {
        if (civlTypeChecker.FormalRemainsInAction(calleeActionProc, calleeActionProc.proc.OutParams[i]))
        {
          newOuts.Add(newCall.Outs[i]);
        }
      }

      newCall.Ins = newIns;
      newCall.Outs = newOuts;

      InjectGate(calleeRefinedAction, newCall, !IsRefinementLayer);
      newCmdSeq.Add(newCall);

      if (calleeRefinedAction.HasPendingAsyncs)
      {
        Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count - calleeRefinedAction.pendingAsyncs.Count);
        CollectReturnedPendingAsyncs(newCall, calleeRefinedAction);
      }
    }

    private void InjectGate(Action action, CallCmd callCmd, bool assume = false)
    {
      if (action.gate.Count == 0)
      {
        return;
      }

      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      for (int i = 0; i < action.proc.InParams.Count; i++)
      {
        // Parameters come from the implementation that defines the action
        map[action.impl.InParams[i]] = callCmd.Ins[i];
      }

      Substitution subst = Substituter.SubstitutionFromDictionary(map);

      // Important: Do not remove CommentCmd!
      // It separates the injected gate from yield assertions.
      newCmdSeq.Add(new CommentCmd("<<< injected gate"));
      foreach (AssertCmd assertCmd in action.gate)
      {
        var expr = Substituter.Apply(subst, assertCmd.Expr);
        if (assume)
        {
          newCmdSeq.Add(new AssumeCmd(assertCmd.tok, expr));
        }
        else
        {
          newCmdSeq.Add(CmdHelper.AssertCmd(assertCmd.tok, expr,
            $"this gate of {action.proc.Name} could not be proved"));
        }
      }

      newCmdSeq.Add(new CommentCmd("injected gate >>>"));
    }

    private void CollectReturnedPendingAsyncs(CallCmd newCall, AtomicAction calleeRefinedAction)
    {
      // Inject pending async collection
      newCall.Outs.AddRange(calleeRefinedAction.pendingAsyncs.Select(action => Expr.Ident(ReturnedPAs(action.pendingAsyncType))));
      if (!IsRefinementLayer)
      {
        return;
      }

      calleeRefinedAction.pendingAsyncs.Iter(action =>
      {
        if (RefinedAction.pendingAsyncs.Contains(action))
        {
          newCmdSeq.Add(CmdHelper.AssignCmd(CollectedPAs(action.pendingAsyncType),
            ExprHelper.FunctionCall(action.pendingAsyncAdd, Expr.Ident(CollectedPAs(action.pendingAsyncType)),
              Expr.Ident(ReturnedPAs(action.pendingAsyncType)))));
        }
        else
        {
          newCmdSeq.Add(CmdHelper.AssertCmd(newCall.tok,
            Expr.Eq(Expr.Ident(ReturnedPAs(action.pendingAsyncType)), ExprHelper.FunctionCall(action.pendingAsyncConst, Expr.Literal(0))),
            $"Pending asyncs to action {action.impl.Name} created by this call are not summarized"));
        }
      });
    }

    private Expr EmptyPendingAsyncMultisetExpr(Func<CtorType, Variable> pendingAsyncMultisets, IEnumerable<AsyncAction> asyncActions)
    {
      var returnExpr = Expr.And(asyncActions.Select(action =>
        Expr.Eq(Expr.Ident(pendingAsyncMultisets(action.pendingAsyncType)),
          ExprHelper.FunctionCall(action.pendingAsyncConst, Expr.Literal(0)))).ToList());
      returnExpr.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
      return returnExpr;
    }

    private void AddDuplicateCall(CallCmd newCall, bool makeParallel)
    {
      newCall.IsAsync = false;
      newCall.Proc = procToDuplicate[newCall.Proc];
      newCall.callee = newCall.Proc.Name;
      if (makeParallel)
      {
        var parCallCmd = new ParCallCmd(newCall.tok, new List<CallCmd> {newCall});
        absyMap[parCallCmd] = absyMap[newCall];
        newCmdSeq.Add(parCallCmd);
      }
      else
      {
        newCmdSeq.Add(newCall);
      }
    }

    private void DesugarAsyncCall(CallCmd newCall)
    {
      if (!asyncCallPreconditionCheckers.ContainsKey(newCall.Proc.Name))
      {
        asyncCallPreconditionCheckers[newCall.Proc.Name] = DeclHelper.Procedure(
          civlTypeChecker.AddNamePrefix($"AsyncCall_{newCall.Proc.Name}_{layerNum}"),
          newCall.Proc.InParams, newCall.Proc.OutParams,
          procToDuplicate[newCall.Proc].Requires, new List<IdentifierExpr>(), new List<Ensures>());
      }

      var asyncCallPreconditionChecker = asyncCallPreconditionCheckers[newCall.Proc.Name];
      newCall.IsAsync = false;
      newCall.Proc = asyncCallPreconditionChecker;
      newCall.callee = newCall.Proc.Name;
      newCmdSeq.Add(newCall);
    }

    private void AddPendingAsync(CallCmd newCall, ActionProc calleeProc)
    {
      AtomicAction calleeRefinedAction;
      if (calleeProc.upperLayer == enclosingYieldingProc.upperLayer)
      {
        calleeRefinedAction = calleeProc.refinedAction;
      }
      else
      {
        calleeRefinedAction = calleeProc.RefinedActionAtLayer(layerNum);
      }

      if (calleeRefinedAction == civlTypeChecker.SkipAtomicAction)
      {
        return;
      }

      var asyncAction = (AsyncAction)calleeRefinedAction;
      if (RefinedAction.pendingAsyncs.Contains(asyncAction))
      {
        Expr[] newIns = new Expr[calleeRefinedAction.proc.InParams.Count];
        for (int i = 0, j = 0; i < calleeProc.proc.InParams.Count; i++)
        {
          if (civlTypeChecker.FormalRemainsInAction(calleeProc, calleeProc.proc.InParams[i]))
          {
            newIns[j] = newCall.Ins[i];
            j++;
          }
        }
        var collectedPAs = CollectedPAs(asyncAction.pendingAsyncType);
        var pa = ExprHelper.FunctionCall(asyncAction.pendingAsyncCtor, newIns);
        var inc = Expr.Add(Expr.Select(Expr.Ident(collectedPAs), pa), Expr.Literal(1));
        var add = CmdHelper.AssignCmd(collectedPAs, Expr.Store(Expr.Ident(collectedPAs), pa, inc));
        newCmdSeq.Add(add);
      }
      else
      {
        newCmdSeq.Add(CmdHelper.AssertCmd(newCall.tok, Expr.False, "This pending async is not summarized"));
      }
    }

    #endregion

    public List<Declaration> Collect()
    {
      var decls = new List<Declaration>();
      decls.AddRange(procToDuplicate.Values);
      var newImpls = absyMap.Keys.OfType<Implementation>();
      decls.AddRange(newImpls);
      decls.AddRange(asyncCallPreconditionCheckers.Values);
      decls.AddRange(YieldingProcInstrumentation.TransformImplementations(
        civlTypeChecker,
        layerNum,
        absyMap,
        refinementBlocks));
      return decls;
    }
  }

  public class AbsyMap
  {
    private Dictionary<Absy, Absy> absyMap;

    public AbsyMap()
    {
      this.absyMap = new Dictionary<Absy, Absy>();
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