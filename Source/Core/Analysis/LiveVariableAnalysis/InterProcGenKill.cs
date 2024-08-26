using System.Collections.Generic;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  public class InterProcGenKill
  {
    private CoreOptions options;
    Program /*!*/ program;

    Dictionary<string /*!*/, ImplementationControlFlowGraph /*!*/> /*!*/
      procICFG;

    Dictionary<string /*!*/, Procedure /*!*/> /*!*/
      name2Proc;

    Dictionary<string /*!*/, List<WorkItem /*!*/> /*!*/> /*!*/
      callers;

    Graph<string /*!*/> /*!*/
      callGraph;

    Dictionary<string /*!*/, int> /*!*/
      procPriority;

    int maxBlocksInProc;

    WorkList /*!*/
      workList;

    Implementation /*!*/
      mainImpl;

    static Dictionary<string /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
      varsLiveAtExit = new Dictionary<string /*!*/, HashSet<Variable /*!*/> /*!*/>();

    static Dictionary<string /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
      varsLiveAtEntry = new Dictionary<string /*!*/, HashSet<Variable /*!*/> /*!*/>();

    static Dictionary<string /*!*/, GenKillWeight /*!*/> /*!*/
      varsLiveSummary = new Dictionary<string /*!*/, GenKillWeight /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(workList != null);
      Contract.Invariant(mainImpl != null);
      Contract.Invariant(program != null);
      Contract.Invariant(cce.NonNullDictionaryAndValues(procICFG));
      Contract.Invariant(cce.NonNullDictionaryAndValues(name2Proc));
      Contract.Invariant(cce.NonNullDictionaryAndValues(callers) &&
                         Contract.ForAll(callers.Values, v => cce.NonNullElements(v)));
      Contract.Invariant(cce.NonNullElements(callGraph.Nodes));
      Contract.Invariant(procPriority != null);
      Contract.Invariant(cce.NonNullDictionaryAndValues(varsLiveAtEntry));
      Contract.Invariant(cce.NonNullDictionaryAndValues(varsLiveAtExit) &&
                         Contract.ForAll(varsLiveAtExit.Values, v => cce.NonNullElements(v)));
      Contract.Invariant(cce.NonNullDictionaryAndValues(varsLiveSummary));
      Contract.Invariant(cce.NonNullDictionaryAndValues(weightCacheAfterCall));
      Contract.Invariant(cce.NonNullDictionaryAndValues(weightCacheBeforeCall));
    }


    [NotDelayed]
    public InterProcGenKill(Implementation impl, Program program, CoreOptions options)
    {
      Contract.Requires(program != null);
      Contract.Requires(impl != null);
      this.program = program;
      this.options = options;
      procICFG = new Dictionary<string /*!*/, ImplementationControlFlowGraph /*!*/>();
      name2Proc = new Dictionary<string /*!*/, Procedure /*!*/>();
      workList = new WorkList();
      this.callers = new Dictionary<string /*!*/, List<WorkItem /*!*/> /*!*/>();
      this.callGraph = new Graph<string /*!*/>();
      this.procPriority = new Dictionary<string /*!*/, int>();
      this.maxBlocksInProc = 0;
      this.mainImpl = impl;

      Dictionary<string /*!*/, Implementation /*!*/> /*!*/
        name2Impl = new Dictionary<string /*!*/, Implementation /*!*/>();
      varsLiveAtExit.Clear();
      varsLiveAtEntry.Clear();
      varsLiveSummary.Clear();

      foreach (var decl in program.TopLevelDeclarations)
      {
        Contract.Assert(decl != null);
        if (decl is Implementation)
        {
          Implementation /*!*/
            imp = (Implementation /*!*/) cce.NonNull(decl);
          name2Impl[imp.Name] = imp;
        }
        else if (decl is Procedure)
        {
          Procedure /*!*/
            proc = cce.NonNull(decl as Procedure);
          name2Proc[proc.Name] = proc;
        }
      }

      ImplementationControlFlowGraph /*!*/
        mainImplementationControlFlowGraph = new ImplementationControlFlowGraph(this.options, mainImpl);
      Contract.Assert(mainImplementationControlFlowGraph != null);
      procICFG.Add(mainImplementationControlFlowGraph.impl.Name, mainImplementationControlFlowGraph);
      callGraph.AddSource(mainImplementationControlFlowGraph.impl.Name);

      List<ImplementationControlFlowGraph /*!*/> /*!*/
        procsToConsider = new List<ImplementationControlFlowGraph /*!*/>();
      procsToConsider.Add(mainImplementationControlFlowGraph);

      while (procsToConsider.Count != 0)
      {
        ImplementationControlFlowGraph /*!*/
          p = procsToConsider[0];
        Contract.Assert(p != null);
        procsToConsider.RemoveAt(0);

        foreach (string /*!*/ callee in p.procsCalled.Keys)
        {
          Contract.Assert(callee != null);
          if (!name2Impl.ContainsKey(callee))
          {
            continue;
          }

          callGraph.AddEdge(p.impl.Name, callee);

          if (maxBlocksInProc < p.nodes.Count)
          {
            maxBlocksInProc = p.nodes.Count;
          }

          if (!callers.ContainsKey(callee))
          {
            callers.Add(callee, new List<WorkItem /*!*/>());
          }

          foreach (Block /*!*/ b in p.procsCalled[callee])
          {
            Contract.Assert(b != null);
            callers[callee].Add(new WorkItem(p, b));
          }

          if (procICFG.ContainsKey(callee))
          {
            continue;
          }

          ImplementationControlFlowGraph /*!*/
            ncfg = new ImplementationControlFlowGraph(this.options, name2Impl[callee]);
          Contract.Assert(ncfg != null);
          procICFG.Add(callee, ncfg);
          procsToConsider.Add(ncfg);
        }
      }

      callGraph.TarjanTopSort(out var acyclic, out var sortedNodes);

      Contract.Assert(acyclic);

      int cnt = 0;
      for (int i = sortedNodes.Count - 1; i >= 0; i--)
      {
        string s = sortedNodes[i];
        if (s == null)
        {
          continue;
        }

        procPriority.Add(s, cnt);
        cnt++;
      }
    }

    public static HashSet<Variable /*!*/> /*!*/ GetVarsLiveAtExit(Implementation impl, Program prog)
    {
      Contract.Requires(prog != null);
      Contract.Requires(impl != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
      if (varsLiveAtExit.ContainsKey(impl.Name))
      {
        return varsLiveAtExit[impl.Name];
      }

      // Return default: all globals and out params
      HashSet<Variable /*!*/> /*!*/
        lv = new HashSet<Variable /*!*/>();
      foreach (Variable /*!*/ v in prog.GlobalVariables)
      {
        Contract.Assert(v != null);
        lv.Add(v);
      }

      foreach (Variable /*!*/ v in impl.OutParams)
      {
        Contract.Assert(v != null);
        lv.Add(v);
      }

      return lv;
    }

    public static HashSet<Variable /*!*/> /*!*/ GetVarsLiveAtEntry(Implementation impl, Program prog)
    {
      Contract.Requires(prog != null);
      Contract.Requires(impl != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
      if (varsLiveAtEntry.ContainsKey(impl.Name))
      {
        return varsLiveAtEntry[impl.Name];
      }

      // Return default: all globals and in params
      HashSet<Variable /*!*/> /*!*/
        lv = new HashSet<Variable /*!*/>();
      foreach (Variable /*!*/ v in prog.GlobalVariables)
      {
        Contract.Assert(v != null);
        lv.Add(v);
      }

      foreach (Variable /*!*/ v in impl.InParams)
      {
        Contract.Assert(v != null);
        lv.Add(v);
      }

      return lv;
    }

    public static bool HasSummary(string name)
    {
      Contract.Requires(name != null);
      return varsLiveSummary.ContainsKey(name);
    }

    public static HashSet<Variable /*!*/> /*!*/
      PropagateLiveVarsAcrossCall(CoreOptions options, CallCmd cmd, HashSet<Variable /*!*/> /*!*/ lvAfter)
    {
      Contract.Requires(cmd != null);
      Contract.Requires(cce.NonNullElements(lvAfter));
      Contract.Ensures(cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
      Procedure /*!*/
        proc = cce.NonNull(cmd.Proc);
      if (varsLiveSummary.ContainsKey(proc.Name))
      {
        GenKillWeight /*!*/
          w1 = getWeightBeforeCall(cmd);
        Contract.Assert(w1 != null);
        GenKillWeight /*!*/
          w2 = varsLiveSummary[proc.Name];
        Contract.Assert(w2 != null);
        GenKillWeight /*!*/
          w3 = getWeightAfterCall(cmd);
        Contract.Assert(w3 != null);
        GenKillWeight /*!*/
          w = GenKillWeight.extend(w1, GenKillWeight.extend(w2, w3));
        Contract.Assert(w != null);
        return w.getLiveVars(lvAfter);
      }

      HashSet<Variable /*!*/> /*!*/
        ret = new HashSet<Variable /*!*/>();
      ret.UnionWith(lvAfter);
      new LiveVariableAnalysis(options).Propagate(cmd, ret);
      return ret;
    }

    class WorkItem
    {
      public ImplementationControlFlowGraph /*!*/
        cfg;

      public Block /*!*/
        block;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(cfg != null);
        Contract.Invariant(block != null);
      }


      public WorkItem(ImplementationControlFlowGraph cfg, Block block)
      {
        Contract.Requires(block != null);
        Contract.Requires(cfg != null);
        this.cfg = cfg;
        this.block = block;
      }

      public GenKillWeight getWeightAfter()
      {
        Contract.Ensures(Contract.Result<GenKillWeight>() != null);
        return cfg.weightAfter[block];
      }

      public bool setWeightBefore(GenKillWeight w)
      {
        Contract.Requires(w != null);
        GenKillWeight /*!*/
          prev = cfg.weightBefore[block];
        Contract.Assert(prev != null);
        GenKillWeight /*!*/
          curr = GenKillWeight.combine(w, prev);
        Contract.Assert(curr != null);
        if (GenKillWeight.isEqual(prev, curr))
        {
          return false;
        }

        cfg.weightBefore[block] = curr;
        return true;
      }

      [Pure]
      [Reads(ReadsAttribute.Reads.Nothing)]
      public override bool Equals(object other)
      {
        WorkItem /*!*/
          wi = (WorkItem /*!*/) cce.NonNull(other);
        return (wi.cfg == cfg && wi.block == block);
      }

      [Pure]
      public override int GetHashCode()
      {
        return 0;
      }

      public string getLabel()
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return cfg.impl.Name + "::" + block.Label;
      }
    }

    private void AddToWorkList(WorkItem wi)
    {
      Contract.Requires(wi != null);
      int i = procPriority[wi.cfg.impl.Name];
      int j = wi.cfg.getPriority(wi.block);
      int priority = (i * maxBlocksInProc) + j;

      workList.Add(wi, priority);
    }

    private void AddToWorkListReverse(WorkItem wi)
    {
      Contract.Requires(wi != null);
      int i = procPriority[wi.cfg.impl.Name];
      int j = wi.cfg.getPriority(wi.block);
      int priority = (procPriority.Count - i) * maxBlocksInProc + j;
      workList.Add(wi, priority);
    }

    class WorkList
    {
      SortedList<int, int> /*!*/
        priorities;

      HashSet<string /*!*/> /*!*/
        labels;

      Dictionary<int, List<WorkItem /*!*/> /*!*/> /*!*/
        workList;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(priorities != null);
        Contract.Invariant(cce.NonNullElements(labels));
        Contract.Invariant(cce.NonNullDictionaryAndValues(workList) &&
                           Contract.ForAll(workList.Values, v => cce.NonNullElements(v)));
      }


      public WorkList()
      {
        labels = new HashSet<string /*!*/>();
        priorities = new SortedList<int, int>();
        workList = new Dictionary<int, List<WorkItem /*!*/> /*!*/>();
      }

      public void Add(WorkItem wi, int priority)
      {
        Contract.Requires(wi != null);
        string /*!*/
          lab = wi.getLabel();
        Contract.Assert(lab != null);
        if (labels.Contains(lab))
        {
          // Already on worklist
          return;
        }

        labels.Add(lab);
        if (!workList.ContainsKey(priority))
        {
          workList.Add(priority, new List<WorkItem /*!*/>());
        }

        workList[priority].Add(wi);
        if (!priorities.ContainsKey(priority))
        {
          priorities.Add(priority, 0);
        }

        priorities[priority] = priorities[priority] + 1;
      }

      public WorkItem Get()
      {
        Contract.Ensures(Contract.Result<WorkItem>() != null);
        // Get minimum priority
        int p = cce.NonNull(priorities.Keys)[0];
        priorities[p] = priorities[p] - 1;
        if (priorities[p] == 0)
        {
          priorities.Remove(p);
        }

        // Get a WI with this priority
        WorkItem /*!*/
          wi = workList[p][0];
        Contract.Assert(wi != null);
        workList[p].RemoveAt(0);

        // update labels
        labels.Remove(wi.getLabel());
        return wi;
      }

      public int Count
      {
        get { return labels.Count; }
      }
    }

    private GenKillWeight getSummary(CallCmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      Contract.Assert(cmd.Proc != null);
      string /*!*/
        procName = cmd.Proc.Name;
      Contract.Assert(procName != null);
      if (procICFG.ContainsKey(procName))
      {
        ImplementationControlFlowGraph /*!*/
          cfg = procICFG[procName];
        Contract.Assert(cfg != null);
        return GenKillWeight.projectLocals(cfg.summary);
      }

      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    public void ComputeLiveVars(Implementation impl, Program /*!*/ prog)
    {
      Contract.Requires(prog != null);
      Contract.Requires(impl != null);
      InterProcGenKill /*!*/
        ipgk = new InterProcGenKill(impl, prog, options);
      Contract.Assert(ipgk != null);
      ipgk.Compute();
    }

    public void Compute()
    {
      // Put all exit nodes in the worklist
      foreach (ImplementationControlFlowGraph /*!*/ cfg in procICFG.Values)
      {
        Contract.Assert(cfg != null);
        foreach (Block /*!*/ eb in cfg.exitNodes)
        {
          Contract.Assert(eb != null);
          WorkItem /*!*/
            wi = new WorkItem(cfg, eb);
          Contract.Assert(wi != null);
          cfg.weightAfter[eb] = GenKillWeight.one();
          AddToWorkList(wi);
        }
      }

      while (workList.Count != 0)
      {
        WorkItem /*!*/
          wi = workList.Get();
        Contract.Assert(wi != null);
        process(wi);
      }

      // Propagate LV to all procedures
      foreach (ImplementationControlFlowGraph /*!*/ cfg in procICFG.Values)
      {
        Contract.Assert(cfg != null);
        foreach (Block /*!*/ b in cfg.nodes)
        {
          Contract.Assert(b != null);
          cfg.liveVarsAfter.Add(b, new HashSet<Variable /*!*/>());
          cfg.liveVarsBefore.Add(b, new HashSet<Variable /*!*/>());
        }
      }

      ImplementationControlFlowGraph /*!*/
        mainCfg = procICFG[mainImpl.Name];
      Contract.Assert(mainCfg != null);
      foreach (Block /*!*/ eb in mainCfg.exitNodes)
      {
        Contract.Assert(eb != null);
        WorkItem /*!*/
          wi = new WorkItem(mainCfg, eb);
        Contract.Assert(wi != null);
        AddToWorkListReverse(wi);
      }

      while (workList.Count != 0)
      {
        WorkItem /*!*/
          wi = workList.Get();
        Contract.Assert(wi != null);
        ProcessLv(wi);
      }

      // Set live variable info
      foreach (ImplementationControlFlowGraph /*!*/ cfg in procICFG.Values)
      {
        Contract.Assert(cfg != null);
        HashSet<Variable /*!*/> /*!*/
          lv = new HashSet<Variable /*!*/>();
        foreach (Block /*!*/ eb in cfg.exitNodes)
        {
          Contract.Assert(eb != null);
          lv.UnionWith(cfg.liveVarsAfter[eb]);
        }

        varsLiveAtExit.Add(cfg.impl.Name, lv);
        lv = new HashSet<Variable /*!*/>();
        foreach (Block /*!*/ eb in cfg.srcNodes)
        {
          Contract.Assert(eb != null);
          lv.UnionWith(cfg.liveVarsBefore[eb]);
        }

        varsLiveAtEntry.Add(cfg.impl.Name, lv);
        varsLiveSummary.Add(cfg.impl.Name, cfg.summary);
      }
    }

    // Called when summaries have already been computed
    private void ProcessLv(WorkItem wi)
    {
      Contract.Requires(wi != null);
      ImplementationControlFlowGraph /*!*/
        cfg = wi.cfg;
      Contract.Assert(cfg != null);
      Block /*!*/
        block = wi.block;
      Contract.Assert(block != null);
      HashSet<Variable /*!*/> /*!*/
        lv = cfg.liveVarsAfter[block];
      Contract.Assert(cce.NonNullElements(lv));
      // Propagate backwards in the block
      HashSet<Variable /*!*/> /*!*/
        prop = new HashSet<Variable /*!*/>();
      prop.UnionWith(lv);
      for (int i = block.Cmds.Count - 1; i >= 0; i--)
      {
        Cmd /*!*/
          cmd = block.Cmds[i];
        Contract.Assert(cmd != null);
        if (cmd is CallCmd)
        {
          string /*!*/
            procName = cce.NonNull(cce.NonNull((CallCmd) cmd).Proc).Name;
          Contract.Assert(procName != null);
          if (procICFG.ContainsKey(procName))
          {
            ImplementationControlFlowGraph /*!*/
              callee = procICFG[procName];
            Contract.Assert(callee != null);
            // Inter propagation
            // Remove local variables; add return variables
            HashSet<Variable /*!*/> /*!*/
              elv = new HashSet<Variable /*!*/>();
            foreach (Variable /*!*/ v in prop)
            {
              Contract.Assert(v != null);
              if (v is GlobalVariable)
              {
                elv.Add(v);
              }
            }

            foreach (Variable /*!*/ v in callee.impl.OutParams)
            {
              Contract.Assert(v != null);
              elv.Add(v);
            }

            foreach (Block /*!*/ eb in callee.exitNodes)
            {
              Contract.Assert(eb != null);
              callee.liveVarsAfter[eb].UnionWith(elv);
              // TODO: check if modified before inserting
              AddToWorkListReverse(new WorkItem(callee, eb));
            }

            // Continue with intra propagation
            GenKillWeight /*!*/
              summary = GetWeightCall(cce.NonNull((CallCmd /*!*/) cmd));
            prop = summary.getLiveVars(prop);
          }
          else
          {
            new LiveVariableAnalysis(options).Propagate(cmd, prop);
          }
        }
        else
        {
          new LiveVariableAnalysis(options).Propagate(cmd, prop);
        }
      }

      cfg.liveVarsBefore[block].UnionWith(prop);

      foreach (Block /*!*/ b in cfg.predEdges[block])
      {
        Contract.Assert(b != null);
        HashSet<Variable /*!*/> /*!*/
          prev = cfg.liveVarsAfter[b];
        Contract.Assert(cce.NonNullElements(prev));
        HashSet<Variable /*!*/> /*!*/
          curr = new HashSet<Variable>(prev);
        curr.UnionWith(cfg.liveVarsBefore[block]);
        Contract.Assert(cce.NonNullElements(curr));
        if (curr.Count != prev.Count)
        {
          cfg.liveVarsAfter[b] = curr;
          AddToWorkListReverse(new WorkItem(cfg, b));
        }
      }
    }

    private void process(WorkItem wi)
    {
      Contract.Requires(wi != null);
      GenKillWeight /*!*/
        w = wi.getWeightAfter();
      Contract.Assert(w != null);

      for (int i = wi.block.Cmds.Count - 1; i >= 0; i--)
      {
        Cmd /*!*/
          c = wi.block.Cmds[i];
        Contract.Assert(c != null);
        if (c is CallCmd && procICFG.ContainsKey(cce.NonNull(cce.NonNull((CallCmd) c).Proc).Name))
        {
          w = GenKillWeight.extend(GetWeightCall(cce.NonNull((CallCmd) c)), w);
        }
        else
        {
          GenKillWeight /*!*/
            cweight = GetWeight(c, wi.cfg.impl, program);
          Contract.Assert(cweight != null);
          w = GenKillWeight.extend(cweight, w);
        }
      }

      bool change = wi.setWeightBefore(w);

      if (change && wi.cfg.srcNodes.Contains(wi.block))
      {
        GenKillWeight /*!*/
          prev = wi.cfg.summary;
        Contract.Assert(prev != null);
        GenKillWeight /*!*/
          curr = GenKillWeight.combine(prev, wi.cfg.weightBefore[wi.block]);
        Contract.Assert(curr != null);
        if (!GenKillWeight.isEqual(prev, curr))
        {
          wi.cfg.summary = curr;
          // push callers onto the worklist
          if (callers.ContainsKey(wi.cfg.impl.Name))
          {
            foreach (WorkItem /*!*/ caller in callers[wi.cfg.impl.Name])
            {
              Contract.Assert(caller != null);
              AddToWorkList(caller);
            }
          }
        }
      }

      foreach (Block /*!*/ b in wi.cfg.predEdges[wi.block])
      {
        Contract.Assert(b != null);
        GenKillWeight /*!*/
          prev = wi.cfg.weightAfter[b];
        Contract.Assert(prev != null);
        GenKillWeight /*!*/
          curr = GenKillWeight.combine(prev, w);
        Contract.Assert(curr != null);
        if (!GenKillWeight.isEqual(prev, curr))
        {
          wi.cfg.weightAfter[b] = curr;
          AddToWorkList(new WorkItem(wi.cfg, b));
        }
      }
    }

    static Dictionary<Cmd /*!*/, GenKillWeight /*!*/> /*!*/
      weightCache = new Dictionary<Cmd /*!*/, GenKillWeight /*!*/>();

    private GenKillWeight GetWeight(Cmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      return GetWeight(cmd, null, null);
    }

    private GenKillWeight GetWeightCall(CallCmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      GenKillWeight /*!*/
        w1 = getWeightBeforeCall(cmd);
      GenKillWeight /*!*/
        w2 = getSummary(cmd);
      GenKillWeight /*!*/
        w3 = getWeightAfterCall(cmd);
      Contract.Assert(w1 != null);
      Contract.Assert(w2 != null);
      Contract.Assert(w3 != null);
      return GenKillWeight.extend(w1, GenKillWeight.extend(w2, w3));
    }

    private GenKillWeight GetWeight(Cmd cmd, Implementation impl, Program prog)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);

      if (weightCache.ContainsKey(cmd))
      {
        return weightCache[cmd];
      }

      HashSet<Variable /*!*/> /*!*/
        gen = new HashSet<Variable /*!*/>();
      HashSet<Variable /*!*/> /*!*/
        kill = new HashSet<Variable /*!*/>();
      GenKillWeight /*!*/
        ret;

      if (cmd is AssignCmd)
      {
        AssignCmd /*!*/
          assignCmd = (AssignCmd) cmd;
        Contract.Assert(cmd != null);
        // I must first iterate over all the targets and remove the live ones.
        // After the removals are done, I must add the variables referred on 
        // the right side of the removed targets
        foreach (AssignLhs /*!*/ lhs in assignCmd.Lhss)
        {
          Contract.Assert(lhs != null);
          Variable var = lhs.DeepAssignedVariable;
          if (var != null)
          {
            if (lhs is SimpleAssignLhs)
            {
              // we should only remove non-map target variables because there is an implicit
              // read of a map variable in an assignment to it
              kill.Add(var);
            }
          }
        }

        int index = 0;
        foreach (Expr /*!*/ expr in assignCmd.Rhss)
        {
          Contract.Assert(expr != null);
          VariableCollector /*!*/
            collector = new VariableCollector();
          collector.Visit(expr);
          gen.UnionWith(collector.usedVars);
          AssignLhs lhs = assignCmd.Lhss[index];
          if (lhs is MapAssignLhs)
          {
            // If the target is a map, then all indices are also read
            MapAssignLhs malhs = (MapAssignLhs) lhs;
            foreach (Expr e in malhs.Indexes)
            {
              VariableCollector /*!*/
                c = new VariableCollector();
              c.Visit(e);
              gen.UnionWith(c.usedVars);
            }
          }

          index++;
        }

        ret = new GenKillWeight(gen, kill);
      }
      else if (cmd is HavocCmd)
      {
        HavocCmd /*!*/
          havocCmd = (HavocCmd) cce.NonNull(cmd);
        foreach (IdentifierExpr /*!*/ expr in havocCmd.Vars)
        {
          Contract.Assert(expr != null);
          if (expr.Decl != null)
          {
            kill.Add(expr.Decl);
          }
        }

        ret = new GenKillWeight(gen, kill);
      }
      else if (cmd is PredicateCmd)
      {
        Contract.Assert((cmd is AssertCmd || cmd is AssumeCmd));
        PredicateCmd /*!*/
          predicateCmd = (PredicateCmd) cce.NonNull(cmd);
        if (predicateCmd.Expr is LiteralExpr && prog != null && impl != null)
        {
          LiteralExpr le = (LiteralExpr) predicateCmd.Expr;
          if (le.IsFalse)
          {
            var globals = prog.GlobalVariables;
            Contract.Assert(cce.NonNullElements(globals));
            foreach (Variable /*!*/ v in globals)
            {
              Contract.Assert(v != null);
              kill.Add(v);
            }

            foreach (Variable /*!*/ v in impl.LocVars)
            {
              Contract.Assert(v != null);
              kill.Add(v);
            }

            foreach (Variable /*!*/ v in impl.OutParams)
            {
              Contract.Assert(v != null);
              kill.Add(v);
            }
          }
        }
        else
        {
          VariableCollector /*!*/
            collector = new VariableCollector();
          collector.Visit(predicateCmd.Expr);
          gen.UnionWith(collector.usedVars);
        }

        ret = new GenKillWeight(gen, kill);
      }
      else if (cmd is CommentCmd)
      {
        ret = new GenKillWeight(gen, kill);
        // comments are just for debugging and don't affect verification
      }
      else if (cmd is SugaredCmd)
      {
        SugaredCmd /*!*/
          sugCmd = (SugaredCmd) cmd;
        Contract.Assert(sugCmd != null);
        ret = GetWeight(sugCmd.GetDesugaring(options), impl, prog);
      }
      else if (cmd is StateCmd)
      {
        StateCmd /*!*/
          stCmd = (StateCmd) cmd;
        Contract.Assert(stCmd != null);
        List<Cmd> /*!*/
          cmds = stCmd.Cmds;
        Contract.Assert(cmds != null);
        int len = cmds.Count;
        ret = GenKillWeight.one();
        for (int i = len - 1; i >= 0; i--)
        {
          GenKillWeight /*!*/
            w = GetWeight(cmds[i], impl, prog);
          Contract.Assert(w != null);
          ret = GenKillWeight.extend(w, ret);
        }

        foreach (Variable /*!*/ v in stCmd.Locals)
        {
          Contract.Assert(v != null);
          kill.Add(v);
        }

        ret = GenKillWeight.extend(new GenKillWeight(gen, kill), ret);
      }
      else
      {
        {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }

      weightCache[cmd] = ret;
      return ret;
    }

    static Dictionary<Cmd /*!*/, GenKillWeight /*!*/> /*!*/
      weightCacheAfterCall = new Dictionary<Cmd /*!*/, GenKillWeight /*!*/>();

    static Dictionary<Cmd /*!*/, GenKillWeight /*!*/> /*!*/
      weightCacheBeforeCall = new Dictionary<Cmd /*!*/, GenKillWeight /*!*/>();

    private static GenKillWeight getWeightAfterCall(Cmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);

      if (weightCacheAfterCall.ContainsKey(cmd))
      {
        return weightCacheAfterCall[cmd];
      }

      HashSet<Variable /*!*/> /*!*/
        gen = new HashSet<Variable /*!*/>();
      HashSet<Variable /*!*/> /*!*/
        kill = new HashSet<Variable /*!*/>();

      Contract.Assert(cmd is CallCmd);
      CallCmd /*!*/
        ccmd = cce.NonNull((CallCmd) cmd);

      foreach (IdentifierExpr /*!*/ ie in ccmd.Outs)
      {
        Contract.Assert(ie != null);
        if (ie.Decl != null)
        {
          kill.Add(ie.Decl);
        }
      }

      // Variables in ensures are considered as "read"
      foreach (Ensures /*!*/ re in cce.NonNull(ccmd.Proc).Ensures)
      {
        Contract.Assert(re != null);
        VariableCollector /*!*/
          collector = new VariableCollector();
        collector.Visit(re.Condition);
        foreach (Variable /*!*/ v in collector.usedVars)
        {
          Contract.Assert(v != null);
          if (v is GlobalVariable)
          {
            gen.Add(v);
          }
        }
      }

      GenKillWeight /*!*/
        ret = new GenKillWeight(gen, kill);
      Contract.Assert(ret != null);
      weightCacheAfterCall[cmd] = ret;
      return ret;
    }

    private static GenKillWeight getWeightBeforeCall(Cmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      Contract.Assert((cmd is CallCmd));
      if (weightCacheBeforeCall.ContainsKey(cmd))
      {
        return weightCacheBeforeCall[cmd];
      }

      HashSet<Variable /*!*/> /*!*/
        gen = new HashSet<Variable /*!*/>();
      HashSet<Variable /*!*/> /*!*/
        kill = new HashSet<Variable /*!*/>();
      CallCmd /*!*/
        ccmd = cce.NonNull((CallCmd /*!*/) cmd);

      foreach (Expr /*!*/ expr in ccmd.Ins)
      {
        Contract.Assert(expr != null);
        VariableCollector /*!*/
          collector = new VariableCollector();
        collector.Visit(expr);
        gen.UnionWith(collector.usedVars);
      }

      Contract.Assert(ccmd.Proc != null);

      // Variables in requires are considered as "read"
      foreach (Requires /*!*/ re in ccmd.Proc.Requires)
      {
        Contract.Assert(re != null);
        VariableCollector /*!*/
          collector = new VariableCollector();
        collector.Visit(re.Condition);
        foreach (Variable /*!*/ v in collector.usedVars)
        {
          Contract.Assert(v != null);
          if (v is GlobalVariable)
          {
            gen.Add(v);
          }
        }
      }

      // Old variables in ensures are considered as "read"
      foreach (Ensures /*!*/ re in ccmd.Proc.Ensures)
      {
        Contract.Assert(re != null);
        VariableCollector /*!*/
          collector = new VariableCollector();
        collector.Visit(re.Condition);
        foreach (Variable /*!*/ v in collector.oldVarsUsed)
        {
          Contract.Assert(v != null);
          if (v is GlobalVariable)
          {
            gen.Add(v);
          }
        }
      }

      GenKillWeight /*!*/
        ret = new GenKillWeight(gen, kill);
      Contract.Assert(ret != null);
      weightCacheAfterCall[cmd] = ret;
      return ret;
    }
  }
}