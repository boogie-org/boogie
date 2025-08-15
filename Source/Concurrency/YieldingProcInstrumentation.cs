using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  class YieldingProcInstrumentation
  {
    public static List<Declaration> TransformImplementations(
      CivlTypeChecker civlTypeChecker,
      int layerNum,
      AbsyMap absyMap,
      Dictionary<CallCmd, Block> refinementBlocks)
    {
      var linearPermissionInstrumentation =
        new LinearPermissionInstrumentation(civlTypeChecker, layerNum, absyMap);
      var yieldingProcInstrumentation = new YieldingProcInstrumentation(
        civlTypeChecker,
        linearPermissionInstrumentation,
        layerNum,
        absyMap,
        refinementBlocks);
      yieldingProcInstrumentation.AddNoninterferenceCheckers();
      var implToPreconditions = yieldingProcInstrumentation.CreatePreconditions(linearPermissionInstrumentation);
      yieldingProcInstrumentation
        .InlineYieldRequiresAndEnsures(); // inline after creating the preconditions but before transforming the implementations
      yieldingProcInstrumentation.TransformImpls(implToPreconditions);

      List<Declaration> decls = new List<Declaration>();
      decls.AddRange(yieldingProcInstrumentation.noninterferenceCheckerProcs.Values);
      decls.AddRange(yieldingProcInstrumentation.noninterferenceCheckerImpls.Values);
      decls.AddRange(yieldingProcInstrumentation.parallelCallAggregators.Values);

      decls.Add(yieldingProcInstrumentation.wrapperYieldToYieldNoninterferenceCheckerProc);
      decls.Add(yieldingProcInstrumentation.wrapperGlobalNoninterferenceCheckerProc);

      var yieldToYieldNoninterferenceCheckerProcs =
        yieldingProcInstrumentation.noninterferenceCheckerProcs.Where(pair => !pair.Key.IsGlobal).Select(pair => pair.Value);
      var globalNoninterferenceCheckerProcs =
        yieldingProcInstrumentation.noninterferenceCheckerProcs.Where(pair => pair.Key.IsGlobal).Select(pair => pair.Value);
      decls.Add(yieldingProcInstrumentation.WrapperNoninterferenceCheckerImpl(
        yieldingProcInstrumentation.wrapperYieldToYieldNoninterferenceCheckerProc,
        yieldToYieldNoninterferenceCheckerProcs));
      decls.Add(yieldingProcInstrumentation.WrapperNoninterferenceCheckerImpl(
        yieldingProcInstrumentation.wrapperGlobalNoninterferenceCheckerProc,
        globalNoninterferenceCheckerProcs));
      if (yieldToYieldNoninterferenceCheckerProcs.Count() > 0)
      {
        decls.AddRange(yieldingProcInstrumentation.ActionNoninterferenceCheckers(
          civlTypeChecker.MoverActions.Where(a => a.LayerRange.Contains(layerNum) && a.ActionDecl.MaybePendingAsync),
          false));
      }
      if (globalNoninterferenceCheckerProcs.Count() > 0)
      {
        decls.AddRange(yieldingProcInstrumentation.ActionNoninterferenceCheckers(
          civlTypeChecker.MoverActions.Where(a => a.LayerRange.Contains(layerNum)),
          true));
      }

      return decls;
    }

    private CivlTypeChecker civlTypeChecker;
    private int layerNum;
    private AbsyMap absyMap;

    private Dictionary<string, Procedure> parallelCallAggregators;
    private Dictionary<YieldInvariantDecl, Procedure> noninterferenceCheckerProcs;
    private Dictionary<YieldInvariantDecl, Implementation> noninterferenceCheckerImpls;
    private Procedure wrapperYieldToYieldNoninterferenceCheckerProc;
    private Procedure wrapperGlobalNoninterferenceCheckerProc;
    
    private RefinementInstrumentation refinementInstrumentation;
    private LinearPermissionInstrumentation linearPermissionInstrumentation;

    private Dictionary<CallCmd, Block> refinementBlocks;

    private Dictionary<LinearDomain, Variable> localPermissionCollectors;
    private Dictionary<Variable, Variable> oldGlobalMap;
    private List<Variable> wrapperNoninterferenceCheckerCallArgs;
    
    private YieldingProcInstrumentation(
      CivlTypeChecker civlTypeChecker,
      LinearPermissionInstrumentation linearPermissionInstrumentation,
      int layerNum,
      AbsyMap absyMap,
      Dictionary<CallCmd, Block> refinementBlocks)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.layerNum = layerNum;
      this.absyMap = absyMap;
      this.linearPermissionInstrumentation = linearPermissionInstrumentation;
      this.refinementBlocks = refinementBlocks;
      parallelCallAggregators = new Dictionary<string, Procedure>();
      noninterferenceCheckerProcs = new Dictionary<YieldInvariantDecl, Procedure>();
      noninterferenceCheckerImpls = new Dictionary<YieldInvariantDecl, Implementation>();
      localPermissionCollectors = new Dictionary<LinearDomain, Variable>();
      oldGlobalMap = new Dictionary<Variable, Variable>();
      wrapperNoninterferenceCheckerCallArgs = new List<Variable>();

      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      List<Variable> wrapperNoninterferenceCheckerFormals = new List<Variable>();
      foreach (var domain in linearTypeChecker.LinearDomains)
      {
        wrapperNoninterferenceCheckerFormals.Add(
          civlTypeChecker.Formal(NoninterferenceChecker.PermissionCollectorFormalName(domain), domain.mapTypeBool,
            true));
        localPermissionCollectors.Add(domain,
          civlTypeChecker.LocalVariable(NoninterferenceChecker.PermissionCollectorLocalName(domain),
            domain.mapTypeBool));
        wrapperNoninterferenceCheckerCallArgs.Add(localPermissionCollectors[domain]);
      }

      foreach (Variable g in civlTypeChecker.GlobalVariables)
      {
        wrapperNoninterferenceCheckerFormals.Add(OldGlobalFormal(g));
        oldGlobalMap[g] = OldGlobalLocal(g);
        wrapperNoninterferenceCheckerCallArgs.Add(oldGlobalMap[g]);
      }

      wrapperYieldToYieldNoninterferenceCheckerProc = DeclHelper.Procedure(
        civlTypeChecker.AddNamePrefix($"Wrapper_YieldToYield_NoninterferenceChecker_{layerNum}"),
        wrapperNoninterferenceCheckerFormals, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
      CivlUtil.AddInlineAttribute(wrapperYieldToYieldNoninterferenceCheckerProc);
      
      wrapperGlobalNoninterferenceCheckerProc = DeclHelper.Procedure(
        civlTypeChecker.AddNamePrefix($"Wrapper_Global_NoninterferenceChecker_{layerNum}"),
        wrapperNoninterferenceCheckerFormals, new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
      CivlUtil.AddInlineAttribute(wrapperGlobalNoninterferenceCheckerProc);

      if (civlTypeChecker.Options.TrustNoninterference)
      {
        localPermissionCollectors.Clear();
      }
    }

    private List<Cmd> CreateUpdatesToPermissionCollector(Absy absy)
    {
      var cmds = new List<Cmd>();
      if (localPermissionCollectors.Count > 0)
      {
        Debug.Assert(!civlTypeChecker.Options.TrustNoninterference);
        var domainToExpr = linearPermissionInstrumentation.PermissionExprs(absy);
        var lhss = localPermissionCollectors.Values.Select(Expr.Ident).ToList();
        var rhss = localPermissionCollectors.Keys.Select(domain => domainToExpr[domain]).ToList();
        cmds.Add(CmdHelper.AssignCmd(lhss, rhss));
      }
      return cmds;
    }

    private List<Cmd> CreateUpdatesToOldGlobalVars()
    {
      List<IdentifierExpr> lhss = new List<IdentifierExpr>();
      List<Expr> rhss = new List<Expr>();
      foreach (Variable g in oldGlobalMap.Keys)
      {
        lhss.Add(Expr.Ident(oldGlobalMap[g]));
        rhss.Add(Expr.Ident(g));
      }
      var cmds = new List<Cmd>();
      if (lhss.Count > 0)
      {
        cmds.Add(CmdHelper.AssignCmd(lhss, rhss));
      }
      return cmds;
    }
    
    private List<Cmd> CreateCallToNoninterferenceChecker(Procedure wrapperNoninterferenceCheckerProc)
    {
      var cmds = new List<Cmd>();
      if (!civlTypeChecker.Options.TrustNoninterference)
      {
        var wrapperNoninterferenceCheckerCallCmd = CmdHelper.CallCmd(wrapperNoninterferenceCheckerProc,
          wrapperNoninterferenceCheckerCallArgs, new List<Variable>());
        cmds.Add(wrapperNoninterferenceCheckerCallCmd);
      }
      return cmds;
    }
    
    private LocalVariable OldGlobalLocal(Variable v)
    {
      return civlTypeChecker.LocalVariable($"global_old_{v.Name}", v.TypedIdent.Type);
    }
    
    private YieldProcedureDecl GetYieldingProc(Implementation impl)
    {
      return (YieldProcedureDecl)absyMap.Original(impl).Proc;
    }

    private Implementation WrapperNoninterferenceCheckerImpl(
      Procedure wrapperNoninterferenceCheckerProc, IEnumerable<Procedure> noninterferenceCheckerProcs)
    {
      var inputs = wrapperNoninterferenceCheckerProc.InParams
        .Select(v => civlTypeChecker.Formal(v.Name, v.TypedIdent.Type, true)).ToList<Variable>();
      List<Block> blocks = new List<Block>();
      TransferCmd transferCmd = CmdHelper.ReturnCmd;
      if (noninterferenceCheckerProcs.Count() > 0)
      {
        List<Block> blockTargets = new List<Block>();
        int labelCount = 0;
        foreach (Procedure proc in noninterferenceCheckerProcs)
        {
          List<Expr> exprSeq = new List<Expr>();
          foreach (Variable v in inputs)
          {
            exprSeq.Add(Expr.Ident(v));
          }
          CallCmd callCmd = CmdHelper.CallCmd(proc, exprSeq, new List<IdentifierExpr>());
          string label = $"L_{labelCount++}";
          Block block = BlockHelper.Block(label, new List<Cmd> {callCmd});
          blockTargets.Add(block);
          blocks.Add(block);
        }
        transferCmd = new GotoCmd(Token.NoToken, blockTargets);
      }
      blocks.Insert(0, new Block(Token.NoToken, "enter", new List<Cmd>(), transferCmd));
      return DeclHelper.Implementation(wrapperNoninterferenceCheckerProc, inputs, new List<Variable>(),
        new List<Variable>(), blocks);
    }

    private Formal OldGlobalFormal(Variable v)
    {
      return civlTypeChecker.Formal($"global_old_{v.Name}", v.TypedIdent.Type, true);
    }

    private void AddNoninterferenceCheckers()
    {
      if (civlTypeChecker.Options.TrustNoninterference)
      {
        return;
      }

      foreach (var yieldInvariantDecl in civlTypeChecker.program.TopLevelDeclarations.OfType<YieldInvariantDecl>().ToList())
      {
        if (layerNum == yieldInvariantDecl.Layer && yieldInvariantDecl.Requires.Any())
        {
          var (proc, impl) = NoninterferenceChecker.CreateNoninterferenceCheckerDecls(civlTypeChecker,
              layerNum, absyMap, yieldInvariantDecl, new List<Variable>());
          noninterferenceCheckerProcs[yieldInvariantDecl] = proc;
          noninterferenceCheckerImpls[yieldInvariantDecl] = impl;
        }
      }
    }

    // Add assignment g := g for all global variables g at yielding loop heads.
    // This is to make all global variables loop targets that get havoced.
    private List<Cmd> YieldingLoopDummyAssignment()
    {
      var globals = civlTypeChecker.GlobalVariables.Select(Expr.Ident).ToList();
      var cmds = new List<Cmd>();
      if (globals.Count != 0)
      {
        cmds.Add(CmdHelper.AssignCmd(globals, globals.ToList<Expr>()));
      }

      return cmds;
    }

    private List<Cmd> InlineYieldLoopInvariants(List<CallCmd> yieldInvariants)
    {
      var inlinedYieldInvariants = new List<Cmd>();
      foreach (var callCmd in yieldInvariants)
      {
        var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
        if (layerNum == yieldInvariant.Layer)
        {
          Dictionary<Variable, Expr> map = yieldInvariant.InParams.Zip(callCmd.Ins)
            .ToDictionary(x => x.Item1, x => x.Item2);
          Substitution subst = Substituter.SubstitutionFromDictionary(map);
          foreach (Requires req in yieldInvariant.Requires)
          {
            var newExpr = Substituter.Apply(subst, req.Condition);
            if (req.Free)
            {
              inlinedYieldInvariants.Add(new AssumeCmd(req.tok, newExpr, req.Attributes));
            }
            else
            {
              inlinedYieldInvariants.Add(new AssertCmd(req.tok, newExpr, req.Attributes));
            }
          }
        }
      }
      return inlinedYieldInvariants;
    }

    private Dictionary<Implementation, List<Cmd>> CreatePreconditions(
      LinearPermissionInstrumentation linearPermissionInstrumentation)
    {
      var implToInitCmds = new Dictionary<Implementation, List<Cmd>>();
      foreach (var impl in absyMap.Keys.OfType<Implementation>())
      {
        var initCmds = new List<Cmd>();

        // Global variables must be havoced to model the yield upon entering a yielding procedure
        if (civlTypeChecker.GlobalVariables.Count() > 0)
        {
          initCmds.Add(CmdHelper.HavocCmd(
            civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList()));
        }

        initCmds.AddRange(linearPermissionInstrumentation.DisjointnessAndWellFormedAssumeCmds(impl, true));

        Substitution procToImplInParams = Substituter.SubstitutionFromDictionary(impl.Proc.InParams
          .Zip(impl.InParams).ToDictionary(x => x.Item1, x => (Expr) Expr.Ident(x.Item2)));

        impl.Proc.Requires.ForEach(req =>
          initCmds.Add(new AssumeCmd(req.tok, Substituter.Apply(procToImplInParams, req.Condition))));

        foreach (var callCmd in GetYieldingProc(impl).DesugaredYieldRequires)
        {
          var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
          if (layerNum == yieldInvariant.Layer)
          {
            Substitution callFormalsToActuals = Substituter.SubstitutionFromDictionary(yieldInvariant.InParams
              .Zip(callCmd.Ins)
              .ToDictionary(x => x.Item1, x => (Expr) ExprHelper.Old(x.Item2)));
            yieldInvariant.Requires.ForEach(req => initCmds.Add(new AssumeCmd(req.tok,
              Substituter.Apply(procToImplInParams,
                Substituter.Apply(callFormalsToActuals, req.Condition)))));
          }
        }

        implToInitCmds[impl] = initCmds;
      }

      return implToInitCmds;
    }

    private void InlineYieldRequiresAndEnsures()
    {
      foreach (var impl in absyMap.Keys.OfType<Implementation>())
      {
        var yieldingProc = GetYieldingProc(impl);
        foreach (var callCmd in yieldingProc.DesugaredYieldRequires)
        {
          var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
          if (layerNum == yieldInvariant.Layer)
          {
            Dictionary<Variable, Expr> map = yieldInvariant.InParams.Zip(callCmd.Ins)
              .ToDictionary(x => x.Item1, x => x.Item2);
            Substitution subst = Substituter.SubstitutionFromDictionary(map);
            foreach (Requires req in yieldInvariant.Requires)
            {
              impl.Proc.Requires.Add(new Requires(req.tok, req.Free, Substituter.Apply(subst, req.Condition),
                null,
                req.Attributes));
            }
          }
        }

        foreach (var callCmd in yieldingProc.DesugaredYieldEnsures)
        {
          var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
          if (layerNum == yieldInvariant.Layer)
          {
            Dictionary<Variable, Expr> map = yieldInvariant.InParams.Zip(callCmd.Ins)
              .ToDictionary(x => x.Item1, x => x.Item2);
            Substitution subst = Substituter.SubstitutionFromDictionary(map);
            foreach (Requires req in yieldInvariant.Requires)
            {
              impl.Proc.Ensures.Add(new Ensures(req.tok, req.Free, Substituter.Apply(subst, req.Condition),
                null,
                req.Attributes));
            }
          }
        }
      }
    }

    private void TransformImpls(Dictionary<Implementation, List<Cmd>> implToPreconditions)
    {
      foreach (var impl in absyMap.Keys.OfType<Implementation>())
      {
        // Add disjointness assumptions at loop headers and after each parallel call
        // for each duplicate implementation of yielding procedures.
        // Disjointness assumptions after yields are added inside TransformImpl which is called for 
        // all implementations except for a mover procedure at its disappearing layer.
        // But this is fine because a mover procedure at its disappearing layer does not have a yield in it.
        linearPermissionInstrumentation.AddDisjointnessAndWellFormedAssumptions(impl);
        var yieldingProc = GetYieldingProc(impl);
        if (yieldingProc.HasMoverType && yieldingProc.Layer == layerNum)
        {
          continue;
        }

        TransformImpl(impl, implToPreconditions[impl]);
      }
    }

    private void TransformImpl(Implementation impl, List<Cmd> preconditions)
    {
      // initialize refinementInstrumentation
      var yieldingProc = GetYieldingProc(impl);
      if (yieldingProc.Layer == this.layerNum)
      {
        refinementInstrumentation = new ActionRefinementInstrumentation(
          civlTypeChecker,
          impl,
          absyMap.Original(impl),
          oldGlobalMap);
      }
      else
      {
        refinementInstrumentation = new RefinementInstrumentation();
      }

      DesugarConcurrency(impl, preconditions);

      impl.LocVars.AddRange(oldGlobalMap.Values);
      impl.LocVars.AddRange(refinementInstrumentation.NewLocalVars);
      impl.LocVars.AddRange(localPermissionCollectors.Values);
    }

    private Block CreateInitialBlock(Implementation impl, List<Cmd> preconditions)
    {
      var initCmds = new List<Cmd>(preconditions);
      initCmds.AddRange(CreateUpdatesToOldGlobalVars());
      initCmds.AddRange(refinementInstrumentation.CreateInitCmds());
      initCmds.AddRange(CreateUpdatesToPermissionCollector(impl));
      return BlockHelper.Block(civlTypeChecker.AddNamePrefix("init"), initCmds, new List<Block> {impl.Blocks[0]});
    }

    private bool IsYieldingLoopHeader(YieldProcedureDecl yieldingProc, Block b)
    {
      if (!absyMap.ContainsKey(b))
      {
        return false;
      }
      var originalBlock = absyMap.Original(b);
      return yieldingProc.IsYieldingLoopHeader(originalBlock, layerNum);
    }

    private void ComputeYieldingLoops(
      Implementation impl,
      out HashSet<Block> yieldingLoopHeaders,
      out HashSet<Block> blocksInYieldingLoops)
    {
      var yieldingProc = GetYieldingProc(impl);
      yieldingLoopHeaders = new HashSet<Block>(impl.Blocks.Where(b => IsYieldingLoopHeader(yieldingProc, b)));

      impl.PruneUnreachableBlocks(civlTypeChecker.Options);
      impl.ComputePredecessorsForBlocks();
      var graph = Program.GraphFromImpl(impl);
      graph.ComputeLoops();
      blocksInYieldingLoops = GetBlocksInAllNaturalLoops(yieldingLoopHeaders, graph);
    }

    private HashSet<Block> GetBlocksInAllNaturalLoops(HashSet<Block> headers, Graph<Block> g)
    {
      var allBlocksInNaturalLoops = new HashSet<Block>();
      foreach (Block header in headers)
      {
        foreach (Block source in g.BackEdgeNodes(header))
        {
          g.NaturalLoops(header, source).ForEach(b => allBlocksInNaturalLoops.Add(b));
        }
      }
      return allBlocksInNaturalLoops;
    }

    private void AddEdge(GotoCmd gotoCmd, Block b)
    {
      gotoCmd.AddTarget(b);
    }

    private void DesugarConcurrency(Implementation impl, List<Cmd> preconditions)
    {
      var yieldingProc = GetYieldingProc(impl);
      var noninterferenceCheckerBlock = CreateNoninterferenceCheckerBlock();
      var refinementCheckerBlock = CreateRefinementCheckerBlock();
      var unchangedCheckerBlock = CreateUnchangedCheckerBlock();
      var returnCheckerBlock = CreateReturnCheckerBlock();
      var returnBlock = BlockHelper.Block(civlTypeChecker.AddNamePrefix("UnifiedReturn"), new List<Cmd>());
      SplitBlocks(impl);

      ComputeYieldingLoops(impl, out var yieldingLoopHeaders, out var blocksInYieldingLoops);
      foreach (Block header in yieldingLoopHeaders)
      {
        foreach (Block pred in header.Predecessors)
        {
          var gotoCmd = pred.TransferCmd as GotoCmd;
          AddEdge(gotoCmd, noninterferenceCheckerBlock);
          if (blocksInYieldingLoops.Contains(pred))
          {
            AddEdge(gotoCmd, unchangedCheckerBlock);
          }
          else
          {
            AddEdge(gotoCmd, refinementCheckerBlock);
          }
        }

        SplitCmds(header.Cmds, out var firstCmds, out var secondCmds);
        List<Cmd> newCmds = new List<Cmd>();
        newCmds.AddRange(firstCmds);
        newCmds.AddRange(refinementInstrumentation.CreateAssumeCmds());
        newCmds.AddRange(
          InlineYieldLoopInvariants(yieldingProc.YieldingLoops[absyMap.Original(header)].YieldInvariants));
        newCmds.AddRange(YieldingLoopDummyAssignment());
        newCmds.AddRange(CreateUpdatesToOldGlobalVars());
        newCmds.AddRange(refinementInstrumentation.CreateUpdatesToOldOutputVars());
        newCmds.AddRange(CreateUpdatesToPermissionCollector(header));
        newCmds.AddRange(secondCmds);
        header.Cmds = newCmds;
      }

      // add jumps to noninterferenceChecker, returnChecker, and refinementChecker blocks
      var implRefinementCheckingBlocks = new List<Block>();
      foreach (var b in impl.Blocks) {
        if (b.TransferCmd is not GotoCmd gotoCmd) {
          b.TransferCmd = new GotoCmd(b.TransferCmd.tok,
            new List<Block> { returnCheckerBlock, returnBlock, noninterferenceCheckerBlock });
          continue;
        }

        var targetBlocks = new List<Block>();
        var addEdge = false;
        foreach (var nextBlock in gotoCmd.LabelTargets) {
          if (nextBlock.Cmds.Count <= 0) {
            continue;
          }

          var cmd = nextBlock.Cmds[0];
          if (cmd is not ParCallCmd parCallCmd) {
            continue;
          }

          foreach (var callCmd in parCallCmd.CallCmds) {
            if (!refinementBlocks.TryGetValue(callCmd, out var targetBlock)) {
              continue;
            }

            FixUpImplRefinementCheckingBlock(targetBlock,
              CivlAttributes.IsCallMarked(callCmd)
                ? returnCheckerBlock
                : unchangedCheckerBlock);
            targetBlocks.Add(targetBlock);
            implRefinementCheckingBlocks.Add(targetBlock);
          }

          addEdge = true;
        }

        gotoCmd.AddTargets(targetBlocks);
        if (!addEdge) {
          continue;
        }

        AddEdge(gotoCmd, noninterferenceCheckerBlock);
        if (blocksInYieldingLoops.Contains(b)) {
          AddEdge(gotoCmd, unchangedCheckerBlock);
        } else {
          b.Cmds.AddRange(refinementInstrumentation.CreateActionEvaluationCmds());
          AddEdge(gotoCmd, refinementCheckerBlock);
        }
      }

      // desugar ParCallCmd 
      foreach (Block b in impl.Blocks)
      {
        if (b.Cmds.Count > 0)
        {
          var cmd = b.Cmds[0];
          if (cmd is ParCallCmd)
          {
            DesugarParCallCmdInBlock(b, blocksInYieldingLoops.Contains(b));
          }
        }
      }

      impl.Blocks.Add(noninterferenceCheckerBlock);
      impl.Blocks.Add(refinementCheckerBlock);
      impl.Blocks.Add(unchangedCheckerBlock);
      impl.Blocks.Add(returnCheckerBlock);
      impl.Blocks.Add(returnBlock);
      impl.Blocks.AddRange(implRefinementCheckingBlocks);
      impl.Blocks.Insert(0, CreateInitialBlock(impl, preconditions));
    }

    private void FixUpImplRefinementCheckingBlock(Block block, Block refinementCheckerBlock)
    {
      var newCmds = new List<Cmd>();
      if (civlTypeChecker.GlobalVariables.Count() > 0)
      {
        newCmds.Add(CmdHelper.HavocCmd(civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList()));
      }

      newCmds.AddRange(refinementInstrumentation.CreateAssumeCmds());
      newCmds.AddRange(CreateUpdatesToOldGlobalVars());
      newCmds.AddRange(refinementInstrumentation.CreateUpdatesToOldOutputVars());
      newCmds.AddRange(block.Cmds);
      block.Cmds = newCmds;
      var gotoCmd = (GotoCmd) block.TransferCmd;
      gotoCmd.AddTarget(refinementCheckerBlock);
    }

    private bool IsParCallMarked(ParCallCmd parCallCmd)
    {
      return parCallCmd.CallCmds.Any(callCmd => CivlAttributes.IsCallMarked(callCmd));
    }

    private void SplitBlocks(Implementation impl)
    {
      List<Block> newBlocks = new List<Block>();
      foreach (Block b in impl.Blocks)
      {
        var currTransferCmd = b.TransferCmd;
        int labelCount = 0;
        int lastSplitIndex = b.Cmds.Count;
        for (int i = b.Cmds.Count - 1; i >= 0; i--)
        {
          var split = false;
          var cmd = b.Cmds[i];
          if (cmd is ParCallCmd)
          {
            split = true;
          }

          if (split)
          {
            var newBlock = new Block(b.tok, $"{b.Label}_{labelCount++}", b.Cmds.GetRange(i, lastSplitIndex - i),
              currTransferCmd);
            newBlocks.Add(newBlock);
            currTransferCmd = new GotoCmd(b.tok, new List<Block> {newBlock});
            lastSplitIndex = i;
          }
        }

        b.Cmds = b.Cmds.GetRange(0, lastSplitIndex);
        b.TransferCmd = currTransferCmd;
      }

      impl.Blocks.AddRange(newBlocks);
    }

    private Block CreateNoninterferenceCheckerBlock()
    {
      var newCmds = new List<Cmd>();
      newCmds.AddRange(CreateCallToNoninterferenceChecker(wrapperYieldToYieldNoninterferenceCheckerProc));
      newCmds.Add(CmdHelper.AssumeCmd(Expr.False));
      return BlockHelper.Block(civlTypeChecker.AddNamePrefix("NoninterferenceChecker"), newCmds);
    }

    private Block CreateRefinementCheckerBlock()
    {
      var newCmds = new List<Cmd>();
      newCmds.AddRange(refinementInstrumentation.CreateAssertCmds());
      newCmds.Add(CmdHelper.AssumeCmd(Expr.False));
      return BlockHelper.Block(civlTypeChecker.AddNamePrefix("RefinementChecker"), newCmds);
    }

    private Block CreateUnchangedCheckerBlock()
    {
      var newCmds = new List<Cmd>();
      newCmds.AddRange(refinementInstrumentation.CreateUnchangedAssertCmds());
      newCmds.Add(CmdHelper.AssumeCmd(Expr.False));
      return BlockHelper.Block(civlTypeChecker.AddNamePrefix("UnchangedChecker"), newCmds);
    }

    private Block CreateReturnCheckerBlock()
    {
      var returnBlockCmds = new List<Cmd>();
      returnBlockCmds.AddRange(refinementInstrumentation.CreateActionEvaluationCmds());
      returnBlockCmds.AddRange(refinementInstrumentation.CreateAssertCmds());
      returnBlockCmds.AddRange(refinementInstrumentation.CreateUpdatesToRefinementVars(false));
      returnBlockCmds.AddRange(refinementInstrumentation.CreateReturnAssertCmds());
      returnBlockCmds.Add(CmdHelper.AssumeCmd(Expr.False));
      return BlockHelper.Block(civlTypeChecker.AddNamePrefix("ReturnChecker"), returnBlockCmds);
    }

    private void DesugarParCallCmdInBlock(Block block, bool isBlockInYieldingLoop)
    {
      var parCallCmd = (ParCallCmd) block.Cmds[0];
      List<Cmd> newCmds = new List<Cmd>();
      if (!isBlockInYieldingLoop)
      {
        newCmds.AddRange(refinementInstrumentation.CreateUpdatesToRefinementVars(IsParCallMarked(parCallCmd)));
      }

      List<Expr> ins = new List<Expr>();
      List<IdentifierExpr> outs = new List<IdentifierExpr>();
      string procName = "ParallelCall";
      foreach (CallCmd callCmd in parCallCmd.CallCmds)
      {
        // Use original procedure names to make aggregated name more readable
        procName = procName + "_" + absyMap.OriginalOrInput(callCmd.Proc).Name;
        ins.AddRange(callCmd.Ins);
        outs.AddRange(callCmd.Outs);
      }
      procName = civlTypeChecker.AddNamePrefix(procName) + "_" + layerNum;

      if (!parallelCallAggregators.ContainsKey(procName))
      {
        List<Variable> inParams = new List<Variable>();
        List<Variable> outParams = new List<Variable>();
        List<Requires> requiresSeq = new List<Requires>();
        List<Ensures> ensuresSeq = new List<Ensures>();
        int count = 0;
        foreach (CallCmd callCmd in parCallCmd.CallCmds)
        {
          Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
          foreach (Variable x in callCmd.Proc.InParams)
          {
            Variable y = ParCallDesugarFormal(x, count, true);
            inParams.Add(y);
            map[x] = Expr.Ident(y);
          }

          foreach (Variable x in callCmd.Proc.OutParams)
          {
            Variable y = ParCallDesugarFormal(x, count, false);
            outParams.Add(y);
            map[x] = Expr.Ident(y);
          }

          Contract.Assume(callCmd.Proc.TypeParameters.Count == 0);
          Substitution subst = Substituter.SubstitutionFromDictionary(map);
          foreach (Requires req in callCmd.Proc.Requires)
          {
            requiresSeq.Add(new Requires(req.tok, req.Free, Substituter.Apply(subst, req.Condition), null,
              req.Attributes));
          }

          foreach (Ensures ens in callCmd.Proc.Ensures)
          {
            ensuresSeq.Add(new Ensures(ens.tok, ens.Free, Substituter.Apply(subst, ens.Condition), null,
              ens.Attributes));
          }

          count++;
        }

        parallelCallAggregators[procName] = DeclHelper.Procedure(
          procName, inParams, outParams, requiresSeq,
          civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v)).ToList(), ensuresSeq);
      }

      Procedure proc = parallelCallAggregators[procName];
      CallCmd checkerCallCmd = new CallCmd(parCallCmd.tok, proc.Name, ins, outs, parCallCmd.Attributes) { Proc = proc };
      newCmds.Add(checkerCallCmd);
      newCmds.AddRange(refinementInstrumentation.CreateAssumeCmds());
      newCmds.AddRange(CreateUpdatesToOldGlobalVars());
      newCmds.AddRange(refinementInstrumentation.CreateUpdatesToOldOutputVars());
      newCmds.AddRange(CreateUpdatesToPermissionCollector(parCallCmd));
      newCmds.AddRange(block.Cmds.GetRange(1, block.Cmds.Count - 1));
      block.Cmds = newCmds;
    }

    private Formal ParCallDesugarFormal(Variable v, int count, bool incoming)
    {
      return civlTypeChecker.Formal($"{count}_{v.Name}", v.TypedIdent.Type, incoming);
    }

    private void SplitCmds(List<Cmd> cmds, out List<Cmd> firstCmds, out List<Cmd> secondCmds)
    {
      firstCmds = new List<Cmd>();
      secondCmds = new List<Cmd>();
      var count = 0;
      bool splitDone = false;
      while (count < cmds.Count)
      {
        var cmd = cmds[count];
        if (splitDone)
        {
          secondCmds.Add(cmd);
          count++;
        }
        else if (cmd is PredicateCmd)
        {
          firstCmds.Add(cmd);
          count++;
        }
        else
        {
          splitDone = true;
        }
      }
    }

    private IEnumerable<Declaration> ActionNoninterferenceCheckers(IEnumerable<Action> actions, bool isGlobal)
    {
      if (civlTypeChecker.Options.TrustNoninterference)
      {
        yield break;
      }

      var wrapperNoninterferenceCheckerProc = isGlobal ? wrapperGlobalNoninterferenceCheckerProc : wrapperYieldToYieldNoninterferenceCheckerProc;
      var checkerNamePrefix = isGlobal ? "Global" : "YieldToYield";
      foreach (var action in actions.Where(action => action.ModifiedGlobalVars.Count > 0))
      {
        var inputs = action.Impl.InParams;
        var outputs = action.Impl.OutParams;
        var requires = action.Gate.Select(a => new Requires(false, a.Expr)).ToList();
        var ensures = new List<Ensures>();
        var modifies = civlTypeChecker.GlobalVariables.Select(Expr.Ident).ToList();
        var locals = oldGlobalMap.Values.Union(localPermissionCollectors.Values).ToList();
        var cmds = new List<Cmd>();

        cmds.AddRange(CreateUpdatesToOldGlobalVars());
        cmds.AddRange(CreateUpdatesToPermissionCollector(action.Impl));
        cmds.Add(CmdHelper.CallCmd(action.Impl.Proc, inputs, outputs));
        cmds.AddRange(CreateCallToNoninterferenceChecker(wrapperNoninterferenceCheckerProc));
        var blocks = new List<Block> { BlockHelper.Block("init", cmds) };

        var name = civlTypeChecker.AddNamePrefix($"{checkerNamePrefix}_NoninterferenceChecker_{action.Name}_{layerNum}");
        var proc = DeclHelper.Procedure(name, inputs, outputs, requires, modifies, ensures);
        var impl = DeclHelper.Implementation(proc, inputs, outputs, locals, blocks);
        yield return proc;
        yield return impl;
      }
    }
  }
}
