using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using VC;

namespace VCGeneration.Transformations;

public class RemoveBackEdges {
  private VerificationConditionGenerator generator;

  public RemoveBackEdges(VerificationConditionGenerator generator) {
    this.generator = generator;
  }

  public void ConvertCfg2Dag(ImplementationRun run, Dictionary<Block, List<Block>> edgesCut = null, int taskID = -1)
  {
    var impl = run.Implementation;
    Contract.Requires(impl != null);
    impl.PruneUnreachableBlocks(generator.Options); // This is needed for VCVariety.BlockNested, and is otherwise just an optimization

    generator.CurrentLocalVariables = impl.LocVars;
    generator.Variable2SequenceNumber = new Dictionary<Variable, int>();
    generator.IncarnationOriginMap = new Dictionary<Incarnation, Absy>();

    #region Debug Tracing

    if (generator.Options.TraceVerify)
    {
      run.OutputWriter.WriteLine("original implementation");
      ConditionGeneration.EmitImpl(generator.Options, run, false);
    }

    #endregion

    #region Debug Tracing

    if (generator.Options.TraceVerify)
    {
      run.OutputWriter.WriteLine("after desugaring sugared commands like procedure calls");
      ConditionGeneration.EmitImpl(generator.Options, run, true);
    }

    #endregion

    // Recompute the predecessors, but first insert a dummy start node that is sure not to be the target of any goto (because the cutting of back edges
    // below assumes that the start node has no predecessor)
    impl.Blocks.Insert(0,
      new Block(Token.NoToken, "0", new List<Cmd>(),
        new GotoCmd(Token.NoToken, new List<String> { impl.Blocks[0].Label }, new List<Block> { impl.Blocks[0] })));
    ConditionGeneration.ResetPredecessors(impl.Blocks);

    var k = Math.Max(generator.Options.KInductionDepth,
      QKeyValue.FindIntAttribute(impl.Attributes, "kInductionDepth", -1));
    if (k < 0)
    {
      ConvertCfg2DagStandard(impl, edgesCut, taskID);
    }
    else
    {
      ConvertCfg2DagkInduction(impl, edgesCut, taskID, k);
    }

    #region Debug Tracing

    if (generator.Options.TraceVerify)
    {
      run.OutputWriter.WriteLine("after conversion into a DAG");
      ConditionGeneration.EmitImpl(generator.Options, run, true);
    }

    #endregion
  }

  private void ConvertCfg2DagStandard(Implementation impl, Dictionary<Block, List<Block>> edgesCut, int taskID)
  {
    #region Convert program CFG into a DAG

    #region Use the graph library to figure out where the (natural) loops are

    #region Create the graph by adding the source node and each edge

    Graph<Block> g = Program.GraphFromImpl(impl);

    #endregion

    //Graph<Block> g = program.ProcessLoops(impl);

    g.ComputeLoops(); // this is the call that does all of the processing
    if (!g.Reducible)
    {
      throw new VCGenException("Irreducible flow graphs are unsupported.");
    }

    #endregion

    #region Cut the backedges, push assert/assume statements from loop header into predecessors, change them all into assume statements at top of loop, introduce havoc statements

    foreach (Block header in cce.NonNull(g.Headers))
    {
      Contract.Assert(header != null);
      IDictionary<Block, object> backEdgeNodes = new Dictionary<Block, object>();
      foreach (Block b in cce.NonNull(g.BackEdgeNodes(header)))
      {
        Contract.Assert(b != null);
        backEdgeNodes.Add(b, null);
      }

      #region Find the (possibly empty) prefix of assert commands in the header, replace each assert with an assume of the same condition

      List<Cmd> prefixOfPredicateCmdsInit = new List<Cmd>();
      List<Cmd> prefixOfPredicateCmdsMaintained = new List<Cmd>();
      for (int i = 0, n = header.Cmds.Count; i < n; i++) {
        if (header.Cmds[i] is not PredicateCmd predicateCmd) {
          if (header.Cmds[i] is CommentCmd) {
            // ignore
            continue;
          }

          break; // stop when an assignment statement (or any other non-predicate cmd) is encountered
        }

        if (predicateCmd is AssertCmd assertCmd) {
          AssertCmd initAssertCmd;

          if (generator.Options.ConcurrentHoudini) {
            Contract.Assert(taskID >= 0);
            initAssertCmd = generator.Options.Cho[taskID].DisableLoopInvEntryAssert
              ? new LoopInitAssertCmd(assertCmd.tok, Expr.True, assertCmd)
              : new LoopInitAssertCmd(assertCmd.tok, assertCmd.Expr, assertCmd);
          } else {
            initAssertCmd = new LoopInitAssertCmd(assertCmd.tok, assertCmd.Expr, assertCmd);
          }

          initAssertCmd.Attributes = (QKeyValue)assertCmd.Attributes?.Clone();
          // Copy any {:id ...} from the invariant to the assertion that it's established, so
          // we can track it while analyzing verification coverage.
          initAssertCmd.CopyIdWithModificationsFrom(assertCmd.tok, assertCmd,
            id => new TrackedInvariantEstablished(id));

          prefixOfPredicateCmdsInit.Add(initAssertCmd);

          LoopInvMaintainedAssertCmd maintainedAssertCmd;
          if (generator.Options.ConcurrentHoudini) {
            Contract.Assert(taskID >= 0);
            maintainedAssertCmd = generator.Options.Cho[taskID].DisableLoopInvMaintainedAssert
              ? new LoopInvMaintainedAssertCmd(assertCmd.tok, Expr.True, assertCmd)
              : new LoopInvMaintainedAssertCmd(assertCmd.tok, assertCmd.Expr, assertCmd);
          } else {
            maintainedAssertCmd = new LoopInvMaintainedAssertCmd(assertCmd.tok, assertCmd.Expr, assertCmd);
          }

          maintainedAssertCmd.Attributes = (QKeyValue)assertCmd.Attributes?.Clone();
          // Copy any {:id ...} from the invariant to the assertion that it's maintained, so
          // we can track it while analyzing verification coverage.
          (maintainedAssertCmd as ICarriesAttributes).CopyIdWithModificationsFrom(assertCmd.tok, assertCmd,
            id => new TrackedInvariantMaintained(id));

          prefixOfPredicateCmdsMaintained.Add(maintainedAssertCmd);
          AssumeCmd assume = new AssumeCmd(assertCmd.tok, assertCmd.Expr);
          // Copy any {:id ...} from the invariant to the assumption used within the body, so
          // we can track it while analyzing verification coverage.
          assume.CopyIdWithModificationsFrom(assertCmd.tok, assertCmd,
            id => new TrackedInvariantAssumed(id));

          header.Cmds[i] = assume;
        } else {
          Contract.Assert(predicateCmd is AssumeCmd);
          if (generator.Options.AlwaysAssumeFreeLoopInvariants) {
            // Usually, "free" stuff, like free loop invariants (and the assume statements
            // that stand for such loop invariants) are ignored on the checking side.  This
            // command-line option changes that behavior to always assume the conditions.
            prefixOfPredicateCmdsInit.Add(predicateCmd);
            prefixOfPredicateCmdsMaintained.Add(predicateCmd);
          }
        }
      }

      #endregion

      #region Copy the prefix of predicate commands into each predecessor. Do this *before* cutting the backedge!!

      for (int predIndex = 0, n = header.Predecessors.Count; predIndex < n; predIndex++)
      {
        Block pred = cce.NonNull(header.Predecessors[predIndex]);

        // Create a block between header and pred for the predicate commands if pred has more than one successor
        GotoCmd gotocmd = cce.NonNull((GotoCmd)pred.TransferCmd);
        Contract.Assert(gotocmd.LabelNames !=
                        null); // if "pred" is really a predecessor, it may be a GotoCmd with at least one label
        if (gotocmd.LabelNames.Count > 1)
        {
          Block newBlock = generator.CreateBlockBetween(predIndex, header);
          impl.Blocks.Add(newBlock);

          // if pred is a back edge node, then now newBlock is the back edge node
          if (backEdgeNodes.ContainsKey(pred))
          {
            backEdgeNodes.Remove(pred);
            backEdgeNodes.Add(newBlock, null);
          }

          pred = newBlock;
        }

        // Add the predicate commands
        if (backEdgeNodes.ContainsKey(pred))
        {
          pred.Cmds.AddRange(prefixOfPredicateCmdsMaintained);
        }
        else
        {
          pred.Cmds.AddRange(prefixOfPredicateCmdsInit);
        }
      }

      #endregion

      #region Cut the back edge

      foreach (Block backEdgeNode in cce.NonNull(backEdgeNodes.Keys))
      {
        Contract.Assert(backEdgeNode != null);
        Debug.Assert(backEdgeNode.TransferCmd is GotoCmd,
          "An node was identified as the source for a backedge, but it does not have a goto command.");
        GotoCmd gotoCmd = backEdgeNode.TransferCmd as GotoCmd;
        if (gotoCmd is { LabelTargets.Count: > 1 })
        {
          // then remove the backedge by removing the target block from the list of gotos
          List<Block> remainingTargets = new List<Block>();
          List<String> remainingLabels = new List<String>();
          Contract.Assume(gotoCmd.LabelNames != null);
          for (int i = 0, n = gotoCmd.LabelTargets.Count; i < n; i++)
          {
            if (gotoCmd.LabelTargets[i] != header)
            {
              remainingTargets.Add(gotoCmd.LabelTargets[i]);
              remainingLabels.Add(gotoCmd.LabelNames[i]);
            }
            else
            {
              RecordCutEdge(edgesCut, backEdgeNode, header);
            }
          }

          gotoCmd.LabelTargets = remainingTargets;
          gotoCmd.LabelNames = remainingLabels;
        }
        else
        {
          // This backedge is the only out-going edge from this node.
          // Add an "assume false" statement to the end of the statements
          // inside of the block and change the goto command to a return command.
          var ac = new AssumeCmd(Token.NoToken, Expr.False);
          backEdgeNode.Cmds.Add(ac);
          backEdgeNode.TransferCmd = new ReturnCmd(backEdgeNode.TransferCmd.tok);
          if (gotoCmd is { LabelTargets.Count: 1 })
          {
            RecordCutEdge(edgesCut, backEdgeNode, gotoCmd.LabelTargets[0]);
          }
        }

        #region Remove the backedge node from the list of predecessor nodes in the header

        List<Block> newPreds = new List<Block>();
        foreach (Block p in header.Predecessors)
        {
          if (p != backEdgeNode)
          {
            newPreds.Add(p);
          }
        }

        header.Predecessors = newPreds;

        #endregion
      }

      #endregion

      #region Collect all variables that are assigned to in all of the natural loops for which this is the header

      List<Variable> varsToHavoc = VarsAssignedInLoop(g, header);
      List<IdentifierExpr> havocExprs = new List<IdentifierExpr>();
      foreach (Variable v in varsToHavoc)
      {
        Contract.Assert(v != null);
        IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
        if (!havocExprs.Contains(ie))
        {
          havocExprs.Add(ie);
        }
      }

      // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
      // the source location for this later on
      HavocCmd hc = new HavocCmd(header.tok, havocExprs);
      List<Cmd> newCmds = new List<Cmd>();
      newCmds.Add(hc);
      foreach (Cmd c in header.Cmds)
      {
        newCmds.Add(c);
      }

      header.Cmds = newCmds;

      #endregion
    }

    #endregion

    #endregion Convert program CFG into a DAG
  }

  private void ConvertCfg2DagkInduction(Implementation impl, Dictionary<Block, List<Block>> edgesCut, int taskID,
    int inductionK)
  {
    // K-induction has not been adapted to be aware of these parameters which standard CFG to DAG transformation uses
    Contract.Requires(edgesCut == null);
    Contract.Requires(taskID == -1);
    Contract.Requires(0 <= inductionK);

    bool contRuleApplication = true;
    while (contRuleApplication)
    {
      contRuleApplication = false;

      #region Use the graph library to figure out where the (natural) loops are

      #region Create the graph by adding the source node and each edge

      Graph<Block> g = Program.GraphFromImpl(impl);

      #endregion

      g.ComputeLoops(); // this is the call that does all of the processing
      if (!g.Reducible)
      {
        throw new VCGenException("Irreducible flow graphs are unsupported.");
      }

      #endregion

      foreach (Block header in cce.NonNull(g.Headers))
      {
        Contract.Assert(header != null);

        #region Debug Tracing

        if (generator.Options.TraceVerify)
        {
          generator.Options.OutputWriter.WriteLine("Applying k-induction rule with k=" + inductionK);
        }

        #endregion

        #region generate the step case

        Block newHeader = DuplicateLoop(impl, g, header, null,
          false, false, "_step_assertion");
        for (int i = 0; i < inductionK; ++i)
        {
          newHeader = DuplicateLoop(impl, g, header, newHeader,
            true, true,
            "_step_" + (inductionK - i));
        }

        #endregion

        #region havoc variables that can be assigned in the loop

        List<Variable> varsToHavoc = VarsAssignedInLoop(g, header);
        List<IdentifierExpr> havocExprs = new List<IdentifierExpr>();
        foreach (Variable v in varsToHavoc)
        {
          Contract.Assert(v != null);
          IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
          if (!havocExprs.Contains(ie))
          {
            havocExprs.Add(ie);
          }
        }

        // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
        // the source location for this later on
        HavocCmd hc = new HavocCmd(newHeader.tok, havocExprs);
        List<Cmd> havocCmds = new List<Cmd>();
        havocCmds.Add(hc);

        var havocBlock = new Block(newHeader.tok, newHeader.Label + "_havoc", havocCmds,
          new GotoCmd(newHeader.tok, new List<Block> { newHeader }));

        impl.Blocks.Add(havocBlock);
        newHeader.Predecessors.Add(havocBlock);
        newHeader = havocBlock;

        #endregion

        #region generate the base case loop copies

        for (int i = 0; i < inductionK; ++i)
        {
          newHeader = DuplicateLoop(impl, g, header, newHeader,
            false, false,
            "_base_" + (inductionK - i));
        }

        #endregion

        #region redirect into the new loop copies and remove the original loop (but don't redirect back-edges)

        IDictionary<Block, object> backEdgeNodes = new Dictionary<Block, object>();
        foreach (Block b in cce.NonNull(g.BackEdgeNodes(header)))
        {
          Contract.Assert(b != null);
          backEdgeNodes.Add(b, null);
        }

        for (int predIndex = 0, n = header.Predecessors.Count; predIndex < n; predIndex++)
        {
          Block pred = cce.NonNull(header.Predecessors[predIndex]);
          if (!backEdgeNodes.ContainsKey(pred))
          {
            GotoCmd gc = pred.TransferCmd as GotoCmd;
            Contract.Assert(gc != null);
            for (int i = 0; i < gc.LabelTargets.Count; ++i)
            {
              if (gc.LabelTargets[i] == header)
              {
                gc.LabelTargets[i] = newHeader;
                gc.LabelNames[i] = newHeader.Label;
                newHeader.Predecessors.Add(pred);
              }
            }
          }
        }

        impl.PruneUnreachableBlocks(generator.Options);

        #endregion

        contRuleApplication = true;
        break;
      }
    }

    ConditionGeneration.ResetPredecessors(impl.Blocks);
    impl.FreshenCaptureStates();
  }
  
  private static void RecordCutEdge(Dictionary<Block, List<Block>> edgesCut, Block from, Block to) {
    edgesCut?.GetOrCreate(from, () => new List<Block>()).Add(to);
  }
  
  private static List<Variable> VarsAssignedInLoop(Graph<Block> g, Block header)
  {
    List<Variable> varsToHavoc = new List<Variable>();
    foreach (var backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
    {
      Contract.Assert(backEdgeNode != null);
      foreach (Block b in g.NaturalLoops(header, backEdgeNode))
      {
        Contract.Assert(b != null);
        foreach (var c in b.Cmds)
        {
          Contract.Assert(c != null);
          varsToHavoc.AddRange(c.GetAssignedVariables());
        }
      }
    }

    return varsToHavoc;
  }

  public static IEnumerable<Variable> VarsReferencedInLoop(Graph<Block> g, Block header)
  {
    HashSet<Variable> referencedVars = new HashSet<Variable>();
    foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
    {
      Contract.Assert(backEdgeNode != null);
      foreach (Block b in g.NaturalLoops(header, backEdgeNode))
      {
        Contract.Assert(b != null);
        foreach (Cmd c in b.Cmds)
        {
          Contract.Assert(c != null);
          var Collector = new VariableCollector();
          Collector.Visit(c);
          foreach (var v in Collector.usedVars)
          {
            referencedVars.Add(v);
          }
        }
      }
    }

    return referencedVars;
  }

  private Block DuplicateLoop(Implementation impl, Graph<Block> g,
    Block header, Block nextHeader, bool cutExits,
    bool toAssumptions, string suffix)
  {
    var ori2CopiedBlocks = new Dictionary<Block, Block>();
    var duplicator = new Duplicator();

    #region create copies of all blocks in the loop

    foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
    {
      Contract.Assert(backEdgeNode != null);
      foreach (Block b in g.NaturalLoops(header, backEdgeNode))
      {
        Contract.Assert(b != null);
        if (ori2CopiedBlocks.ContainsKey(b)) {
          continue;
        }

        Block copy = (Block)duplicator.Visit(b);
        copy.Cmds = new List<Cmd>(copy
          .Cmds); // Philipp Ruemmer commented that this was necessary due to a bug in the Duplicator.  That was a long time; worth checking whether this has been fixed
        copy.Predecessors = new List<Block>();
        copy.Label += suffix;

        #region turn asserts into assumptions

        if (toAssumptions)
        {
          for (int i = 0; i < copy.Cmds.Count; ++i)
          {
            if (copy.Cmds[i] is AssertCmd ac)
            {
              copy.Cmds[i] = new AssumeCmd(ac.tok, ac.Expr);
            }
          }
        }

        #endregion

        impl.Blocks.Add(copy);
        ori2CopiedBlocks.Add(b, copy);
      }
    }

    #endregion

    #region adjust the transfer commands of the newly created blocks

    foreach (KeyValuePair<Block, Block> pair in ori2CopiedBlocks)
    {
      var copy = pair.Value;
      if (copy.TransferCmd is GotoCmd gc)
      {
        List<Block> newTargets = new List<Block>();
        List<string> newLabels = new List<string>();

        for (int i = 0; i < gc.LabelTargets.Count; ++i)
        {
          if (gc.LabelTargets[i] == header)
          {
            if (nextHeader != null)
            {
              newTargets.Add(nextHeader);
              newLabels.Add(nextHeader.Label);
              nextHeader.Predecessors.Add(copy);
            }
          }
          else if (ori2CopiedBlocks.TryGetValue(gc.LabelTargets[i], out var newTarget))
          {
            newTargets.Add(newTarget);
            newLabels.Add(newTarget.Label);
            newTarget.Predecessors.Add(copy);
          }
          else if (!cutExits)
          {
            newTargets.Add(gc.LabelTargets[i]);
            newLabels.Add(gc.LabelNames[i]);
            gc.LabelTargets[i].Predecessors.Add(copy);
          }
        }

        if (newTargets.Count == 0)
        {
          // if no targets are left, we assume false and return
          copy.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
          copy.TransferCmd = new ReturnCmd(Token.NoToken);
        }
        else
        {
          copy.TransferCmd = new GotoCmd(gc.tok, newLabels, newTargets);
        }
      }
      else if (cutExits && (copy.TransferCmd is ReturnCmd))
      {
        // because return is a kind of exit from the loop, we
        // assume false to cut this path
        copy.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
      }
    }

    #endregion

    return ori2CopiedBlocks[header];
  }
}