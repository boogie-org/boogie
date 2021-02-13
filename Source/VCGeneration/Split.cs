using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{
  using Bpl = Microsoft.Boogie;
  using System.Threading.Tasks;
  
  class Split
    {
      class BlockStats
      {
        public bool big_block;
        public int id;
        public double assertion_cost;
        public double assumption_cost; // before multiplier
        public double incomming_paths;

        public List<Block> /*!>!*/
          virtual_successors = new List<Block>();

        public List<Block> /*!>!*/
          virtual_predecesors = new List<Block>();

        public HashSet<Block> reachable_blocks;
        public readonly Block block;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
          Contract.Invariant(cce.NonNullElements(virtual_successors));
          Contract.Invariant(cce.NonNullElements(virtual_predecesors));
          Contract.Invariant(block != null);
        }


        public BlockStats(Block b, int i)
        {
          Contract.Requires(b != null);
          block = b;
          assertion_cost = -1;
          id = i;
        }
      }

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(cce.NonNullElements(blocks));
        Contract.Invariant(cce.NonNullElements(big_blocks));
        Contract.Invariant(cce.NonNullDictionaryAndValues(stats));
        Contract.Invariant(cce.NonNullElements(assumized_branches));
        Contract.Invariant(gotoCmdOrigins != null);
        Contract.Invariant(parent != null);
        Contract.Invariant(impl != null);
        Contract.Invariant(copies != null);
        Contract.Invariant(cce.NonNull(protected_from_assert_to_assume));
        Contract.Invariant(cce.NonNull(keep_at_all));
      }


      readonly List<Block> blocks;
      readonly List<Block> big_blocks = new List<Block>();

      readonly Dictionary<Block /*!*/, BlockStats /*!*/> /*!*/
        stats = new Dictionary<Block /*!*/, BlockStats /*!*/>();

      readonly int id;
      static int current_id = -1;
      Block split_block;
      bool assert_to_assume;

      List<Block /*!*/> /*!*/
        assumized_branches = new List<Block /*!*/>();

      double score;
      bool score_computed;
      double total_cost;
      int assertion_count;
      double assertion_cost; // without multiplication by paths

      Dictionary<TransferCmd, ReturnCmd> /*!*/
        gotoCmdOrigins;

      readonly public VCGen /*!*/
        parent;

      Implementation /*!*/
        impl;

      Dictionary<Block /*!*/, Block /*!*/> /*!*/
        copies = new Dictionary<Block /*!*/, Block /*!*/>();

      bool doing_slice;
      double slice_initial_limit;
      double slice_limit;
      bool slice_pos;

      HashSet<Block /*!*/> /*!*/
        protected_from_assert_to_assume = new HashSet<Block /*!*/>();

      HashSet<Block /*!*/> /*!*/
        keep_at_all = new HashSet<Block /*!*/>();

      // async interface
      private Checker checker;
      private int splitNo;
      internal VCGen.ErrorReporter reporter;

      public Split(List<Block /*!*/> /*!*/ blocks, Dictionary<TransferCmd, ReturnCmd> /*!*/ gotoCmdOrigins,
        VCGen /*!*/ par, Implementation /*!*/ impl)
      {
        Contract.Requires(cce.NonNullElements(blocks));
        Contract.Requires(gotoCmdOrigins != null);
        Contract.Requires(par != null);
        Contract.Requires(impl != null);
        this.blocks = blocks;
        this.gotoCmdOrigins = gotoCmdOrigins;
        this.parent = par;
        this.impl = impl;
        this.id = Interlocked.Increment(ref current_id);
      }

      public double Cost
      {
        get
        {
          ComputeBestSplit();
          return total_cost;
        }
      }

      public bool LastChance
      {
        get
        {
          ComputeBestSplit();
          return assertion_count == 1 && score < 0;
        }
      }

      public string Stats
      {
        get
        {
          ComputeBestSplit();
          return string.Format("(cost:{0:0}/{1:0}{2})", total_cost, assertion_cost, LastChance ? " last" : "");
        }
      }

      public void DumpDot(int no)
      {
        using (System.IO.StreamWriter sw = System.IO.File.CreateText(string.Format("split.{0}.dot", no)))
        {
          sw.WriteLine("digraph G {");

          ComputeBestSplit();
          List<Block> saved = assumized_branches;
          Contract.Assert(saved != null);
          assumized_branches = new List<Block>();
          DoComputeScore(false);
          assumized_branches = saved;

          foreach (Block b in big_blocks)
          {
            Contract.Assert(b != null);
            BlockStats s = GetBlockStats(b);
            foreach (Block t in s.virtual_successors)
            {
              Contract.Assert(t != null);
              sw.WriteLine("n{0} -> n{1};", s.id, GetBlockStats(t).id);
            }

            sw.WriteLine("n{0} [label=\"{1}:\\n({2:0.0}+{3:0.0})*{4:0.0}\"{5}];",
              s.id, b.Label,
              s.assertion_cost, s.assumption_cost, s.incomming_paths,
              s.assertion_cost > 0 ? ",shape=box" : "");
          }

          sw.WriteLine("}");
          sw.Close();
        }

        string filename = string.Format("split.{0}.bpl", no);
        using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename))
        {
          int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
          CommandLineOptions.Clo.PrintUnstructured = 2; // print only the unstructured program
          bool oldPrintDesugaringSetting = CommandLineOptions.Clo.PrintDesugarings;
          CommandLineOptions.Clo.PrintDesugarings = false;
          List<Block> backup = impl.Blocks;
          Contract.Assert(backup != null);
          impl.Blocks = blocks;
          impl.Emit(new TokenTextWriter(filename, sw, /*setTokens=*/ false, /*pretty=*/ false), 0);
          impl.Blocks = backup;
          CommandLineOptions.Clo.PrintDesugarings = oldPrintDesugaringSetting;
          CommandLineOptions.Clo.PrintUnstructured = oldPrintUnstructured;
        }
      }

      int bsid;

      BlockStats GetBlockStats(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<BlockStats>() != null);

        BlockStats s;
        if (!stats.TryGetValue(b, out s))
        {
          s = new BlockStats(b, bsid++);
          stats[b] = s;
        }

        return cce.NonNull(s);
      }

      double AssertionCost(PredicateCmd c)
      {
        return 1.0;
      }

      void CountAssertions(Block b)
      {
        Contract.Requires(b != null);
        BlockStats s = GetBlockStats(b);
        if (s.assertion_cost >= 0)
          return; // already done
        s.big_block = true;
        s.assertion_cost = 0;
        s.assumption_cost = 0;
        foreach (Cmd c in b.Cmds)
        {
          if (c is AssertCmd)
          {
            double cost = AssertionCost((AssertCmd) c);
            s.assertion_cost += cost;
            assertion_count++;
            assertion_cost += cost;
          }
          else if (c is AssumeCmd)
          {
            s.assumption_cost += AssertionCost((AssumeCmd) c);
          }
        }

        foreach (Block c in b.Exits())
        {
          Contract.Assert(c != null);
          s.virtual_successors.Add(c);
        }

        if (s.virtual_successors.Count == 1)
        {
          Block next = s.virtual_successors[0];
          BlockStats se = GetBlockStats(next);
          CountAssertions(next);
          if (next.Predecessors.Count > 1 || se.virtual_successors.Count != 1)
            return;
          s.virtual_successors[0] = se.virtual_successors[0];
          s.assertion_cost += se.assertion_cost;
          s.assumption_cost += se.assumption_cost;
          se.big_block = false;
        }
      }

      HashSet<Block /*!*/> /*!*/ ComputeReachableNodes(Block /*!*/ b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(cce.NonNull(Contract.Result<HashSet<Block /*!*/>>()));
        BlockStats s = GetBlockStats(b);
        if (s.reachable_blocks != null)
        {
          return s.reachable_blocks;
        }

        HashSet<Block /*!*/> blocks = new HashSet<Block /*!*/>();
        s.reachable_blocks = blocks;
        blocks.Add(b);
        foreach (Block /*!*/ succ in b.Exits())
        {
          Contract.Assert(succ != null);
          foreach (Block r in ComputeReachableNodes(succ))
          {
            Contract.Assert(r != null);
            blocks.Add(r);
          }
        }

        return blocks;
      }

      double ProverCost(double vc_cost)
      {
        return vc_cost * vc_cost;
      }

      void ComputeBestSplit()
      {
        if (score_computed)
          return;
        score_computed = true;

        assertion_count = 0;

        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          CountAssertions(b);
        }

        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          BlockStats bs = GetBlockStats(b);
          if (bs.big_block)
          {
            big_blocks.Add(b);
            foreach (Block ch in bs.virtual_successors)
            {
              Contract.Assert(ch != null);
              BlockStats chs = GetBlockStats(ch);
              if (!chs.big_block)
              {
                Console.WriteLine("non-big {0} accessed from {1}", ch, b);
                DumpDot(-1);
                Contract.Assert(false);
                throw new cce.UnreachableException();
              }

              chs.virtual_predecesors.Add(b);
            }
          }
        }

        assumized_branches.Clear();
        total_cost = ProverCost(DoComputeScore(false));

        score = double.PositiveInfinity;
        Block best_split = null;
        List<Block> saved_branches = new List<Block>();

        foreach (Block b in big_blocks)
        {
          Contract.Assert(b != null);
          GotoCmd gt = b.TransferCmd as GotoCmd;
          if (gt == null)
            continue;
          List<Block> targ = cce.NonNull(gt.labelTargets);
          if (targ.Count < 2)
            continue;
          // caution, we only consider two first exits

          double left0, right0, left1, right1;
          split_block = b;

          assumized_branches.Clear();
          assumized_branches.Add(cce.NonNull(targ[0]));
          left0 = DoComputeScore(true);
          right0 = DoComputeScore(false);

          assumized_branches.Clear();
          for (int idx = 1; idx < targ.Count; idx++)
          {
            assumized_branches.Add(cce.NonNull(targ[idx]));
          }

          left1 = DoComputeScore(true);
          right1 = DoComputeScore(false);

          double current_score = ProverCost(left1) + ProverCost(right1);
          double other_score = ProverCost(left0) + ProverCost(right0);

          if (other_score < current_score)
          {
            current_score = other_score;
            assumized_branches.Clear();
            assumized_branches.Add(cce.NonNull(targ[0]));
          }

          if (current_score < score)
          {
            score = current_score;
            best_split = split_block;
            saved_branches.Clear();
            saved_branches.AddRange(assumized_branches);
          }
        }

        if (CommandLineOptions.Clo.VcsPathSplitMult * score > total_cost)
        {
          split_block = null;
          score = -1;
        }
        else
        {
          assumized_branches = saved_branches;
          split_block = best_split;
        }
      }

      void UpdateIncommingPaths(BlockStats s)
      {
        Contract.Requires(s != null);
        if (s.incomming_paths < 0.0)
        {
          int count = 0;
          s.incomming_paths = 0.0;
          if (!keep_at_all.Contains(s.block))
            return;
          foreach (Block b in s.virtual_predecesors)
          {
            Contract.Assert(b != null);
            BlockStats ch = GetBlockStats(b);
            Contract.Assert(ch != null);
            UpdateIncommingPaths(ch);
            if (ch.incomming_paths > 0.0)
            {
              s.incomming_paths += ch.incomming_paths;
              count++;
            }
          }

          if (count > 1)
          {
            s.incomming_paths *= CommandLineOptions.Clo.VcsPathJoinMult;
          }
        }
      }

      void ComputeBlockSetsHelper(Block b, bool allow_small)
      {
        Contract.Requires(b != null);
        if (keep_at_all.Contains(b))
          return;
        keep_at_all.Add(b);

        if (allow_small)
        {
          foreach (Block ch in b.Exits())
          {
            Contract.Assert(ch != null);
            if (b == split_block && assumized_branches.Contains(ch))
              continue;
            ComputeBlockSetsHelper(ch, allow_small);
          }
        }
        else
        {
          foreach (Block ch in GetBlockStats(b).virtual_successors)
          {
            Contract.Assert(ch != null);
            if (b == split_block && assumized_branches.Contains(ch))
              continue;
            ComputeBlockSetsHelper(ch, allow_small);
          }
        }
      }

      void ComputeBlockSets(bool allow_small)
      {
        protected_from_assert_to_assume.Clear();
        keep_at_all.Clear();

        Debug.Assert(split_block == null || GetBlockStats(split_block).big_block);
        Debug.Assert(GetBlockStats(blocks[0]).big_block);

        if (assert_to_assume)
        {
          foreach (Block b in allow_small ? blocks : big_blocks)
          {
            Contract.Assert(b != null);
            if (ComputeReachableNodes(b).Contains(cce.NonNull(split_block)))
            {
              keep_at_all.Add(b);
            }
          }

          foreach (Block b in assumized_branches)
          {
            Contract.Assert(b != null);
            foreach (Block r in ComputeReachableNodes(b))
            {
              Contract.Assert(r != null);
              if (allow_small || GetBlockStats(r).big_block)
              {
                keep_at_all.Add(r);
                protected_from_assert_to_assume.Add(r);
              }
            }
          }
        }
        else
        {
          ComputeBlockSetsHelper(blocks[0], allow_small);
        }
      }

      bool ShouldAssumize(Block b)
      {
        Contract.Requires(b != null);
        return assert_to_assume && !protected_from_assert_to_assume.Contains(b);
      }

      double DoComputeScore(bool aa)
      {
        assert_to_assume = aa;
        ComputeBlockSets(false);

        foreach (Block b in big_blocks)
        {
          Contract.Assert(b != null);
          GetBlockStats(b).incomming_paths = -1.0;
        }

        GetBlockStats(blocks[0]).incomming_paths = 1.0;

        double cost = 0.0;
        foreach (Block b in big_blocks)
        {
          Contract.Assert(b != null);
          if (keep_at_all.Contains(b))
          {
            BlockStats s = GetBlockStats(b);
            UpdateIncommingPaths(s);
            double local = s.assertion_cost;
            if (ShouldAssumize(b))
            {
              local = (s.assertion_cost + s.assumption_cost) * CommandLineOptions.Clo.VcsAssumeMult;
            }
            else
            {
              local = s.assumption_cost * CommandLineOptions.Clo.VcsAssumeMult + s.assertion_cost;
            }

            local = local + local * s.incomming_paths * CommandLineOptions.Clo.VcsPathCostMult;
            cost += local;
          }
        }

        return cost;
      }

      List<Cmd> SliceCmds(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);

        List<Cmd> seq = b.Cmds;
        Contract.Assert(seq != null);
        if (!doing_slice && !ShouldAssumize(b))
          return seq;
        List<Cmd> res = new List<Cmd>();
        foreach (Cmd c in seq)
        {
          Contract.Assert(c != null);
          AssertCmd a = c as AssertCmd;
          Cmd the_new = c;
          bool swap = false;
          if (a != null)
          {
            if (doing_slice)
            {
              double cost = AssertionCost(a);
              bool first = (slice_limit - cost) >= 0 || slice_initial_limit == slice_limit;
              slice_limit -= cost;
              swap = slice_pos == first;
            }
            else if (assert_to_assume)
            {
              swap = true;
            }
            else
            {
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }

            if (swap)
            {
              the_new = VCGen.AssertTurnedIntoAssume(a);
            }
          }

          res.Add(the_new);
        }

        return res;
      }

      Block CloneBlock(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<Block>() != null);

        Block res;
        if (copies.TryGetValue(b, out res))
        {
          return cce.NonNull(res);
        }

        res = new Block(b.tok, b.Label, SliceCmds(b), b.TransferCmd);
        GotoCmd gt = b.TransferCmd as GotoCmd;
        copies[b] = res;
        if (gt != null)
        {
          GotoCmd newGoto = new GotoCmd(gt.tok, new List<String>(), new List<Block>());
          res.TransferCmd = newGoto;
          int pos = 0;
          foreach (Block ch in cce.NonNull(gt.labelTargets))
          {
            Contract.Assert(ch != null);
            Contract.Assert(doing_slice ||
                            (assert_to_assume || (keep_at_all.Contains(ch) || assumized_branches.Contains(ch))));
            if (doing_slice ||
                ((b != split_block || assumized_branches.Contains(ch) == assert_to_assume) &&
                 keep_at_all.Contains(ch)))
            {
              newGoto.AddTarget(CloneBlock(ch));
            }

            pos++;
          }
        }

        return res;
      }

      Split DoSplit()
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        copies.Clear();
        CloneBlock(blocks[0]);
        List<Block> newBlocks = new List<Block>();
        Dictionary<TransferCmd, ReturnCmd> newGotoCmdOrigins = new Dictionary<TransferCmd, ReturnCmd>();
        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          Block tmp;
          if (copies.TryGetValue(b, out tmp))
          {
            newBlocks.Add(cce.NonNull(tmp));
            if (gotoCmdOrigins.ContainsKey(b.TransferCmd))
            {
              newGotoCmdOrigins[tmp.TransferCmd] = gotoCmdOrigins[b.TransferCmd];
            }

            foreach (Block p in b.Predecessors)
            {
              Contract.Assert(p != null);
              Block tmp2;
              if (copies.TryGetValue(p, out tmp2))
              {
                tmp.Predecessors.Add(tmp2);
              }
            }
          }
        }

        return new Split(newBlocks, newGotoCmdOrigins, parent, impl);
      }

      Split SplitAt(int idx)
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        assert_to_assume = idx == 0;
        doing_slice = false;
        ComputeBlockSets(true);

        return DoSplit();
      }

      Split SliceAsserts(double limit, bool pos)
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        slice_pos = pos;
        slice_limit = limit;
        slice_initial_limit = limit;
        doing_slice = true;
        Split r = DoSplit();
        /*
        Console.WriteLine("split {0} / {1} -->", limit, pos);
        List<Block!> tmp = impl.Blocks;
        impl.Blocks = r.blocks;
        EmitImpl(impl, false);
        impl.Blocks = tmp;
        */

        return r;
      }

      void Print()
      {
        List<Block> tmp = impl.Blocks;
        Contract.Assert(tmp != null);
        impl.Blocks = blocks;
        ConditionGeneration.EmitImpl(impl, false);
        impl.Blocks = tmp;
      }

      public Counterexample ToCounterexample(ProverContext context)
      {
        Contract.Requires(context != null);
        Contract.Ensures(Contract.Result<Counterexample>() != null);

        List<Block> trace = new List<Block>();
        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          trace.Add(b);
        }

        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          foreach (Cmd c in b.Cmds)
          {
            Contract.Assert(c != null);
            if (c is AssertCmd)
            {
              return VCGen.AssertCmdToCounterexample((AssertCmd) c, cce.NonNull(b.TransferCmd), trace, null, null, null, context);
            }
          }
        }

        Contract.Assume(false);
        throw new cce.UnreachableException();
      }

      /// <summary>
      /// Starting from the 0-index "split_here" annotation in begin, verifies until it reaches a subsequent "split_here" annotation
      /// Returns a list of blocks where all code not verified has asserts converted into assumes
      /// </summary>
      /// <param name="blocks">Implementation's collection of blocks</param>
      /// <param name="begin">Block containing the first split_here from which to start verifying</param>
      /// <param name="begin_split_id">0-based ID of the "split_here" annotation within begin at which to start verifying</param>
      /// <param name="blockInternalSplit">True if the entire split is contained within block begin</param>
      /// <param name="endPoints">Set of all blocks containing a "split_here" annotation</param>
      /// <returns></returns>
      // Note: Current implementation may over report errors.
      //       For example, if the control flow graph is a diamond (e.g., A -> B, C, B->D, C->D),
      //       and there is a split in B and an error in D, then D will be verified twice and hence report the error twice.
      //       Best solution may be to memoize blocks that have been fully verified and be sure not to verify them again
      private static List<Block> DoManualSplit(List<Block> blocks, Block begin, int begin_split_id,
        bool blockInternalSplit, IEnumerable<Block> endPoints)
      {
        // Compute the set of blocks reachable from begin but not included in endPoints.  These will be verified in their entirety.
        var blocksToVerifyEntirely = new HashSet<Block>();
        var reachableEndPoints =
          new HashSet<Block>(); // Reachable end points will be verified up to their first split point
        var todo = new Stack<Block>();
        todo.Push(begin);
        while (todo.Count > 0)
        {
          var currentBlock = todo.Pop();
          if (blocksToVerifyEntirely.Contains(currentBlock)) continue;
          blocksToVerifyEntirely.Add(currentBlock);
          var exit = currentBlock.TransferCmd as GotoCmd;
          if (exit != null)
            foreach (Block targetBlock in exit.labelTargets)
            {
              if (!endPoints.Contains(targetBlock))
              {
                todo.Push(targetBlock);
              }
              else
              {
                reachableEndPoints.Add(targetBlock);
              }
            }
        }

        blocksToVerifyEntirely.Remove(begin);

        // Convert assumes to asserts in "unreachable" blocks, including portions of blocks containing "split_here"
        var newBlocks = new List<Block>(blocks.Count()); // Copies of the original blocks
        var duplicator = new Duplicator();
        var oldToNewBlockMap =
          new Dictionary<Block, Block>(blocks.Count()); // Maps original blocks to their new copies in newBlocks

        foreach (var currentBlock in blocks)
        {
          var newBlock = (Block) duplicator.VisitBlock(currentBlock);
          oldToNewBlockMap[currentBlock] = newBlock;
          newBlocks.Add(newBlock);

          if (!blockInternalSplit && blocksToVerifyEntirely.Contains(currentBlock))
            continue; // All reachable blocks must be checked in their entirety, so don't change anything
          // Otherwise, we only verify a portion of the current block, so we'll need to look at each of its commands                 

          // !verify -> convert assert to assume
          var verify =
            (currentBlock == begin &&
             begin_split_id == -1
            ) // -1 tells us to start verifying from the very beginning (i.e., there is no split in the begin block)
            || (
              reachableEndPoints
                .Contains(currentBlock) // This endpoint is reachable from begin, so we verify until we hit the first split point
              && !blockInternalSplit); // Don't bother verifying if all of the splitting is within the begin block
          var newCmds = new List<Cmd>();
          var split_here_count = 0;

          foreach (Cmd c in currentBlock.Cmds)
          {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "split_here"))
            {
              if (currentBlock == begin)
              {
                // Verify everything between the begin_split_id we were given and the next split
                if (split_here_count == begin_split_id)
                {
                  verify = true;
                }
                else if (split_here_count == begin_split_id + 1)
                {
                  verify = false;
                }
              }
              else
              {
                // We're in an endPoint so we stop verifying as soon as we hit a "split_here"
                verify = false;
              }

              split_here_count++;
            }

            var asrt = c as AssertCmd;
            if (verify || asrt == null)
              newCmds.Add(c);
            else
              newCmds.Add(VCGen.AssertTurnedIntoAssume(asrt));
          }

          newBlock.Cmds = newCmds;
        }

        // Patch the edges between the new blocks
        foreach (var oldBlock in blocks)
        {
          if (oldBlock.TransferCmd is ReturnCmd)
          {
            continue;
          }

          var gotoCmd = (GotoCmd) oldBlock.TransferCmd;
          var newLabelTargets = new List<Block>(gotoCmd.labelTargets.Count());
          var newLabelNames = new List<string>(gotoCmd.labelTargets.Count());
          foreach (var target in gotoCmd.labelTargets)
          {
            newLabelTargets.Add(oldToNewBlockMap[target]);
            newLabelNames.Add(oldToNewBlockMap[target].Label);
          }

          oldToNewBlockMap[oldBlock].TransferCmd = new GotoCmd(gotoCmd.tok, newLabelNames, newLabelTargets);
        }

        return newBlocks;
      }

      public static List<Split /*!*/> FindManualSplits(Implementation /*!*/ impl,
        Dictionary<TransferCmd, ReturnCmd> /*!*/ gotoCmdOrigins, VCGen /*!*/ par)
      {
        Contract.Requires(impl != null);
        Contract.Ensures(Contract.Result<List<Split>>() == null || cce.NonNullElements(Contract.Result<List<Split>>()));

        var splitPoints = new Dictionary<Block, int>();
        foreach (var b in impl.Blocks)
        {
          foreach (Cmd c in b.Cmds)
          {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "split_here"))
            {
              int count;
              splitPoints.TryGetValue(b, out count);
              splitPoints[b] = count + 1;
            }
          }
        }

        if (splitPoints.Count() == 0)
        {
          // No manual split points here
          return null;
        }

        List<Split> splits = new List<Split>();
        Block entryPoint = impl.Blocks[0];
        var newEntryBlocks = DoManualSplit(impl.Blocks, entryPoint, -1, splitPoints.Keys.Contains(entryPoint),
          splitPoints.Keys);
        splits.Add(new Split(newEntryBlocks, gotoCmdOrigins, par,
          impl)); // REVIEW: Does gotoCmdOrigins need to be changed at all?        

        foreach (KeyValuePair<Block, int> pair in splitPoints)
        {
          for (int i = 0; i < pair.Value; i++)
          {
            bool blockInternalSplit =
              i < pair.Value - 1; // There's at least one more split, after this one, in the current block
            var newBlocks = DoManualSplit(impl.Blocks, pair.Key, i, blockInternalSplit, splitPoints.Keys);
            Split s = new Split(newBlocks, gotoCmdOrigins, par,
              impl); // REVIEW: Does gotoCmdOrigins need to be changed at all?
            splits.Add(s);
          }
        }

        return splits;
      }

      public static List<Split /*!*/> /*!*/ DoSplit(Split initial, double max_cost, int max)
      {
        Contract.Requires(initial != null);
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Split>>()));

        List<Split> res = new List<Split>();
        res.Add(initial);

        while (res.Count < max)
        {
          Split best = null;
          int best_idx = 0, pos = 0;
          foreach (Split s in res)
          {
            Contract.Assert(s != null);
            s.ComputeBestSplit(); // TODO check total_cost first
            if (s.total_cost > max_cost &&
                (best == null || best.total_cost < s.total_cost) &&
                (s.assertion_count > 1 || s.split_block != null))
            {
              best = s;
              best_idx = pos;
            }

            pos++;
          }

          if (best == null)
            break; // no split found

          Split s0, s1;

          bool split_stats = CommandLineOptions.Clo.TraceVerify;

          if (split_stats)
          {
            Console.WriteLine("{0} {1} -->", best.split_block == null ? "SLICE" : ("SPLIT@" + best.split_block.Label),
              best.Stats);
            if (best.split_block != null)
            {
              GotoCmd g = best.split_block.TransferCmd as GotoCmd;
              if (g != null)
              {
                Console.Write("    exits: ");
                foreach (Block b in cce.NonNull(g.labelTargets))
                {
                  Contract.Assert(b != null);
                  Console.Write("{0} ", b.Label);
                }

                Console.WriteLine("");
                Console.Write("    assumized: ");
                foreach (Block b in best.assumized_branches)
                {
                  Contract.Assert(b != null);
                  Console.Write("{0} ", b.Label);
                }

                Console.WriteLine("");
              }
            }
          }

          if (best.split_block != null)
          {
            s0 = best.SplitAt(0);
            s1 = best.SplitAt(1);
          }
          else
          {
            best.split_block = null;
            s0 = best.SliceAsserts(best.assertion_cost / 2, true);
            s1 = best.SliceAsserts(best.assertion_cost / 2, false);
          }

          if (true)
          {
            List<Block> ss = new List<Block>();
            ss.Add(s0.blocks[0]);
            ss.Add(s1.blocks[0]);
            try
            {
              best.SoundnessCheck(new HashSet<List<Block>>(new BlockListComparer()), best.blocks[0], ss);
            }
            catch (System.Exception e)
            {
              Console.WriteLine(e);
              best.DumpDot(-1);
              s0.DumpDot(-2);
              s1.DumpDot(-3);
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }
          }

          if (split_stats)
          {
            s0.ComputeBestSplit();
            s1.ComputeBestSplit();
            Console.WriteLine("    --> {0}", s0.Stats);
            Console.WriteLine("    --> {0}", s1.Stats);
          }

          if (CommandLineOptions.Clo.TraceVerify)
          {
            best.Print();
          }

          res[best_idx] = s0;
          res.Add(s1);
        }

        return res;
      }

      class BlockListComparer : IEqualityComparer<List<Block>>
      {
        public bool Equals(List<Block> x, List<Block> y)
        {
          return x == y || x.SequenceEqual(y);
        }

        public int GetHashCode(List<Block> obj)
        {
          int h = 0;
          Contract.Assume(obj != null);
          foreach (var b in obj)
          {
            if (b != null)
            {
              h += b.GetHashCode();
            }
          }

          return h;
        }
      }

      public Checker Checker
      {
        get
        {
          Contract.Ensures(Contract.Result<Checker>() != null);

          Contract.Assert(checker != null);
          return checker;
        }
      }

      public Task ProverTask
      {
        get
        {
          Contract.Assert(checker != null);
          return checker.ProverTask;
        }
      }

      public void ReadOutcome(ref ConditionGeneration.Outcome cur_outcome, out bool prover_failed)
      {
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        ProverInterface.Outcome outcome = cce.NonNull(checker).ReadOutcome();

        if (CommandLineOptions.Clo.Trace && splitNo >= 0)
        {
          System.Console.WriteLine("      --> split #{0} done,  [{1} s] {2}", splitNo,
            checker.ProverRunTime.TotalSeconds, outcome);
        }

        if (CommandLineOptions.Clo.VcsDumpSplits)
        {
          DumpDot(splitNo);
        }

        prover_failed = false;

        switch (outcome)
        {
          case ProverInterface.Outcome.Valid:
            return;
          case ProverInterface.Outcome.Invalid:
            cur_outcome = ConditionGeneration.Outcome.Errors;
            return;
          case ProverInterface.Outcome.OutOfMemory:
            prover_failed = true;
            if (cur_outcome != ConditionGeneration.Outcome.Errors && cur_outcome != ConditionGeneration.Outcome.Inconclusive)
              cur_outcome = ConditionGeneration.Outcome.OutOfMemory;
            return;
          case ProverInterface.Outcome.TimeOut:
            prover_failed = true;
            if (cur_outcome != ConditionGeneration.Outcome.Errors && cur_outcome != ConditionGeneration.Outcome.Inconclusive)
              cur_outcome = ConditionGeneration.Outcome.TimedOut;
            return;
          case ProverInterface.Outcome.OutOfResource:
            prover_failed = true;
            if (cur_outcome != ConditionGeneration.Outcome.Errors && cur_outcome != ConditionGeneration.Outcome.Inconclusive)
              cur_outcome = ConditionGeneration.Outcome.OutOfResource;
            return;
          case ProverInterface.Outcome.Undetermined:
            if (cur_outcome != ConditionGeneration.Outcome.Errors)
              cur_outcome = ConditionGeneration.Outcome.Inconclusive;
            return;
          default:
            Contract.Assert(false);
            throw new cce.UnreachableException();
        }
      }

      /// <summary>
      /// As a side effect, updates "this.parent.CumulativeAssertionCount".
      /// </summary>
      public void BeginCheck(Checker checker, VerifierCallback callback, ModelViewInfo mvInfo, int no, int timeout, int rlimit)
      {
        Contract.Requires(checker != null);
        Contract.Requires(callback != null);

        splitNo = no;

        impl.Blocks = blocks;

        this.checker = checker;

        Dictionary<int, Absy> label2absy = new Dictionary<int, Absy>();

        ProverContext ctx = checker.TheoremProver.Context;
        Boogie2VCExprTranslator bet = ctx.BoogieExprTranslator;
        var cc = new VCGen.CodeExprConversionClosure(label2absy, ctx);
        bet.SetCodeExprConverter(cc.CodeExprToVerificationCondition);

        var exprGen = ctx.ExprGen;
        VCExpr controlFlowVariableExpr = exprGen.Integer(BigNum.ZERO);

        VCExpr vc = parent.GenerateVCAux(impl, controlFlowVariableExpr, label2absy, checker.TheoremProver.Context);
        Contract.Assert(vc != null);

        VCExpr controlFlowFunctionAppl =
          exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
        VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
        vc = exprGen.Implies(eqExpr, vc);
        reporter = new VCGen.ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, parent.debugInfos, callback,
          mvInfo, this.Checker.TheoremProver.Context, parent.program);

        if (CommandLineOptions.Clo.TraceVerify && no >= 0)
        {
          Console.WriteLine("-- after split #{0}", no);
          Print();
        }

        string desc = cce.NonNull(impl.Name);
        if (no >= 0)
          desc += "_split" + no;
        checker.BeginCheck(desc, vc, reporter, timeout, rlimit, impl.RandomSeed);
      }

      private void SoundnessCheck(HashSet<List<Block> /*!*/> /*!*/ cache, Block /*!*/ orig,
        List<Block /*!*/> /*!*/ copies)
      {
        Contract.Requires(cce.NonNull(cache));
        Contract.Requires(orig != null);
        Contract.Requires(copies != null);
        {
          var t = new List<Block> {orig};
          foreach (Block b in copies)
          {
            Contract.Assert(b != null);
            t.Add(b);
          }

          if (cache.Contains(t))
          {
            return;
          }

          cache.Add(t);
        }

        for (int i = 0; i < orig.Cmds.Count; ++i)
        {
          Cmd cmd = orig.Cmds[i];
          if (cmd is AssertCmd)
          {
            int found = 0;
            foreach (Block c in copies)
            {
              Contract.Assert(c != null);
              if (c.Cmds[i] == cmd)
              {
                found++;
              }
            }

            if (found == 0)
            {
              throw new System.Exception(string.Format("missing assertion: {0}({1})", cmd.tok.filename, cmd.tok.line));
            }
          }
        }

        foreach (Block exit in orig.Exits())
        {
          Contract.Assert(exit != null);
          List<Block> newcopies = new List<Block>();
          foreach (Block c in copies)
          {
            foreach (Block cexit in c.Exits())
            {
              Contract.Assert(cexit != null);
              if (cexit.Label == exit.Label)
              {
                newcopies.Add(cexit);
              }
            }
          }

          if (newcopies.Count == 0)
          {
            throw new System.Exception("missing exit " + exit.Label);
          }

          SoundnessCheck(cache, exit, newcopies);
        }
      }
    }
}