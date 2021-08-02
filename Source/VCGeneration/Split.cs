using System;
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
        public bool bigBlock;
        public int id;
        public double assertionCost;
        public double assumptionCost; // before multiplier
        public double incomingPaths;

        public List<Block> /*!>!*/
          virtualSuccessors = new List<Block>();

        public List<Block> /*!>!*/
          virtualPredecessors = new List<Block>();

        public HashSet<Block> reachableBlocks;
        public readonly Block block;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
          Contract.Invariant(cce.NonNullElements(virtualSuccessors));
          Contract.Invariant(cce.NonNullElements(virtualPredecessors));
          Contract.Invariant(block != null);
        }


        public BlockStats(Block b, int i)
        {
          Contract.Requires(b != null);
          block = b;
          assertionCost = -1;
          id = i;
        }
      }

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(cce.NonNullElements(blocks));
        Contract.Invariant(cce.NonNullElements(bigBlocks));
        Contract.Invariant(cce.NonNullDictionaryAndValues(stats));
        Contract.Invariant(cce.NonNullElements(assumizedBranches));
        Contract.Invariant(gotoCmdOrigins != null);
        Contract.Invariant(parent != null);
        Contract.Invariant(impl != null);
        Contract.Invariant(copies != null);
        Contract.Invariant(cce.NonNull(protectedFromAssertToAssume));
        Contract.Invariant(cce.NonNull(keepAtAll));
      }


      readonly List<Block> blocks;
      readonly List<Block> bigBlocks = new List<Block>();

      readonly Dictionary<Block /*!*/, BlockStats /*!*/> /*!*/
        stats = new Dictionary<Block /*!*/, BlockStats /*!*/>();

      static int currentId = -1;
      Block splitBlock;
      bool assertToAssume;

      List<Block /*!*/> /*!*/
        assumizedBranches = new List<Block /*!*/>();

      double score;
      bool scoreComputed;
      double totalCost;
      int assertionCount;
      double assertionCost; // without multiplication by paths

      Dictionary<TransferCmd, ReturnCmd> /*!*/
        gotoCmdOrigins;

      readonly public VCGen /*!*/
        parent;

      Implementation /*!*/
        impl;

      Dictionary<Block /*!*/, Block /*!*/> /*!*/
        copies = new Dictionary<Block /*!*/, Block /*!*/>();

      bool doingSlice;
      double sliceInitialLimit;
      double sliceLimit;
      bool slicePos;

      HashSet<Block /*!*/> /*!*/
        protectedFromAssertToAssume = new HashSet<Block /*!*/>();

      HashSet<Block /*!*/> /*!*/
        keepAtAll = new HashSet<Block /*!*/>();

      // async interface
      private Checker checker;
      private int splitNum;
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
        Interlocked.Increment(ref currentId);
      }

      public double Cost
      {
        get
        {
          ComputeBestSplit();
          return totalCost;
        }
      }

      public bool LastChance
      {
        get
        {
          ComputeBestSplit();
          return assertionCount == 1 && score < 0;
        }
      }

      public string Stats
      {
        get
        {
          ComputeBestSplit();
          return string.Format("(cost:{0:0}/{1:0}{2})", totalCost, assertionCost, LastChance ? " last" : "");
        }
      }

      public void DumpDot(int splitNum)
      {
        using (System.IO.StreamWriter sw = System.IO.File.CreateText(string.Format("{0}.split.{1}.dot", impl.Name, splitNum)))
        {
          sw.WriteLine("digraph G {");

          ComputeBestSplit();
          List<Block> saved = assumizedBranches;
          Contract.Assert(saved != null);
          assumizedBranches = new List<Block>();
          DoComputeScore(false);
          assumizedBranches = saved;

          foreach (Block b in bigBlocks)
          {
            Contract.Assert(b != null);
            BlockStats s = GetBlockStats(b);
            foreach (Block t in s.virtualSuccessors)
            {
              Contract.Assert(t != null);
              sw.WriteLine("n{0} -> n{1};", s.id, GetBlockStats(t).id);
            }

            sw.WriteLine("n{0} [label=\"{1}:\\n({2:0.0}+{3:0.0})*{4:0.0}\"{5}];",
              s.id, b.Label,
              s.assertionCost, s.assumptionCost, s.incomingPaths,
              s.assertionCost > 0 ? ",shape=box" : "");
          }

          sw.WriteLine("}");
          sw.Close();
        }

        string filename = string.Format("{0}.split.{1}.bpl", impl.Name, splitNum);
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
        if (s.assertionCost >= 0)
          return; // already done
        s.bigBlock = true;
        s.assertionCost = 0;
        s.assumptionCost = 0;
        foreach (Cmd c in b.Cmds)
        {
          if (c is AssertCmd)
          {
            double cost = AssertionCost((AssertCmd) c);
            s.assertionCost += cost;
            assertionCount++;
            assertionCost += cost;
          }
          else if (c is AssumeCmd)
          {
            s.assumptionCost += AssertionCost((AssumeCmd) c);
          }
        }

        foreach (Block c in b.Exits())
        {
          Contract.Assert(c != null);
          s.virtualSuccessors.Add(c);
        }

        if (s.virtualSuccessors.Count == 1)
        {
          Block next = s.virtualSuccessors[0];
          BlockStats se = GetBlockStats(next);
          CountAssertions(next);
          if (next.Predecessors.Count > 1 || se.virtualSuccessors.Count != 1)
            return;
          s.virtualSuccessors[0] = se.virtualSuccessors[0];
          s.assertionCost += se.assertionCost;
          s.assumptionCost += se.assumptionCost;
          se.bigBlock = false;
        }
      }

      HashSet<Block /*!*/> /*!*/ ComputeReachableNodes(Block /*!*/ b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(cce.NonNull(Contract.Result<HashSet<Block /*!*/>>()));
        BlockStats s = GetBlockStats(b);
        if (s.reachableBlocks != null)
        {
          return s.reachableBlocks;
        }

        HashSet<Block /*!*/> blocks = new HashSet<Block /*!*/>();
        s.reachableBlocks = blocks;
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

      double ProverCost(double vcCost)
      {
        return vcCost * vcCost;
      }

      void ComputeBestSplit()
      {
        if (scoreComputed)
          return;
        scoreComputed = true;

        assertionCount = 0;

        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          CountAssertions(b);
        }

        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          BlockStats bs = GetBlockStats(b);
          if (bs.bigBlock)
          {
            bigBlocks.Add(b);
            foreach (Block ch in bs.virtualSuccessors)
            {
              Contract.Assert(ch != null);
              BlockStats chs = GetBlockStats(ch);
              if (!chs.bigBlock)
              {
                Console.WriteLine("non-big {0} accessed from {1}", ch, b);
                DumpDot(-1);
                Contract.Assert(false);
                throw new cce.UnreachableException();
              }

              chs.virtualPredecessors.Add(b);
            }
          }
        }

        assumizedBranches.Clear();
        totalCost = ProverCost(DoComputeScore(false));

        score = double.PositiveInfinity;
        Block bestSplit = null;
        List<Block> savedBranches = new List<Block>();

        foreach (Block b in bigBlocks)
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
          splitBlock = b;

          assumizedBranches.Clear();
          assumizedBranches.Add(cce.NonNull(targ[0]));
          left0 = DoComputeScore(true);
          right0 = DoComputeScore(false);

          assumizedBranches.Clear();
          for (int idx = 1; idx < targ.Count; idx++)
          {
            assumizedBranches.Add(cce.NonNull(targ[idx]));
          }

          left1 = DoComputeScore(true);
          right1 = DoComputeScore(false);

          double currentScore = ProverCost(left1) + ProverCost(right1);
          double otherScore = ProverCost(left0) + ProverCost(right0);

          if (otherScore < currentScore)
          {
            currentScore = otherScore;
            assumizedBranches.Clear();
            assumizedBranches.Add(cce.NonNull(targ[0]));
          }

          if (currentScore < score)
          {
            score = currentScore;
            bestSplit = splitBlock;
            savedBranches.Clear();
            savedBranches.AddRange(assumizedBranches);
          }
        }

        if (CommandLineOptions.Clo.VcsPathSplitMult * score > totalCost)
        {
          splitBlock = null;
          score = -1;
        }
        else
        {
          assumizedBranches = savedBranches;
          splitBlock = bestSplit;
        }
      }

      void UpdateIncommingPaths(BlockStats s)
      {
        Contract.Requires(s != null);
        if (s.incomingPaths < 0.0)
        {
          int count = 0;
          s.incomingPaths = 0.0;
          if (!keepAtAll.Contains(s.block))
            return;
          foreach (Block b in s.virtualPredecessors)
          {
            Contract.Assert(b != null);
            BlockStats ch = GetBlockStats(b);
            Contract.Assert(ch != null);
            UpdateIncommingPaths(ch);
            if (ch.incomingPaths > 0.0)
            {
              s.incomingPaths += ch.incomingPaths;
              count++;
            }
          }

          if (count > 1)
          {
            s.incomingPaths *= CommandLineOptions.Clo.VcsPathJoinMult;
          }
        }
      }

      void ComputeBlockSetsHelper(Block b, bool allowSmall)
      {
        Contract.Requires(b != null);
        if (keepAtAll.Contains(b))
          return;
        keepAtAll.Add(b);

        if (allowSmall)
        {
          foreach (Block ch in b.Exits())
          {
            Contract.Assert(ch != null);
            if (b == splitBlock && assumizedBranches.Contains(ch))
              continue;
            ComputeBlockSetsHelper(ch, allowSmall);
          }
        }
        else
        {
          foreach (Block ch in GetBlockStats(b).virtualSuccessors)
          {
            Contract.Assert(ch != null);
            if (b == splitBlock && assumizedBranches.Contains(ch))
              continue;
            ComputeBlockSetsHelper(ch, allowSmall);
          }
        }
      }

      void ComputeBlockSets(bool allowSmall)
      {
        protectedFromAssertToAssume.Clear();
        keepAtAll.Clear();

        Debug.Assert(splitBlock == null || GetBlockStats(splitBlock).bigBlock);
        Debug.Assert(GetBlockStats(blocks[0]).bigBlock);

        if (assertToAssume)
        {
          foreach (Block b in allowSmall ? blocks : bigBlocks)
          {
            Contract.Assert(b != null);
            if (ComputeReachableNodes(b).Contains(cce.NonNull(splitBlock)))
            {
              keepAtAll.Add(b);
            }
          }

          foreach (Block b in assumizedBranches)
          {
            Contract.Assert(b != null);
            foreach (Block r in ComputeReachableNodes(b))
            {
              Contract.Assert(r != null);
              if (allowSmall || GetBlockStats(r).bigBlock)
              {
                keepAtAll.Add(r);
                protectedFromAssertToAssume.Add(r);
              }
            }
          }
        }
        else
        {
          ComputeBlockSetsHelper(blocks[0], allowSmall);
        }
      }

      bool ShouldAssumize(Block b)
      {
        Contract.Requires(b != null);
        return assertToAssume && !protectedFromAssertToAssume.Contains(b);
      }

      double DoComputeScore(bool aa)
      {
        assertToAssume = aa;
        ComputeBlockSets(false);

        foreach (Block b in bigBlocks)
        {
          Contract.Assert(b != null);
          GetBlockStats(b).incomingPaths = -1.0;
        }

        GetBlockStats(blocks[0]).incomingPaths = 1.0;

        double cost = 0.0;
        foreach (Block b in bigBlocks)
        {
          Contract.Assert(b != null);
          if (keepAtAll.Contains(b))
          {
            BlockStats s = GetBlockStats(b);
            UpdateIncommingPaths(s);
            double local = s.assertionCost;
            if (ShouldAssumize(b))
            {
              local = (s.assertionCost + s.assumptionCost) * CommandLineOptions.Clo.VcsAssumeMult;
            }
            else
            {
              local = s.assumptionCost * CommandLineOptions.Clo.VcsAssumeMult + s.assertionCost;
            }

            local = local + local * s.incomingPaths * CommandLineOptions.Clo.VcsPathCostMult;
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
        if (!doingSlice && !ShouldAssumize(b))
          return seq;
        List<Cmd> res = new List<Cmd>();
        foreach (Cmd c in seq)
        {
          Contract.Assert(c != null);
          AssertCmd a = c as AssertCmd;
          Cmd theNewCmd = c;
          bool swap = false;
          if (a != null)
          {
            if (doingSlice)
            {
              double cost = AssertionCost(a);
              bool first = (sliceLimit - cost) >= 0 || sliceInitialLimit == sliceLimit;
              sliceLimit -= cost;
              swap = slicePos == first;
            }
            else if (assertToAssume)
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
              theNewCmd = VCGen.AssertTurnedIntoAssume(a);
            }
          }

          res.Add(theNewCmd);
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
            Contract.Assert(doingSlice ||
                            (assertToAssume || (keepAtAll.Contains(ch) || assumizedBranches.Contains(ch))));
            if (doingSlice ||
                ((b != splitBlock || assumizedBranches.Contains(ch) == assertToAssume) &&
                 keepAtAll.Contains(ch)))
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

        assertToAssume = idx == 0;
        doingSlice = false;
        ComputeBlockSets(true);

        return DoSplit();
      }

      Split SliceAsserts(double limit, bool pos)
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        slicePos = pos;
        sliceLimit = limit;
        sliceInitialLimit = limit;
        doingSlice = true;
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

      private static void PrintSet<T> (HashSet<T> s) {
        foreach(T i in s)
          Console.WriteLine(i);
      }

      // Verify b with the last split in blockAssignments[b]
      private static Dictionary<Block, Block> PickBlocksToVerify (List<Block> blocks, Dictionary<Block, int> splitPoints)
      {
        var todo = new Stack<Block>();
        var blockAssignments = new Dictionary<Block, Block>();
        var immediateDominator = (Program.GraphFromBlocks(blocks)).ImmediateDominator();
        todo.Push(blocks[0]);
        while(todo.Count > 0)
        {
          var currentBlock = todo.Pop();
          if (blockAssignments.Keys.Contains(currentBlock))
            continue;
          else if (immediateDominator[currentBlock] == currentBlock) // if the currentBlock doesn't have a predecessor.
            blockAssignments[currentBlock] = currentBlock;
          else if (splitPoints.Keys.Contains(immediateDominator[currentBlock])) // if the currentBlock's dominator has a split then it will be associated with that split
            blockAssignments[currentBlock] = immediateDominator[currentBlock];
          else
          {
            Contract.Assert(blockAssignments.Keys.Contains(immediateDominator[currentBlock]));
            blockAssignments[currentBlock] = blockAssignments[immediateDominator[currentBlock]];
          }
          if (currentBlock.TransferCmd is GotoCmd exit)
            exit.labelTargets.ForEach(blk => todo.Push(blk));
        }
        return blockAssignments;
      }
      private static List<Block> DoPreAssignedManualSplit(List<Block> blocks, Dictionary<Block, Block> blockAssignments, int splitNumberWithinBlock,
        Block containingBlock, bool lastSplitInBlock)
      {

        bool isSplitCmd(Cmd c)
        {
          return c is PredicateCmd p && QKeyValue.FindBoolAttribute(p.Attributes, "split_here");
        }

        var newBlocks = new List<Block>(blocks.Count()); // Copies of the original blocks
        var duplicator = new Duplicator();
        var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count()); // Maps original blocks to their new copies in newBlocks
        foreach (var currentBlock in blocks)
        {
          var newBlock = (Block)duplicator.VisitBlock(currentBlock);
          oldToNewBlockMap[currentBlock] = newBlock;
          newBlocks.Add(newBlock);
          if (currentBlock == containingBlock)
          {
            var newCmds = new List<Cmd>();
            var splitCount = -1;
            var verify = splitCount == splitNumberWithinBlock;
            foreach (Cmd c in currentBlock.Cmds)
            {
              if (isSplitCmd(c))
              {
                splitCount++;
                verify = splitCount == splitNumberWithinBlock;
              }
              newCmds.Add(verify ? c : Split.AssertIntoAssume(c));
            }
            newBlock.Cmds = newCmds;
          }
          else if (lastSplitInBlock && blockAssignments[currentBlock] == containingBlock)
          {
            var verify = true;
            var newCmds = new List<Cmd>();
            foreach(Cmd c in currentBlock.Cmds) {
              verify = isSplitCmd(c) ? false : verify;
              newCmds.Add(verify ? c : Split.AssertIntoAssume(c));
            }
            newBlock.Cmds = newCmds;
          }
          else
          {
            newBlock.Cmds = currentBlock.Cmds.Select<Cmd, Cmd>(c => Split.AssertIntoAssume(c)).ToList();
          }
        }
        // Patch the edges between the new blocks
        foreach (var oldBlock in blocks)
        {
          if (oldBlock.TransferCmd is ReturnCmd)
            continue;

          var gotoCmd = (GotoCmd)oldBlock.TransferCmd;
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


      /// <summary>
      /// Starting from the 0-index "split_here" annotation in begin, verifies until it reaches a subsequent "split_here" annotation
      /// Returns a list of blocks where all code not verified has asserts converted into assumes
      /// </summary>
      /// <param name="blocks">Implementation's collection of blocks</param>
      /// <param name="begin">Block containing the first split_here from which to start verifying</param>
      /// <param name="beginSplitId">0-based ID of the "split_here" annotation within begin at which to start verifying</param>
      /// <param name="blockInternalSplit">True if the entire split is contained within block begin</param>
      /// <param name="endPoints">Set of all blocks containing a "split_here" annotation</param>
      /// <returns></returns>
      // Note: Current implementation may over report errors.
      //       For example, if the control flow graph is a diamond (e.g., A -> B, C, B->D, C->D),
      //       and there is a split in B and an error in D, then D will be verified twice and hence report the error twice.
      //       Best solution may be to memoize blocks that have been fully verified and be sure not to verify them again
      private static List<Block> DoManualSplit(List<Block> blocks, Block begin, int beginSplitId,
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
             beginSplitId == -1
            ) // -1 tells us to start verifying from the very beginning (i.e., there is no split in the begin block)
            || (
              reachableEndPoints
                .Contains(currentBlock) // This endpoint is reachable from begin, so we verify until we hit the first split point
              && !blockInternalSplit); // Don't bother verifying if all of the splitting is within the begin block
          var newCmds = new List<Cmd>();
          var splitHereCount = 0;

          foreach (Cmd c in currentBlock.Cmds)
          {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "split_here"))
            {
              if (currentBlock == begin)
              {
                // Verify everything between the beginSplitId we were given and the next split
                if (splitHereCount == beginSplitId)
                {
                  verify = true;
                }
                else if (splitHereCount == beginSplitId + 1)
                {
                  verify = false;
                }
              }
              else
              {
                // We're in an endpoint so we stop verifying as soon as we hit a "split_here"
                verify = false;
              }

              splitHereCount++;
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

      private static List<Block> PostProcess(List<Block> blocks)
      {
        void DeleteFalseGotos (Block b)
        {
          bool isAssumeFalse (Cmd c) { return c is AssumeCmd ac && ac.Expr is LiteralExpr le && !le.asBool; }
          var firstFalseIdx = b.Cmds.FindIndex(c => isAssumeFalse(c));
          if (firstFalseIdx != -1)
          {
            b.Cmds = b.Cmds.Take(firstFalseIdx + 1).ToList();
            b.TransferCmd = (b.TransferCmd is GotoCmd) ? new ReturnCmd(b.tok) : b.TransferCmd;
          }
        }

        bool ContainsAssert(Block b)
        {
          bool isNonTrivialAssert (Cmd c) { return c is AssertCmd ac && !(ac.Expr is LiteralExpr le && le.asBool); }
          return b.Cmds.Exists(cmd => isNonTrivialAssert(cmd));
        }

        blocks.ForEach(b => DeleteFalseGotos(b)); // make blocks ending in assume false leaves of the CFG-DAG -- this is probably unnecessary, may have been done previously
        var todo = new Stack<Block>();
        var peeked = new HashSet<Block>();
        var interestingBlocks = new HashSet<Block>();
        todo.Push(blocks[0]);
        while(todo.Count() > 0)
        {
          var currentBlock = todo.Peek();
          var pop = peeked.Contains(currentBlock);
          peeked.Add(currentBlock);
          var interesting = false;
          var exit = currentBlock.TransferCmd as GotoCmd;
          if (exit != null && !pop) {
            exit.labelTargets.ForEach(b => todo.Push(b));
          } else if (exit != null) {
            Contract.Assert(pop);
            var gtc = new GotoCmd(exit.tok, exit.labelTargets.Where(l => interestingBlocks.Contains(l)).ToList());
            currentBlock.TransferCmd = gtc;
            interesting = interesting || gtc.labelTargets.Count() != 0;
          }
          if (pop)
          {
            interesting = interesting || ContainsAssert(currentBlock);
            if (interesting) {
              interestingBlocks.Add(currentBlock);
            }
            todo.Pop();
          }
        }
        interestingBlocks.Add(blocks[0]); // must not be empty
        return blocks.Where(b => interestingBlocks.Contains(b)).ToList(); // this is not the same as interestingBlocks.ToList() because the resulting lists will have different orders.
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
        var blockAssignments = PickBlocksToVerify(impl.Blocks, splitPoints);
        var entryBlockHasSplit = splitPoints.Keys.Contains(entryPoint);
        var baseSplitBlocks = PostProcess(DoPreAssignedManualSplit(impl.Blocks, blockAssignments, -1, entryPoint, !entryBlockHasSplit));
        splits.Add(new Split(baseSplitBlocks, gotoCmdOrigins, par, impl));
        foreach (KeyValuePair<Block, int> pair in splitPoints)
        {
          for (int i = 0; i < pair.Value; i++)
          {
            bool lastSplitInBlock = i == pair.Value - 1;
            var newBlocks = DoPreAssignedManualSplit(impl.Blocks, blockAssignments, i, pair.Key, lastSplitInBlock);
            var processedBlocks = PostProcess(newBlocks);
            Split s = new Split(processedBlocks, gotoCmdOrigins, par, impl); // REVIEW: Does gotoCmdOrigins need to be changed at all?
            splits.Add(s);
          }
        }
        return splits;
      }

      public static List<Split> FocusImpl(Implementation impl, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VCGen par)
      {
        bool isFocusCmd(Cmd c) {
          return c is PredicateCmd p && QKeyValue.FindBoolAttribute(p.Attributes, "focus");
        }
        List<Block> getFocusBlocks(List<Block> blocks) {
          return blocks.Where(blk => blk.Cmds.Where(c => isFocusCmd(c)).Count() != 0).ToList();
        }
        var dag = VCGen.BlocksToDag(impl.Blocks);
        var topoSorted = dag.TopologicalSort().ToList();
        // If reallyFocus is set to true,
        // foci are processed in a top-down fashion --- i.e., if two foci are on the same path,
        // the ancestor is processed first.
        // On the other hand, if reallyFocus is false,
        // foci are processed in a bottom-up fashion --- i.e., the descendant is processed first.
        bool reallyFocus = false;
        int compareBlocks(Block b1, Block b2) {
          if (topoSorted.IndexOf(b1) == topoSorted.IndexOf(b2)) {
            return 0;
          } else {
            return (topoSorted.IndexOf(b1) < topoSorted.IndexOf(b2)) ^ reallyFocus ? 1 : -1;
          }
        }
        List<Block> focusBlocks = getFocusBlocks(impl.Blocks);
        if(focusBlocks.Count() == 0) {
          return null;
        }

        focusBlocks.Sort(compareBlocks); // if reallyFocus is true, blocks are sorted according to the topological order; otherwise they are placed in reverse topo order.
        var s = new List<Split>();
        var duplicator = new Duplicator();
        HashSet<Block> getReachableBlocks(Block root, bool direction) {
          var todo = new Stack<Block>();
          var visited = new HashSet<Block> ();
          todo.Push(root);
          while(todo.Count() != 0) {
            var b = todo.Pop();
            if (visited.Contains(b)) continue;
            var related = direction ? dag.Successors(b) : dag.Predecessors(b);
            related.Where(b => !visited.Contains(b)).ToList().ForEach(b => todo.Push(b));
            visited.Add(b);
          }
          return visited;
        }

        // finds all the blocks dominated by focusBlock in the subgraph
        // which only contains vertices of subGraph.
        HashSet<Block> DominatedBlocks(Block focusBlock, IEnumerable<Block> subGraph) {
          var topoSorted = dag.TopologicalSort();
          var dominators = new Dictionary<Block, HashSet<Block>>();
          var todo = new Queue<Block>();
          foreach (var b in topoSorted.Where(blk => subGraph.Contains(blk)))
          {
            var s = new HashSet<Block>();
            var pred = b.Predecessors.Where(blk => subGraph.Contains(blk)).ToList();
            if (pred.Count() != 0)
            {
              s.UnionWith(dominators[pred[0]]);
              pred.ForEach(blk => s.IntersectWith(dominators[blk]));
            }
            s.Add(b);
            dominators[b] = s;
          }
          return subGraph.Where(blk => dominators[blk].Contains(focusBlock)).ToHashSet();
        }


        Cmd ForgetSplits(Cmd c)
        {
          if (c is PredicateCmd pc) {
            for (var kv = pc.Attributes; kv != null; kv = kv.Next)
            {
              if (kv.Key == "split") {
                kv.AddParam(new LiteralExpr(Token.NoToken, false));
              }
            }
          }
          return c;
        }

        void focusRec(int focusIdx, IEnumerable<Block> blocks, IEnumerable<Block> freeBlocks)
        {
          if (focusIdx == focusBlocks.Count()) {
            // freeBlocks consist of the predecessors of the relevant foci.
            // Their assertions turn into assumes and any splits inside them are erased.
            var l = blocks.ToList();
            l.Sort(compareBlocks);
            // assert that the root block, impl.Blocks[0], is in l
            Contract.Assert((reallyFocus && l.ElementAt(0) == impl.Blocks[0])
                            || (!reallyFocus && l.ElementAt(l.Count() - 1) == impl.Blocks[0]));
            if (reallyFocus) {
              l.Reverse();
            }
            var newBlocks = new List<Block>();
            var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count());
            // it is important for this loop to be bottom-up
            foreach (Block b in l)
            {
              var newBlock = (Block)duplicator.Visit(b);
              newBlocks.Add(newBlock);
              oldToNewBlockMap[b] = newBlock;
              if(freeBlocks.Contains(b)) {
                newBlock.Cmds = b.Cmds.Select(c => Split.AssertIntoAssume(c)).Select(c => ForgetSplits(c)).ToList();
              }
              if (b.TransferCmd is GotoCmd gtc) {
                var targets = gtc.labelTargets.Where(blk => blocks.Contains(blk));
                newBlock.TransferCmd = new GotoCmd(gtc.tok,
                                              targets.Select(blk => oldToNewBlockMap[blk].Label).ToList(),
                                              targets.Select(blk => oldToNewBlockMap[blk]).ToList());
              }
            }
            newBlocks.Reverse();
            Contract.Assert(newBlocks[0] == oldToNewBlockMap[impl.Blocks[0]]);
            s.Add(new Split(PostProcess(newBlocks), gotoCmdOrigins, par, impl));
          } else if (!blocks.Contains(focusBlocks[focusIdx])) {
            focusRec(focusIdx + 1, blocks, freeBlocks);
          } else {
            var b = focusBlocks[focusIdx];
            var dominatedBlocks = DominatedBlocks(b, blocks);
            // the first part takes all blocks except the ones dominated by the focus block
            focusRec(focusIdx + 1, blocks.Where(blk => !dominatedBlocks.Contains(blk)), freeBlocks);
            // the other part takes all predecessors, the focus block, and the successors.
            var ancestors = getReachableBlocks(b, false);
            ancestors.Remove(b);
            var descendants = getReachableBlocks(b, true);
            focusRec(focusIdx + 1, ancestors.Union(descendants).Intersect(blocks), ancestors.Union(freeBlocks));
          }
        }

        focusRec(0, impl.Blocks, new List<Block>());
        return s;
      }

      public static List<Split> FocusAndSplit(Implementation impl, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VCGen par)
      {
        List<Split> focussedImpl = FocusImpl(impl, gotoCmdOrigins, par);
        if (focussedImpl == null) {
          return FindManualSplits(impl, gotoCmdOrigins, par);
        } else {
          List<Split> splits = new List<Split>();
          foreach (var f in focussedImpl)
          {
            var new_splits = FindManualSplits(f.impl, f.gotoCmdOrigins, par);
            if (new_splits == null) {
              splits.Add(f);
            } else {
              splits.AddRange(new_splits);
            }
          }
          return splits;
        }
      }

      public static List<Split /*!*/> /*!*/ DoSplit(Split initial, double maxCost, int max)
      {
        Contract.Requires(initial != null);
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Split>>()));

        List<Split> res = new List<Split>();
        res.Add(initial);

        while (res.Count < max)
        {
          Split best = null;
          int bestIdx = 0, pos = 0;
          foreach (Split s in res)
          {
            Contract.Assert(s != null);
            s.ComputeBestSplit(); // TODO check totalCost first
            if (s.totalCost > maxCost &&
                (best == null || best.totalCost < s.totalCost) &&
                (s.assertionCount > 1 || s.splitBlock != null))
            {
              best = s;
              bestIdx = pos;
            }

            pos++;
          }

          if (best == null)
            break; // no split found

          Split s0, s1;

          bool splitStats = CommandLineOptions.Clo.TraceVerify;

          if (splitStats)
          {
            Console.WriteLine("{0} {1} -->", best.splitBlock == null ? "SLICE" : ("SPLIT@" + best.splitBlock.Label),
              best.Stats);
            if (best.splitBlock != null)
            {
              GotoCmd g = best.splitBlock.TransferCmd as GotoCmd;
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
                foreach (Block b in best.assumizedBranches)
                {
                  Contract.Assert(b != null);
                  Console.Write("{0} ", b.Label);
                }

                Console.WriteLine("");
              }
            }
          }

          if (best.splitBlock != null)
          {
            s0 = best.SplitAt(0);
            s1 = best.SplitAt(1);
          }
          else
          {
            best.splitBlock = null;
            s0 = best.SliceAsserts(best.assertionCost / 2, true);
            s1 = best.SliceAsserts(best.assertionCost / 2, false);
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

          if (splitStats)
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

          res[bestIdx] = s0;
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

      public void ReadOutcome(ref ConditionGeneration.Outcome curOutcome, out bool proverFailed)
      {
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        ProverInterface.Outcome outcome = cce.NonNull(checker).ReadOutcome();

        if (CommandLineOptions.Clo.Trace && splitNum >= 0)
        {
          System.Console.WriteLine("      --> split #{0} done,  [{1} s] {2}", splitNum,
            checker.ProverRunTime.TotalSeconds, outcome);
        }

        if (CommandLineOptions.Clo.VcsDumpSplits)
        {
          DumpDot(splitNum);
        }

        proverFailed = false;

        switch (outcome)
        {
          case ProverInterface.Outcome.Valid:
            return;
          case ProverInterface.Outcome.Invalid:
            curOutcome = ConditionGeneration.Outcome.Errors;
            return;
          case ProverInterface.Outcome.OutOfMemory:
            proverFailed = true;
            if (curOutcome != ConditionGeneration.Outcome.Errors && curOutcome != ConditionGeneration.Outcome.Inconclusive)
              curOutcome = ConditionGeneration.Outcome.OutOfMemory;
            return;
          case ProverInterface.Outcome.TimeOut:
            proverFailed = true;
            if (curOutcome != ConditionGeneration.Outcome.Errors && curOutcome != ConditionGeneration.Outcome.Inconclusive)
              curOutcome = ConditionGeneration.Outcome.TimedOut;
            return;
          case ProverInterface.Outcome.OutOfResource:
            proverFailed = true;
            if (curOutcome != ConditionGeneration.Outcome.Errors && curOutcome != ConditionGeneration.Outcome.Inconclusive)
              curOutcome = ConditionGeneration.Outcome.OutOfResource;
            return;
          case ProverInterface.Outcome.Undetermined:
            if (curOutcome != ConditionGeneration.Outcome.Errors)
              curOutcome = ConditionGeneration.Outcome.Inconclusive;
            return;
          default:
            Contract.Assert(false);
            throw new cce.UnreachableException();
        }
      }

      /// <summary>
      /// As a side effect, updates "this.parent.CumulativeAssertionCount".
      /// </summary>
      public void BeginCheck(Checker checker, VerifierCallback callback, ModelViewInfo mvInfo, int no, uint timeout, uint rlimit)
      {
        Contract.Requires(checker != null);
        Contract.Requires(callback != null);

        splitNum = no;

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

        vc = QuantifierInstantiationEngine.Instantiate(impl, exprGen, bet, vc);

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

      private static Cmd AssertIntoAssume(Cmd c)
      {
        if (c is AssertCmd assrt) return VCGen.AssertTurnedIntoAssume(assrt);
        return c;
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