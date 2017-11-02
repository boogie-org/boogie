//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using System.IO;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC {
  using Bpl = Microsoft.Boogie;
  using System.Threading.Tasks;

  public class VCGen : ConditionGeneration {
    /// <summary>
    /// Constructor.  Initializes the theorem prover.
    /// </summary>
    [NotDelayed]
    public VCGen(Program program, string/*?*/ logFilePath, bool appendLogFile, List<Checker> checkers)
      : base(program, checkers)
    {
      Contract.Requires(program != null);
      this.appendLogFile = appendLogFile;
      this.logFilePath = logFilePath;
    }

    private static AssumeCmd AssertTurnedIntoAssume(AssertCmd assrt) {
      Contract.Requires(assrt != null);
      Contract.Ensures(Contract.Result<AssumeCmd>() != null);

      Expr expr = assrt.Expr;
      Contract.Assert(expr != null);
      switch (Wlp.Subsumption(assrt)) {
        case CommandLineOptions.SubsumptionOption.Never:
          expr = Expr.True;
          break;
        case CommandLineOptions.SubsumptionOption.Always:
          break;
        case CommandLineOptions.SubsumptionOption.NotForQuantifiers:
          if (expr is QuantifierExpr) {
            expr = Expr.True;
          }
          break;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();  // unexpected case
      }

      return new AssumeCmd(assrt.tok, expr);
    }

    #region Soundness smoke tester
    class SmokeTester {
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(parent != null);
        Contract.Invariant(impl != null);
        Contract.Invariant(initial != null);
        Contract.Invariant(cce.NonNullDictionaryAndValues(copies));
        Contract.Invariant(cce.NonNull(visited));
        Contract.Invariant(callback != null);
      }

      VCGen parent;
      Implementation impl;
      Block initial;
      int id;
      Dictionary<Block, Block> copies = new Dictionary<Block, Block>();
      HashSet<Block> visited = new HashSet<Block>();
      VerifierCallback callback;

      internal SmokeTester(VCGen par, Implementation i, VerifierCallback callback) {
        Contract.Requires(par != null);
        Contract.Requires(i != null);
        Contract.Requires(callback != null);
        parent = par;
        impl = i;
        initial = i.Blocks[0];
        this.callback = callback;
      }

      internal void Copy() {
        CloneBlock(impl.Blocks[0]);
        initial = GetCopiedBlocks()[0];
      }

      internal void Test() {
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

        DFS(initial);
      }

      void TopologicalSortImpl() {
        Graph<Block> dag = new Graph<Block>();
        dag.AddSource(cce.NonNull(impl.Blocks[0])); // there is always at least one node in the graph
        foreach (Block b in impl.Blocks) {
          GotoCmd gtc = b.TransferCmd as GotoCmd;
          if (gtc != null) {
            Contract.Assume(gtc.labelTargets != null);
            foreach (Block dest in gtc.labelTargets) {
              Contract.Assert(dest != null);
              dag.AddEdge(b, dest);
            }
          }
        }
        impl.Blocks = new List<Block>();
        foreach (Block b in dag.TopologicalSort()) {
          Contract.Assert(b != null);
          impl.Blocks.Add(b);
        }
      }

      void Emit() {
        TopologicalSortImpl();
        EmitImpl(impl, false);
      }

      // this one copies forward
      Block CloneBlock(Block b) {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<Block>() != null);

        Block fake_res;
        if (copies.TryGetValue(b, out fake_res)) {
          return cce.NonNull(fake_res);
        }
        Block res = new Block(b.tok, b.Label, new List<Cmd>(b.Cmds), null);
        copies[b] = res;
        if (b.TransferCmd is GotoCmd) {
          foreach (Block ch in cce.NonNull((GotoCmd)b.TransferCmd).labelTargets) {
            Contract.Assert(ch != null);
            CloneBlock(ch);
          }
        }
        foreach (Block p in b.Predecessors) {
          Contract.Assert(p != null);
          res.Predecessors.Add(CloneBlock(p));
        }
        return res;
      }

      // this one copies backwards
      Block CopyBlock(Block b) {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<Block>() != null);

        Block fake_res;
        if (copies.TryGetValue(b, out fake_res)) {
          // fake_res should be Block! but the compiler fails
          return cce.NonNull(fake_res);
        }
        Block res;
        List<Cmd> seq = new List<Cmd>();
        foreach (Cmd c in b.Cmds) {
          Contract.Assert(c != null);
          AssertCmd turn = c as AssertCmd;
          if (!turnAssertIntoAssumes || turn == null) {
            seq.Add(c);
          } else {
            seq.Add(AssertTurnedIntoAssume(turn));
          }
        }
        res = new Block(b.tok, b.Label, seq, null);
        copies[b] = res;
        foreach (Block p in b.Predecessors) {
          Contract.Assert(p != null);
          res.Predecessors.Add(CopyBlock(p));
        }
        return res;
      }

      List<Block> GetCopiedBlocks() {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));

        // the order of nodes in res is random (except for the first one, being the entry)
        List<Block> res = new List<Block>();
        res.Add(copies[initial]);

        foreach (KeyValuePair<Block, Block> kv in copies) {
          Contract.Assert(kv.Key != null&&kv.Value!=null);
          GotoCmd go = kv.Key.TransferCmd as GotoCmd;
          ReturnCmd ret = kv.Key.TransferCmd as ReturnCmd;
          if (kv.Key != initial) {
            res.Add(kv.Value);
          }
          if (go != null) {
            GotoCmd copy = new GotoCmd(go.tok, new List<String>(), new List<Block>());
            kv.Value.TransferCmd = copy;
            foreach (Block b in cce.NonNull(go.labelTargets)) {
              Contract.Assert(b != null);
              Block c;
              if (copies.TryGetValue(b, out c)) {
                copy.AddTarget(cce.NonNull(c));
              }
            }
          } else if (ret != null) {
            kv.Value.TransferCmd = ret;
          } else {
            Contract.Assume(false);
            throw new cce.UnreachableException();
          }
        }

        copies.Clear();

        return res;
      }

      // check if e is true, false, !true, !false
      // if so return true and the value of the expression in val
      bool BooleanEval(Expr e, ref bool val) {
        Contract.Requires(e != null);
        LiteralExpr lit = e as LiteralExpr;
        NAryExpr call = e as NAryExpr;

        if (lit != null && lit.isBool) {
          val = lit.asBool;
          return true;
        } else if (call != null &&
                   call.Fun is UnaryOperator &&
                   ((UnaryOperator)call.Fun).Op == UnaryOperator.Opcode.Not &&
                   BooleanEval(cce.NonNull(call.Args[0]), ref val)) {
          val = !val;
          return true;
        }
          // this is for the 0bv32 != 0bv32 generated by vcc
        else if (call != null &&
                   call.Fun is BinaryOperator &&
                   ((BinaryOperator)call.Fun).Op == BinaryOperator.Opcode.Neq &&
                   call.Args[0] is LiteralExpr &&
                   cce.NonNull(call.Args[0]).Equals(call.Args[1])) {
          val = false;
          return true;
        }

        return false;
      }

      bool IsFalse(Expr e) {
        Contract.Requires(e != null);
        bool val = false;
        return BooleanEval(e, ref val) && !val;
      }

      bool CheckUnreachable(Block cur, List<Cmd> seq)
      {
        Contract.Requires(cur != null);
        Contract.Requires(seq != null);
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        foreach (Cmd cmd in seq)
        {
          AssertCmd assrt = cmd as AssertCmd;
          if (assrt != null && QKeyValue.FindBoolAttribute(assrt.Attributes, "PossiblyUnreachable"))
            return false;
        }

        DateTime start = DateTime.UtcNow;
        if (CommandLineOptions.Clo.Trace)
        {
          System.Console.Write("    soundness smoke test #{0} ... ", id);
        }
        callback.OnProgress("smoke", id, id, 0.0);

        Token tok = new Token();
        tok.val = "soundness smoke test assertion";
        seq.Add(new AssertCmd(tok, Expr.False));
        Block copy = CopyBlock(cur);
        Contract.Assert(copy != null);
        copy.Cmds = seq;
        List<Block> backup = impl.Blocks;
        Contract.Assert(backup != null);
        impl.Blocks = GetCopiedBlocks();
        copy.TransferCmd = new ReturnCmd(Token.NoToken);
        if (CommandLineOptions.Clo.TraceVerify)
        {
          System.Console.WriteLine();
          System.Console.WriteLine(" --- smoke #{0}, before passify", id);
          Emit();
        }
        parent.CurrentLocalVariables = impl.LocVars;
        ModelViewInfo mvInfo;
        parent.PassifyImpl(impl, out mvInfo);
        Dictionary<int, Absy> label2Absy;
        Checker ch = parent.FindCheckerFor(CommandLineOptions.Clo.SmokeTimeout, CommandLineOptions.Clo.Resourcelimit);
        Contract.Assert(ch != null);

        ProverInterface.Outcome outcome = ProverInterface.Outcome.Undetermined;
        try
        {
          lock (ch)
          {
            var exprGen = ch.TheoremProver.Context.ExprGen;
            VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : exprGen.Integer(BigNum.ZERO);

            VCExpr vc = parent.GenerateVC(impl, controlFlowVariableExpr, out label2Absy, ch.TheoremProver.Context);
            Contract.Assert(vc != null);

            if (!CommandLineOptions.Clo.UseLabels)
            {
              VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
              VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
              vc = exprGen.Implies(eqExpr, vc);
            }

            impl.Blocks = backup;

            if (CommandLineOptions.Clo.TraceVerify)
            {
              System.Console.WriteLine(" --- smoke #{0}, after passify", id);
              Emit();
            }

            ch.BeginCheck(cce.NonNull(impl.Name + "_smoke" + id++), vc, new ErrorHandler(label2Absy, this.callback));
          }

          ch.ProverTask.Wait();

          lock (ch)
          {
             outcome = ch.ReadOutcome();
          }
        }
        finally
        {
          ch.GoBackToIdle();
        }

        parent.CurrentLocalVariables = null;

        DateTime end = DateTime.UtcNow;
        TimeSpan elapsed = end - start;
        if (CommandLineOptions.Clo.Trace)
        {
          System.Console.WriteLine("  [{0} s] {1}", elapsed.TotalSeconds,
            outcome == ProverInterface.Outcome.Valid ? "OOPS" :
              "OK" + (outcome == ProverInterface.Outcome.Invalid ? "" : " (" + outcome + ")"));
        }

        if (outcome == ProverInterface.Outcome.Valid)
        {
          // copy it again, so we get the version with calls, assignments and such
          copy = CopyBlock(cur);
          copy.Cmds = seq;
          impl.Blocks = GetCopiedBlocks();
          TopologicalSortImpl();
          callback.OnUnreachableCode(impl);
          impl.Blocks = backup;
          return true;
        }
        return false;
      }

      const bool turnAssertIntoAssumes = false;

      void DFS(Block cur) {
        Contract.Requires(cur != null);
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        if (visited.Contains(cur))
          return;
        visited.Add(cur);

        List<Cmd> seq = new List<Cmd>();
        foreach (Cmd cmd_ in cur.Cmds) {
          Cmd cmd = cmd_;
          Contract.Assert(cmd != null);
          AssertCmd assrt = cmd as AssertCmd;
          AssumeCmd assm = cmd as AssumeCmd;
          CallCmd call = cmd as CallCmd;

          bool assumeFalse = false;

          if (assrt != null) {
            // we're not going any further
            // it's clear the user expected unreachable code here
            // it's not clear where did he expect it, maybe it would be right to insert
            // a check just one command before
            if (IsFalse(assrt.Expr))
              return;

#if TURN_ASSERT_INFO_ASSUMES
            if (turnAssertIntoAssumes) {
              cmd = AssertTurnedIntoAssume(assrt);
            }
#endif
          } else if (assm != null) {
            if (IsFalse(assm.Expr))
              assumeFalse = true;
          } else if (call != null) {
            foreach (Ensures e in (cce.NonNull(call.Proc)).Ensures) {
              Contract.Assert(e != null);
              if (IsFalse(e.Condition))
                assumeFalse = true;
            }
          }

          if (assumeFalse) {
            CheckUnreachable(cur, seq);
            return;
          }

          seq.Add(cmd);
        }


        GotoCmd go = cur.TransferCmd as GotoCmd;
        ReturnCmd ret = cur.TransferCmd as ReturnCmd;

        Contract.Assume(!(go != null && go.labelTargets == null && go.labelNames != null && go.labelNames.Count > 0));

        if (ret != null || (go != null && cce.NonNull(go.labelTargets).Count == 0)) {
          // we end in return, so there will be no more places to check
          CheckUnreachable(cur, seq);
        } else if (go != null) {
          bool needToCheck = true;
          // if all of our children have more than one parent, then
          // we're in the right place to check
          foreach (Block target in cce.NonNull(go.labelTargets)) {
            Contract.Assert(target != null);
            if (target.Predecessors.Count == 1) {
              needToCheck = false;
            }
          }
          if (needToCheck) {
            CheckUnreachable(cur, seq);
          }
          foreach (Block target in go.labelTargets) {
            Contract.Assert(target != null);
            DFS(target);
          }
        }
      }

      class ErrorHandler : ProverInterface.ErrorHandler {
        Dictionary<int, Absy> label2Absy;
        VerifierCallback callback;
        [ContractInvariantMethod]
        void ObjectInvariant() {
          Contract.Invariant(label2Absy != null);
          Contract.Invariant(callback != null);
        }


        public ErrorHandler(Dictionary<int, Absy> label2Absy, VerifierCallback callback) {
          Contract.Requires(label2Absy != null);
          Contract.Requires(callback != null);
          this.label2Absy = label2Absy;
          this.callback = callback;
        }

        public override Absy Label2Absy(string label) {
          //Contract.Requires(label != null);
          Contract.Ensures(Contract.Result<Absy>() != null);

          int id = int.Parse(label);
          return cce.NonNull((Absy)label2Absy[id]);
        }

        public override void OnProverWarning(string msg) {
          //Contract.Requires(msg != null);
          this.callback.OnWarning(msg);
        }
      }
    }


    #endregion

    #region Splitter
    class Split {
      class BlockStats {
        public bool big_block;
        public int id;
        public double assertion_cost;
        public double assumption_cost; // before multiplier
        public double incomming_paths;
        public List<Block>/*!>!*/ virtual_successors = new List<Block>();
        public List<Block>/*!>!*/ virtual_predecesors = new List<Block>();
        public HashSet<Block> reachable_blocks;
        public readonly Block block;
        [ContractInvariantMethod]
        void ObjectInvariant() {
          Contract.Invariant(cce.NonNullElements(virtual_successors));
          Contract.Invariant(cce.NonNullElements(virtual_predecesors));
          Contract.Invariant(block != null);
        }


        public BlockStats(Block b, int i) {
          Contract.Requires(b != null);
          block = b;
          assertion_cost = -1;
          id = i;
        }
      }
      [ContractInvariantMethod]
      void ObjectInvariant() {
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
      readonly Dictionary<Block/*!*/, BlockStats/*!*/>/*!*/ stats = new Dictionary<Block/*!*/, BlockStats/*!*/>();
      readonly int id;
      static int current_id = -1;
      Block split_block;
      bool assert_to_assume;
      List<Block/*!*/>/*!*/ assumized_branches = new List<Block/*!*/>();

      double score;
      bool score_computed;
      double total_cost;
      int assertion_count;
      double assertion_cost; // without multiplication by paths
      Dictionary<TransferCmd, ReturnCmd>/*!*/ gotoCmdOrigins;
      readonly public VCGen/*!*/ parent;
      Implementation/*!*/ impl;

      Dictionary<Block/*!*/, Block/*!*/>/*!*/ copies = new Dictionary<Block/*!*/, Block/*!*/>();
      bool doing_slice;
      double slice_initial_limit;
      double slice_limit;
      bool slice_pos;
      HashSet<Block/*!*/>/*!*/ protected_from_assert_to_assume = new HashSet<Block/*!*/>();
      HashSet<Block/*!*/>/*!*/ keep_at_all = new HashSet<Block/*!*/>();

      // async interface
      private Checker checker;
      private int splitNo;
      internal ErrorReporter reporter;

      public Split(List<Block/*!*/>/*!*/ blocks, Dictionary<TransferCmd, ReturnCmd>/*!*/ gotoCmdOrigins, VCGen/*!*/ par, Implementation/*!*/ impl) {
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

      public double Cost {
        get {
          ComputeBestSplit();
          return total_cost;
        }
      }

      public bool LastChance {
        get {
          ComputeBestSplit();
          return assertion_count == 1 && score < 0;
        }
      }

      public string Stats {
        get {
          ComputeBestSplit();
          return string.Format("(cost:{0:0}/{1:0}{2})", total_cost, assertion_cost, LastChance ? " last" : "");
        }
      }

      public void DumpDot(int no) {
        using (System.IO.StreamWriter sw = System.IO.File.CreateText(string.Format("split.{0}.dot", no))) {
          sw.WriteLine("digraph G {");

          ComputeBestSplit();
          List<Block> saved = assumized_branches;
          Contract.Assert(saved != null);
          assumized_branches = new List<Block>();
          DoComputeScore(false);
          assumized_branches = saved;

          foreach (Block b in big_blocks) {
            Contract.Assert(b != null);
            BlockStats s = GetBlockStats(b);
            foreach (Block t in s.virtual_successors) {
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
        using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename)) {
          int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
          CommandLineOptions.Clo.PrintUnstructured = 2;  // print only the unstructured program
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
      BlockStats GetBlockStats(Block b) {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<BlockStats>() != null);

        BlockStats s;
        if (!stats.TryGetValue(b, out s)) {
          s = new BlockStats(b, bsid++);
          stats[b] = s;
        }
        return cce.NonNull(s);
      }

      double AssertionCost(PredicateCmd c) {
        return 1.0;
      }

      void CountAssertions(Block b) {
        Contract.Requires(b != null);
        BlockStats s = GetBlockStats(b);
        if (s.assertion_cost >= 0)
          return; // already done
        s.big_block = true;
        s.assertion_cost = 0;
        s.assumption_cost = 0;
        foreach (Cmd c in b.Cmds) {
          if (c is AssertCmd) {
            double cost = AssertionCost((AssertCmd)c);
            s.assertion_cost += cost;
            assertion_count++;
            assertion_cost += cost;
          } else if (c is AssumeCmd) {
            s.assumption_cost += AssertionCost((AssumeCmd)c);
          }
        }
        foreach (Block c in Exits(b)) {
          Contract.Assert(c != null);
          s.virtual_successors.Add(c);
        }
        if (s.virtual_successors.Count == 1) {
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

      HashSet<Block/*!*/>/*!*/ ComputeReachableNodes(Block/*!*/ b) {
        Contract.Requires(b != null);
        Contract.Ensures(cce.NonNull(Contract.Result<HashSet<Block/*!*/>>()));
        BlockStats s = GetBlockStats(b);
        if (s.reachable_blocks != null) {
          return s.reachable_blocks;
        }
        HashSet<Block/*!*/> blocks = new HashSet<Block/*!*/>();
        s.reachable_blocks = blocks;
        blocks.Add(b);
        foreach (Block/*!*/ succ in Exits(b)) {
          Contract.Assert(succ != null);
          foreach (Block r in ComputeReachableNodes(succ)) {
            Contract.Assert(r != null);
            blocks.Add(r);
          }
        }
        return blocks;
      }

      double ProverCost(double vc_cost) {
        return vc_cost * vc_cost;
      }

      void ComputeBestSplit() {
        if (score_computed)
          return;
        score_computed = true;

        assertion_count = 0;

        foreach (Block b in blocks) {
          Contract.Assert(b != null);
          CountAssertions(b);
        }

        foreach (Block b in blocks) {
          Contract.Assert(b != null);
          BlockStats bs = GetBlockStats(b);
          if (bs.big_block) {
            big_blocks.Add(b);
            foreach (Block ch in bs.virtual_successors) {
              Contract.Assert(ch != null);
              BlockStats chs = GetBlockStats(ch);
              if (!chs.big_block) {
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

        foreach (Block b in big_blocks) {
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
          for (int idx = 1; idx < targ.Count; idx++) {
            assumized_branches.Add(cce.NonNull(targ[idx]));
          }
          left1 = DoComputeScore(true);
          right1 = DoComputeScore(false);

          double current_score = ProverCost(left1) + ProverCost(right1);
          double other_score = ProverCost(left0) + ProverCost(right0);

          if (other_score < current_score) {
            current_score = other_score;
            assumized_branches.Clear();
            assumized_branches.Add(cce.NonNull(targ[0]));
          }

          if (current_score < score) {
            score = current_score;
            best_split = split_block;
            saved_branches.Clear();
            saved_branches.AddRange(assumized_branches);
          }
        }

        if (CommandLineOptions.Clo.VcsPathSplitMult * score > total_cost) {
          split_block = null;
          score = -1;
        } else {
          assumized_branches = saved_branches;
          split_block = best_split;
        }
      }

      void UpdateIncommingPaths(BlockStats s) {
        Contract.Requires(s != null);
        if (s.incomming_paths < 0.0) {
          int count = 0;
          s.incomming_paths = 0.0;
          if (!keep_at_all.Contains(s.block))
            return;
          foreach (Block b in s.virtual_predecesors) {
            Contract.Assert(b != null);
            BlockStats ch = GetBlockStats(b);
            Contract.Assert(ch != null);
            UpdateIncommingPaths(ch);
            if (ch.incomming_paths > 0.0) {
              s.incomming_paths += ch.incomming_paths;
              count++;
            }
          }
          if (count > 1) {
            s.incomming_paths *= CommandLineOptions.Clo.VcsPathJoinMult;
          }
        }
      }

      void ComputeBlockSetsHelper(Block b, bool allow_small) {
        Contract.Requires(b != null);
        if (keep_at_all.Contains(b))
          return;
        keep_at_all.Add(b);

        if (allow_small) {
          foreach (Block ch in Exits(b)) {
            Contract.Assert(ch != null);
            if (b == split_block && assumized_branches.Contains(ch))
              continue;
            ComputeBlockSetsHelper(ch, allow_small);
          }
        } else {
          foreach (Block ch in GetBlockStats(b).virtual_successors) {
            Contract.Assert(ch != null);
            if (b == split_block && assumized_branches.Contains(ch))
              continue;
            ComputeBlockSetsHelper(ch, allow_small);
          }
        }
      }

      void ComputeBlockSets(bool allow_small) {
        protected_from_assert_to_assume.Clear();
        keep_at_all.Clear();

        Debug.Assert(split_block == null || GetBlockStats(split_block).big_block);
        Debug.Assert(GetBlockStats(blocks[0]).big_block);

        if (assert_to_assume) {
          foreach (Block b in allow_small ? blocks : big_blocks) {
            Contract.Assert(b != null);
            if (ComputeReachableNodes(b).Contains(cce.NonNull(split_block))) {
              keep_at_all.Add(b);
            }
          }

          foreach (Block b in assumized_branches) {
            Contract.Assert(b != null);
            foreach (Block r in ComputeReachableNodes(b)) {
              Contract.Assert(r != null);
              if (allow_small || GetBlockStats(r).big_block) {
                keep_at_all.Add(r);
                protected_from_assert_to_assume.Add(r);
              }
            }
          }
        } else {
          ComputeBlockSetsHelper(blocks[0], allow_small);
        }
      }

      bool ShouldAssumize(Block b) {
        Contract.Requires(b != null);
        return assert_to_assume && !protected_from_assert_to_assume.Contains(b);
      }

      double DoComputeScore(bool aa) {
        assert_to_assume = aa;
        ComputeBlockSets(false);

        foreach (Block b in big_blocks) {
          Contract.Assert(b != null);
          GetBlockStats(b).incomming_paths = -1.0;
        }

        GetBlockStats(blocks[0]).incomming_paths = 1.0;

        double cost = 0.0;
        foreach (Block b in big_blocks) {
          Contract.Assert(b != null);
          if (keep_at_all.Contains(b)) {
            BlockStats s = GetBlockStats(b);
            UpdateIncommingPaths(s);
            double local = s.assertion_cost;
            if (ShouldAssumize(b)) {
              local = (s.assertion_cost + s.assumption_cost) * CommandLineOptions.Clo.VcsAssumeMult;
            } else {
              local = s.assumption_cost * CommandLineOptions.Clo.VcsAssumeMult + s.assertion_cost;
            }
            local = local + local * s.incomming_paths * CommandLineOptions.Clo.VcsPathCostMult;
            cost += local;
          }
        }

        return cost;
      }

      List<Cmd> SliceCmds(Block b) {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);

        List<Cmd> seq = b.Cmds;
        Contract.Assert(seq != null);
        if (!doing_slice && !ShouldAssumize(b))
          return seq;
        List<Cmd> res = new List<Cmd>();
        foreach (Cmd c in seq) {
          Contract.Assert(c != null);
          AssertCmd a = c as AssertCmd;
          Cmd the_new = c;
          bool swap = false;
          if (a != null) {
            if (doing_slice) {
              double cost = AssertionCost(a);
              bool first = (slice_limit - cost) >= 0 || slice_initial_limit == slice_limit;
              slice_limit -= cost;
              swap = slice_pos == first;
            } else if (assert_to_assume) {
              swap = true;
            } else {
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }

            if (swap) {
              the_new = AssertTurnedIntoAssume(a);
            }
          }
          res.Add(the_new);
        }
        return res;
      }

      Block CloneBlock(Block b) {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<Block>() != null);

        Block res;
        if (copies.TryGetValue(b, out res)) {
          return cce.NonNull(res);
        }
        res = new Block(b.tok, b.Label, SliceCmds(b), b.TransferCmd);
        GotoCmd gt = b.TransferCmd as GotoCmd;
        copies[b] = res;
        if (gt != null) {
          GotoCmd newGoto = new GotoCmd(gt.tok, new List<String>(), new List<Block>());
          res.TransferCmd = newGoto;
          int pos = 0;
          foreach (Block ch in cce.NonNull(gt.labelTargets)) {
            Contract.Assert(ch != null);
            Contract.Assert(doing_slice ||
                   (assert_to_assume || (keep_at_all.Contains(ch) || assumized_branches.Contains(ch))));
            if (doing_slice ||
                ((b != split_block || assumized_branches.Contains(ch) == assert_to_assume) &&
                 keep_at_all.Contains(ch))) {
              newGoto.AddTarget(CloneBlock(ch));
            }
            pos++;
          }
        }
        return res;
      }

      Split DoSplit() {
        Contract.Ensures(Contract.Result<Split>() != null);

        copies.Clear();
        CloneBlock(blocks[0]);
        List<Block> newBlocks = new List<Block>();
        Dictionary<TransferCmd, ReturnCmd> newGotoCmdOrigins = new Dictionary<TransferCmd, ReturnCmd>();
        foreach (Block b in blocks) {
          Contract.Assert(b != null);
          Block tmp;
          if (copies.TryGetValue(b, out tmp)) {
            newBlocks.Add(cce.NonNull(tmp));
            if (gotoCmdOrigins.ContainsKey(b.TransferCmd)) {
              newGotoCmdOrigins[tmp.TransferCmd] = gotoCmdOrigins[b.TransferCmd];
            }

            foreach (Block p in b.Predecessors) {
              Contract.Assert(p != null);
              Block tmp2;
              if (copies.TryGetValue(p, out tmp2)) {
                tmp.Predecessors.Add(tmp2);
              }
            }
          }
        }

        return new Split(newBlocks, newGotoCmdOrigins, parent, impl);
      }

      Split SplitAt(int idx) {
        Contract.Ensures(Contract.Result<Split>() != null);

        assert_to_assume = idx == 0;
        doing_slice = false;
        ComputeBlockSets(true);

        return DoSplit();
      }

      Split SliceAsserts(double limit, bool pos) {
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

      void Print() {
        List<Block> tmp = impl.Blocks;
        Contract.Assert(tmp != null);
        impl.Blocks = blocks;
        EmitImpl(impl, false);
        impl.Blocks = tmp;
      }

      public Counterexample ToCounterexample(ProverContext context) {
        Contract.Requires(context != null);
        Contract.Ensures(Contract.Result<Counterexample>() != null);

        List<Block> trace = new List<Block>();
        foreach (Block b in blocks) {
          Contract.Assert(b != null);
          trace.Add(b);
        }
        foreach (Block b in blocks) {
          Contract.Assert(b != null);
          foreach (Cmd c in b.Cmds) {
            Contract.Assert(c != null);
            if (c is AssertCmd) {
              return AssertCmdToCounterexample((AssertCmd)c, cce.NonNull(b.TransferCmd), trace, null, null, context);
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
      private static List<Block> DoManualSplit(List<Block> blocks, Block begin, int begin_split_id, bool blockInternalSplit, IEnumerable<Block> endPoints) {
        // Compute the set of blocks reachable from begin but not included in endPoints.  These will be verified in their entirety.
        var blocksToVerifyEntirely = new HashSet<Block>();
        var reachableEndPoints = new HashSet<Block>();  // Reachable end points will be verified up to their first split point
        var todo = new Stack<Block>();
        todo.Push(begin);
        while (todo.Count > 0) {
          var currentBlock = todo.Pop();
          if (blocksToVerifyEntirely.Contains(currentBlock)) continue;
          blocksToVerifyEntirely.Add(currentBlock);
          var exit = currentBlock.TransferCmd as GotoCmd;
          if (exit != null)
            foreach (Block targetBlock in exit.labelTargets) {
              if (!endPoints.Contains(targetBlock)) {
                todo.Push(targetBlock);
              } else {
                reachableEndPoints.Add(targetBlock);
              }
            }
              
        }
        blocksToVerifyEntirely.Remove(begin);

        // Convert assumes to asserts in "unreachable" blocks, including portions of blocks containing "split_here"
        var newBlocks = new List<Block>(blocks.Count());  // Copies of the original blocks
        var duplicator = new Duplicator();
        var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count());  // Maps original blocks to their new copies in newBlocks

        foreach (var currentBlock in blocks) {
          var newBlock = (Block)duplicator.VisitBlock(currentBlock);
          oldToNewBlockMap[currentBlock] = newBlock;          
          newBlocks.Add(newBlock);

          if (!blockInternalSplit && blocksToVerifyEntirely.Contains(currentBlock)) continue;  // All reachable blocks must be checked in their entirety, so don't change anything
          // Otherwise, we only verify a portion of the current block, so we'll need to look at each of its commands                 

          // !verify -> convert assert to assume
          var verify = (currentBlock == begin && begin_split_id == -1) // -1 tells us to start verifying from the very beginning (i.e., there is no split in the begin block)
                      || (reachableEndPoints.Contains(currentBlock)    // This endpoint is reachable from begin, so we verify until we hit the first split point
                          && !blockInternalSplit);                     // Don't bother verifying if all of the splitting is within the begin block
          var newCmds = new List<Cmd>();
          var split_here_count = 0;

          foreach (Cmd c in currentBlock.Cmds) {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "split_here")) {
              if (currentBlock == begin) { // Verify everything between the begin_split_id we were given and the next split
                if (split_here_count == begin_split_id) {
                  verify = true;
                } else if (split_here_count == begin_split_id + 1) {
                  verify = false;
                }
              } else {  // We're in an endPoint so we stop verifying as soon as we hit a "split_here"
                verify = false;
              }
              split_here_count++;              
            }
              
            var asrt = c as AssertCmd;
            if (verify || asrt == null)
              newCmds.Add(c);
            else
              newCmds.Add(AssertTurnedIntoAssume(asrt));
          }

          newBlock.Cmds = newCmds;
        }

        // Patch the edges between the new blocks
        foreach (var oldBlock in blocks) {
          if (oldBlock.TransferCmd is ReturnCmd) { continue; }
          var gotoCmd = (GotoCmd)oldBlock.TransferCmd;
          var newLabelTargets = new List<Block>(gotoCmd.labelTargets.Count());
          var newLabelNames = new List<string>(gotoCmd.labelTargets.Count());
          foreach (var target in gotoCmd.labelTargets) {
            newLabelTargets.Add(oldToNewBlockMap[target]);
            newLabelNames.Add(oldToNewBlockMap[target].Label);
          }
          oldToNewBlockMap[oldBlock].TransferCmd = new GotoCmd(gotoCmd.tok, newLabelNames, newLabelTargets);
        }

        return newBlocks;
      }

      public static List<Split/*!*/> FindManualSplits(Implementation/*!*/ impl, Dictionary<TransferCmd, ReturnCmd>/*!*/ gotoCmdOrigins, VCGen/*!*/ par) {
        Contract.Requires(impl != null);
        Contract.Ensures(Contract.Result<List<Split>>() == null || cce.NonNullElements(Contract.Result<List<Split>>()));

        var splitPoints = new Dictionary<Block,int>();
        foreach (var b in impl.Blocks) {
          foreach (Cmd c in b.Cmds) {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "split_here")) {
              int count;
              splitPoints.TryGetValue(b, out count);
              splitPoints[b] = count + 1;
            }
          }
        }

        if (splitPoints.Count() == 0) { // No manual split points here
          return null;
        }

        List<Split> splits = new List<Split>();
        Block entryPoint = impl.Blocks[0];
        var newEntryBlocks = DoManualSplit(impl.Blocks, entryPoint, -1, splitPoints.Keys.Contains(entryPoint), splitPoints.Keys);
        splits.Add(new Split(newEntryBlocks, gotoCmdOrigins, par, impl));   // REVIEW: Does gotoCmdOrigins need to be changed at all?        

        foreach (KeyValuePair<Block,int> pair in splitPoints) {
          for (int i = 0; i < pair.Value; i++) {
            bool blockInternalSplit = i < pair.Value - 1;   // There's at least one more split, after this one, in the current block
            var newBlocks = DoManualSplit(impl.Blocks, pair.Key, i, blockInternalSplit, splitPoints.Keys);
            Split s = new Split(newBlocks, gotoCmdOrigins, par, impl);   // REVIEW: Does gotoCmdOrigins need to be changed at all?
            splits.Add(s);
          }
        }

        return splits;
      }

      public static List<Split/*!*/>/*!*/ DoSplit(Split initial, double max_cost, int max) {
        Contract.Requires(initial != null);
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Split>>()));

        List<Split> res = new List<Split>();
        res.Add(initial);

        while (res.Count < max) {
          Split best = null;
          int best_idx = 0, pos = 0;
          foreach (Split s in res) {
            Contract.Assert(s != null);
            s.ComputeBestSplit(); // TODO check total_cost first
            if (s.total_cost > max_cost &&
                (best == null || best.total_cost < s.total_cost) &&
                (s.assertion_count > 1 || s.split_block != null)) {
              best = s;
              best_idx = pos;
            }
            pos++;
          }

          if (best == null)
            break; // no split found

          Split s0, s1;

          bool split_stats = CommandLineOptions.Clo.TraceVerify;

          if (split_stats) {
            Console.WriteLine("{0} {1} -->", best.split_block == null ? "SLICE" : ("SPLIT@" + best.split_block.Label), best.Stats);
            if (best.split_block != null) {
              GotoCmd g = best.split_block.TransferCmd as GotoCmd;
              if (g != null) {
                Console.Write("    exits: ");
                foreach (Block b in cce.NonNull(g.labelTargets)) {
                  Contract.Assert(b != null);
                  Console.Write("{0} ", b.Label);
                }
                Console.WriteLine("");
                Console.Write("    assumized: ");
                foreach (Block b in best.assumized_branches) {
                  Contract.Assert(b != null);
                  Console.Write("{0} ", b.Label);
                }
                Console.WriteLine("");
              }
            }
          }

          if (best.split_block != null) {
            s0 = best.SplitAt(0);
            s1 = best.SplitAt(1);
          } else {
            best.split_block = null;
            s0 = best.SliceAsserts(best.assertion_cost / 2, true);
            s1 = best.SliceAsserts(best.assertion_cost / 2, false);
          }

          if (true) {
            List<Block> ss = new List<Block>();
            ss.Add(s0.blocks[0]);
            ss.Add(s1.blocks[0]);
            try {
              best.SoundnessCheck(new HashSet<List<Block>>(new BlockListComparer()), best.blocks[0], ss);
            } catch (System.Exception e) {
              Console.WriteLine(e);
              best.DumpDot(-1);
              s0.DumpDot(-2);
              s1.DumpDot(-3);
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }
          }

          if (split_stats) {
            s0.ComputeBestSplit();
            s1.ComputeBestSplit();
            Console.WriteLine("    --> {0}", s0.Stats);
            Console.WriteLine("    --> {0}", s1.Stats);
          }

          if (CommandLineOptions.Clo.TraceVerify) {
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

      public Checker Checker {
        get {
          Contract.Ensures(Contract.Result<Checker>() != null);

          Contract.Assert(checker != null);
          return checker;
        }
      }

      public Task ProverTask {
        get {
          Contract.Assert(checker != null);
          return checker.ProverTask;
        }
      }

      public void ReadOutcome(ref Outcome cur_outcome, out bool prover_failed) {
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        ProverInterface.Outcome outcome = cce.NonNull(checker).ReadOutcome();

        if (CommandLineOptions.Clo.Trace && splitNo >= 0) {
          System.Console.WriteLine("      --> split #{0} done,  [{1} s] {2}", splitNo, checker.ProverRunTime.TotalSeconds, outcome);
        }

        if (CommandLineOptions.Clo.VcsDumpSplits) {
          DumpDot(splitNo);
        }

        prover_failed = false;

        switch (outcome) {
          case ProverInterface.Outcome.Valid:
            return;
          case ProverInterface.Outcome.Invalid:
            cur_outcome = Outcome.Errors;
            return;
          case ProverInterface.Outcome.OutOfMemory:
            prover_failed = true;
            if (cur_outcome != Outcome.Errors && cur_outcome != Outcome.Inconclusive)
              cur_outcome = Outcome.OutOfMemory;
            return;
          case ProverInterface.Outcome.TimeOut:
            prover_failed = true;
            if (cur_outcome != Outcome.Errors && cur_outcome != Outcome.Inconclusive)
              cur_outcome = Outcome.TimedOut;
            return;
          case ProverInterface.Outcome.OutOfResource:
            prover_failed = true;
            if (cur_outcome != Outcome.Errors && cur_outcome != Outcome.Inconclusive)
              cur_outcome = Outcome.OutOfResource;
            return;
          case ProverInterface.Outcome.Undetermined:
            if (cur_outcome != Outcome.Errors)
              cur_outcome = Outcome.Inconclusive;
            return;
          default:
            Contract.Assert(false);
            throw new cce.UnreachableException();
        }
      }

      /// <summary>
      /// As a side effect, updates "this.parent.CumulativeAssertionCount".
      /// </summary>
      public void BeginCheck(Checker checker, VerifierCallback callback, ModelViewInfo mvInfo, int no, int timeout)
      {
        Contract.Requires(checker != null);
        Contract.Requires(callback != null);

        splitNo = no;

        impl.Blocks = blocks;

        this.checker = checker;

        Dictionary<int, Absy> label2absy = new Dictionary<int, Absy>();

        ProverContext ctx = checker.TheoremProver.Context;
        Boogie2VCExprTranslator bet = ctx.BoogieExprTranslator;
        CodeExprConversionClosure cc = new CodeExprConversionClosure(label2absy, ctx);
        bet.SetCodeExprConverter(cc.CodeExprToVerificationCondition);

        var exprGen = ctx.ExprGen;
        VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : exprGen.Integer(BigNum.ZERO);

        VCExpr vc = parent.GenerateVCAux(impl, controlFlowVariableExpr, label2absy, checker.TheoremProver.Context);
        Contract.Assert(vc != null);

        if (!CommandLineOptions.Clo.UseLabels)
        {
          VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
          VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
          vc = exprGen.Implies(eqExpr, vc);
        }

        if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local)
        {
          reporter = new ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, parent.incarnationOriginMap, callback, mvInfo, cce.NonNull(this.Checker.TheoremProver.Context), parent.program);
        }
        else
        {
          reporter = new ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, parent.incarnationOriginMap, callback, mvInfo, this.Checker.TheoremProver.Context, parent.program);
        }

        if (CommandLineOptions.Clo.TraceVerify && no >= 0)
        {
          Console.WriteLine("-- after split #{0}", no);
          Print();
        }

        string desc = cce.NonNull(impl.Name);
        if (no >= 0)
          desc += "_split" + no;
        checker.BeginCheck(desc, vc, reporter);
      }

      private void SoundnessCheck(HashSet<List<Block>/*!*/>/*!*/ cache, Block/*!*/ orig, List<Block/*!*/>/*!*/ copies) {
        Contract.Requires(cce.NonNull(cache));
        Contract.Requires(orig != null);
        Contract.Requires(copies != null);
        {
          var t = new List<Block> { orig };
          foreach (Block b in copies) {
            Contract.Assert(b != null);
            t.Add(b);
          }
          if (cache.Contains(t)) {
            return;
          }
          cache.Add(t);
        }

        for (int i = 0; i < orig.Cmds.Count; ++i) {
          Cmd cmd = orig.Cmds[i];
          if (cmd is AssertCmd) {
            int found = 0;
            foreach (Block c in copies) {
              Contract.Assert(c != null);
              if (c.Cmds[i] == cmd) {
                found++;
              }
            }
            if (found == 0) {
              throw new System.Exception(string.Format("missing assertion: {0}({1})", cmd.tok.filename, cmd.tok.line));
            }
          }
        }

        foreach (Block exit in Exits(orig)) {
          Contract.Assert(exit != null);
          List<Block> newcopies = new List<Block>();
          foreach (Block c in copies) {
            foreach (Block cexit in Exits(c)) {
              Contract.Assert(cexit != null);
              if (cexit.Label == exit.Label) {
                newcopies.Add(cexit);
              }
            }
          }
          if (newcopies.Count == 0) {
            throw new System.Exception("missing exit " + exit.Label);
          }
          SoundnessCheck(cache, exit, newcopies);
        }
      }
    }
    #endregion


    public class CodeExprConversionClosure
    {
        Dictionary<int, Absy> label2absy;
        ProverContext ctx;
        public CodeExprConversionClosure(Dictionary<int, Absy> label2absy, ProverContext ctx)
        {
            this.label2absy = label2absy;
            this.ctx = ctx;
        }

        public VCExpr CodeExprToVerificationCondition(CodeExpr codeExpr, Hashtable blockVariables, List<VCExprLetBinding> bindings, bool isPositiveContext)
        {
            VCGen vcgen = new VCGen(new Program(), null, false, new List<Checker>());
            vcgen.variable2SequenceNumber = new Dictionary<Variable, int>();
            vcgen.incarnationOriginMap = new Dictionary<Incarnation, Absy>();
            vcgen.CurrentLocalVariables = codeExpr.LocVars;

            ResetPredecessors(codeExpr.Blocks);
            vcgen.AddBlocksBetween(codeExpr.Blocks);
            Dictionary<Variable, Expr> gotoCmdOrigins = vcgen.ConvertBlocks2PassiveCmd(codeExpr.Blocks, new List<IdentifierExpr>(), new ModelViewInfo(codeExpr));
            int ac;  // computed, but then ignored for this CodeExpr
            VCExpr startCorrect = VCGen.LetVCIterative(codeExpr.Blocks, null, label2absy, ctx, out ac, isPositiveContext);
            VCExpr vce = ctx.ExprGen.Let(bindings, startCorrect);
            if (vcgen.CurrentLocalVariables.Count != 0)
            {
                Boogie2VCExprTranslator translator = ctx.BoogieExprTranslator;
                List<VCExprVar> boundVars = new List<VCExprVar>();
                foreach (Variable v in vcgen.CurrentLocalVariables)
                {
                    Contract.Assert(v != null);
                    VCExprVar ev = translator.LookupVariable(v);
                    Contract.Assert(ev != null);
                    boundVars.Add(ev);
                    if (v.TypedIdent.Type.Equals(Bpl.Type.Bool))
                    {
                        // add an antecedent (tickleBool ev) to help the prover find a possible trigger
                        vce = ctx.ExprGen.Implies(ctx.ExprGen.Function(VCExpressionGenerator.TickleBoolOp, ev), vce);
                    }
                }
                vce = ctx.ExprGen.Forall(boundVars, new List<VCTrigger>(), vce);
            }
            if (isPositiveContext)
            {
                vce = ctx.ExprGen.Not(vce);
            } 
            return vce;
        }
    }

    public VCExpr GenerateVC(Implementation/*!*/ impl, VCExpr controlFlowVariableExpr, out Dictionary<int, Absy>/*!*/ label2absy, ProverContext proverContext, IList<VCExprVar> namedAssumeVars = null)
    {
      Contract.Requires(impl != null);
      Contract.Requires(proverContext != null);
      Contract.Ensures(Contract.ValueAtReturn(out label2absy) != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      label2absy = new Dictionary<int, Absy>();
      return GenerateVCAux(impl, controlFlowVariableExpr, label2absy, proverContext, namedAssumeVars: namedAssumeVars);
    }

    public VCExpr GenerateVCAux(Implementation/*!*/ impl, VCExpr controlFlowVariableExpr, Dictionary<int, Absy>/*!*/ label2absy, ProverContext proverContext, IList<VCExprVar> namedAssumeVars = null) {
      Contract.Requires(impl != null);
      Contract.Requires(proverContext != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      TypecheckingContext tc = new TypecheckingContext(null);
      impl.Typecheck(tc);

      VCExpr vc;
      int assertionCount;
      switch (CommandLineOptions.Clo.vcVariety) {
        case CommandLineOptions.VCVariety.Structured:
          vc = VCViaStructuredProgram(impl, label2absy, proverContext, out assertionCount);
          break;
        case CommandLineOptions.VCVariety.Block:
          vc = FlatBlockVC(impl, label2absy, false, false, false, proverContext, out assertionCount);
          break;
        case CommandLineOptions.VCVariety.BlockReach:
          vc = FlatBlockVC(impl, label2absy, false, true, false, proverContext, out assertionCount);
          break;
        case CommandLineOptions.VCVariety.Local:
          vc = FlatBlockVC(impl, label2absy, true, false, false, proverContext, out assertionCount);
          break;
        case CommandLineOptions.VCVariety.BlockNested:
          vc = NestedBlockVC(impl, label2absy, false, proverContext, out assertionCount);
          break;
        case CommandLineOptions.VCVariety.BlockNestedReach:
          vc = NestedBlockVC(impl, label2absy, true, proverContext, out assertionCount);
          break;
        case CommandLineOptions.VCVariety.Dag:
          if (cce.NonNull(CommandLineOptions.Clo.TheProverFactory).SupportsDags || CommandLineOptions.Clo.FixedPointEngine != null) {
            vc = DagVC(cce.NonNull(impl.Blocks[0]), controlFlowVariableExpr, label2absy, new Hashtable/*<Block, VCExpr!>*/(), proverContext, out assertionCount);
          } else {
            vc = LetVC(cce.NonNull(impl.Blocks[0]), controlFlowVariableExpr, label2absy, proverContext, out assertionCount);
          }
          break;
        case CommandLineOptions.VCVariety.DagIterative:
          vc = LetVCIterative(impl.Blocks, controlFlowVariableExpr, label2absy, proverContext, out assertionCount);
          break;
        case CommandLineOptions.VCVariety.Doomed:
          vc = FlatBlockVC(impl, label2absy, false, false, true, proverContext, out assertionCount);
          break;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();  // unexpected enumeration value
      }
      CumulativeAssertionCount += assertionCount;
      return vc;
    }

    void CheckIntAttributeOnImpl(Implementation impl, string name, ref int val) {
      Contract.Requires(impl != null);
      Contract.Requires(name != null);
      if (!(cce.NonNull(impl.Proc).CheckIntAttribute(name, ref val) || !impl.CheckIntAttribute(name, ref val))) {
        Console.WriteLine("ignoring ill-formed {:{0} ...} attribute on {1}, parameter should be an int", name, impl.Name);
      }
    }

    public override Outcome VerifyImplementation(Implementation/*!*/ impl, VerifierCallback/*!*/ callback) {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      if (impl.SkipVerification) {
        return Outcome.Inconclusive; // not sure about this one
      }

      callback.OnProgress("VCgen", 0, 0, 0.0);
      
      Stopwatch watch = new Stopwatch();
#if PRINT_TIME
      Console.WriteLine("Checking function {0}", impl.Name);
      watch.Reset();
      watch.Start();
#endif

      ConvertCFG2DAG(impl);

      SmokeTester smoke_tester = null;
      if (CommandLineOptions.Clo.SoundnessSmokeTest) {
        smoke_tester = new SmokeTester(this, impl, callback);
        smoke_tester.Copy();
      }

      ModelViewInfo mvInfo;
      var gotoCmdOrigins = PassifyImpl(impl, out mvInfo);

      // If "expand" attribute is supplied, expand any assertion of conjunctions into multiple assertions, one per conjunct
      foreach (var b in impl.Blocks)
      {
        List<Cmd> newCmds = new List<Cmd>();
        bool changed = false;
        foreach (var c in b.Cmds)
        {
          var a = c as AssertCmd;
          var ar = c as AssertRequiresCmd;
          var ae = c as AssertEnsuresCmd;
          var ai = c as LoopInitAssertCmd;
          var am = c as LoopInvMaintainedAssertCmd;
          // TODO:
          //use Duplicator and Substituter rather than new
          //nested IToken?
          //document expand attribute (search for {:ignore}, for example)
          //fix up new CallCmd, new Requires, new Ensures in CivlRefinement.cs
          Func<Expr,Expr,Expr> withType = (Expr from, Expr to) =>
          {
            NAryExpr nFrom = from as NAryExpr;
            NAryExpr nTo = to as NAryExpr;
            to.Type = from.Type;
            if (nFrom != null && nTo != null) nTo.TypeParameters = nFrom.TypeParameters;
            return to;
          };

          Action<int,Expr,Action<Expr>> traverse = null;
          traverse = (depth, e, act) =>
          {
            ForallExpr forall = e as ForallExpr;
            NAryExpr nary = e as NAryExpr;
            if (forall != null)
            {
              traverse(depth, forall.Body, e1 => act(withType(forall,
                new ForallExpr(e1.tok, forall.TypeParameters, forall.Dummies, forall.Attributes, forall.Triggers, e1))));
              return;
            }
            if (nary != null)
            {
              var args = nary.Args;
              IAppliable fun = nary.Fun;
              BinaryOperator bop = fun as BinaryOperator;
              FunctionCall call = fun as FunctionCall;
              if (bop != null)
              {
                switch (bop.Op)
                {
                  case BinaryOperator.Opcode.And:
                    traverse(depth, args[0], act);
                    traverse(depth, args[1], act);
                    return;
                  case BinaryOperator.Opcode.Imp:
                    traverse(depth, args[1], e1 => act(withType(nary,
                      new NAryExpr(e1.tok, fun, new List<Expr>() { args[0], e1 }))));
                    return;
                }
              }
              if (depth > 0 && call != null && call.Func != null)
              {
                Function cf = call.Func;
                Expr body = cf.Body;
                List<Variable> ins = cf.InParams;
                if (body == null && cf.DefinitionAxiom != null)
                {
                  ForallExpr all = cf.DefinitionAxiom.Expr as ForallExpr;
                  if (all != null)
                  {
                    NAryExpr def = all.Body as NAryExpr;
                    if (def != null && def.Fun is BinaryOperator && ((BinaryOperator) (def.Fun)).Op == BinaryOperator.Opcode.Iff)
                    {
                      body = def.Args[1];
                      ins = all.Dummies;
                    }
                  }
                }
                if (body != null)
                {
                  Func<Expr,Expr> new_f = e1 =>
                  {
                    Function f = new Function(cf.tok, "expand<" + cf.Name + ">", cf.TypeParameters, ins, cf.OutParams[0], cf.Comment);
                    f.Body = e1;
                    Token tok = new Token(e1.tok.line, e1.tok.col);
                    tok.filename = e.tok.filename + "(" + e.tok.line + "," + e.tok.col + ") --> " + e1.tok.filename;
                    return withType(nary, new NAryExpr(tok, new FunctionCall(f), args));
                  };
                  traverse(depth - 1, body, e1 => act(new_f(e1)));
                  return;
                }
              }
            }
            act(e);
          };

          if (a != null)
          {
            var attr = a.Attributes;
            if (ar != null && ar.Requires.Attributes != null) attr = ar.Requires.Attributes;
            if (ar != null && ar.Call.Attributes != null) attr = ar.Call.Attributes;
            if (ae != null && ae.Ensures.Attributes != null) attr = ae.Ensures.Attributes;
            if (QKeyValue.FindExprAttribute(attr, "expand") != null || QKeyValue.FindBoolAttribute(attr, "expand"))
            {
              int depth = QKeyValue.FindIntAttribute(attr, "expand", 100);
              Func<Expr,Expr> fe = e => Expr.Or(a.Expr, e);
              //traverse(depth, a.Expr, e => System.Console.WriteLine(e.GetType() + " :: " + e + " @ " + e.tok.line + ", " + e.tok.col));
              traverse(depth, a.Expr, e =>
                {
                  AssertCmd new_c = 
                    (ar != null) ? new AssertRequiresCmd(ar.Call, new Requires(e.tok, ar.Requires.Free, fe(e), ar.Requires.Comment)) :
                    (ae != null) ? new AssertEnsuresCmd(new Ensures(e.tok, ae.Ensures.Free, fe(e), ae.Ensures.Comment)) :
                    (ai != null) ? new LoopInitAssertCmd(e.tok, fe(e)) :
                    (am != null) ? new LoopInvMaintainedAssertCmd(e.tok, fe(e)) :
                    new AssertCmd(e.tok, fe(e));
                  new_c.Attributes = new QKeyValue(e.tok, "subsumption", new List<object>() { new LiteralExpr(e.tok, BigNum.FromInt(0)) }, a.Attributes);
                  newCmds.Add(new_c);
                });
            }
            newCmds.Add(c);
            changed = true;
          }
          else
          {
            newCmds.Add(c);
          }
        }
        if (changed) b.Cmds = newCmds;
      }

      double max_vc_cost = CommandLineOptions.Clo.VcsMaxCost;
      int tmp_max_vc_cost = -1, max_splits = CommandLineOptions.Clo.VcsMaxSplits, 
          max_kg_splits = CommandLineOptions.Clo.VcsMaxKeepGoingSplits;
      CheckIntAttributeOnImpl(impl, "vcs_max_cost", ref tmp_max_vc_cost);
      CheckIntAttributeOnImpl(impl, "vcs_max_splits", ref max_splits);
      CheckIntAttributeOnImpl(impl, "vcs_max_keep_going_splits", ref max_kg_splits);
      if (tmp_max_vc_cost >= 0) { 
        max_vc_cost = tmp_max_vc_cost;
      }

      Outcome outcome = Outcome.Correct;

      // Report all recycled failing assertions for this implementation.
      if (impl.RecycledFailingAssertions != null && impl.RecycledFailingAssertions.Any())
      {
        outcome = Outcome.Errors;
        foreach (var a in impl.RecycledFailingAssertions)
        {
          var checksum = a.Checksum;
          var oldCex = impl.ErrorChecksumToCachedError[checksum] as Counterexample;
          if (oldCex != null) {
            if (CommandLineOptions.Clo.VerifySnapshots < 3) {
              callback.OnCounterexample(oldCex, null);
            } else {
              // If possible, we use the old counterexample, but with the location information of "a"
              var cex = AssertCmdToCloneCounterexample(a, oldCex, impl.Blocks[0], gotoCmdOrigins);
              callback.OnCounterexample(cex, null);
              // OnCounterexample may have had side effects on the RequestId and OriginalRequestId fields.  We make
              // any such updates available in oldCex. (Is this really a good design? --KRML)
              oldCex.RequestId = cex.RequestId;
              oldCex.OriginalRequestId = cex.OriginalRequestId;
            }
          }
        }
      }

      Cores = CommandLineOptions.Clo.VcsCores;
      Stack<Split> work = new Stack<Split>();
      List<Split> currently_running = new List<Split>();
      ResetPredecessors(impl.Blocks);
      List<Split> manual_splits = Split.FindManualSplits(impl, gotoCmdOrigins, this);
      if (manual_splits != null) {
        foreach (var split in manual_splits) {
          work.Push(split);
        }
      } else {
        work.Push(new Split(impl.Blocks, gotoCmdOrigins, this, impl));
      }

      bool keep_going = max_kg_splits > 1;
      int total = 0;
      int no = max_splits == 1 && !keep_going ? -1 : 0;
      bool first_round = true;
      bool do_splitting = keep_going || max_splits > 1;
      double remaining_cost = 0.0, proven_cost = 0.0;

      if (do_splitting) {
        remaining_cost = work.Peek().Cost;
      }

      while (work.Any() || currently_running.Any())
      {
        bool prover_failed = false;
        Split s = null;
        var isWaiting = !work.Any();

        if (!isWaiting)
        {
          s = work.Peek();

          if (first_round && max_splits > 1)
          {
            prover_failed = true;
            remaining_cost -= s.Cost;
          }
          else
          {
            var timeout = (keep_going && s.LastChance) ? CommandLineOptions.Clo.VcsFinalAssertTimeout :
                  keep_going ? CommandLineOptions.Clo.VcsKeepGoingTimeout :
                  impl.TimeLimit;

            var checker = s.parent.FindCheckerFor(timeout, impl.ResourceLimit, false);            
            try
            {
              if (checker == null)
              {
                isWaiting = true;
                goto waiting;
              }
              else
              {
                s = work.Pop();
              }
              
              if (CommandLineOptions.Clo.Trace && no >= 0)
              {
                System.Console.WriteLine("    checking split {1}/{2}, {3:0.00}%, {0} ...",
                                     s.Stats, no + 1, total, 100 * proven_cost / (proven_cost + remaining_cost));
              }
              callback.OnProgress("VCprove", no < 0 ? 0 : no, total, proven_cost / (remaining_cost + proven_cost));
              
              Contract.Assert(s.parent == this);
              lock (checker)
              {
                s.BeginCheck(checker, callback, mvInfo, no, timeout);
              }
              
              no++;
              
              currently_running.Add(s);
            }
            catch (Exception)
            {
              checker.GoBackToIdle();
              throw;
            }
          }
        }

      waiting:
        if (isWaiting)
        {
          // Wait for one split to terminate.
          var tasks = currently_running.Select(splt => splt.ProverTask).ToArray();

          if (tasks.Any())
          {
            try
            {
              int index = Task.WaitAny(tasks);
              s = currently_running[index];
              currently_running.RemoveAt(index);

              if (do_splitting)
              {
                remaining_cost -= s.Cost;
              }

              lock (s.Checker)
              {
                s.ReadOutcome(ref outcome, out prover_failed);
              }

              if (do_splitting)
              {
                if (prover_failed)
                {
                  // even if the prover fails, we have learned something, i.e., it is 
                  // annoying to watch Boogie say Timeout, 0.00% a couple of times
                  proven_cost += s.Cost / 100;
                }
                else
                {
                  proven_cost += s.Cost;
                }
              }
              callback.OnProgress("VCprove", no < 0 ? 0 : no, total, proven_cost / (remaining_cost + proven_cost));

              if (prover_failed && !first_round && s.LastChance)
              {
                string msg = "some timeout";
                if (s.reporter != null && s.reporter.resourceExceededMessage != null)
                {
                  msg = s.reporter.resourceExceededMessage;
                }
                callback.OnCounterexample(s.ToCounterexample(s.Checker.TheoremProver.Context), msg);
                outcome = Outcome.Errors;
                break;
              }
            }
            finally
            {
              s.Checker.GoBackToIdle();
            }

            Contract.Assert(prover_failed || outcome == Outcome.Correct || outcome == Outcome.Errors || outcome == Outcome.Inconclusive);
          }
        }

        if (prover_failed)
        {
          int splits = first_round && max_splits > 1 ? max_splits : max_kg_splits;

          if (splits > 1)
          {
            List<Split> tmp = Split.DoSplit(s, max_vc_cost, splits);
            Contract.Assert(tmp != null);
            max_vc_cost = 1.0; // for future
            first_round = false;
            //tmp.Sort(new Comparison<Split!>(Split.Compare));
            foreach (Split a in tmp)
            {
              Contract.Assert(a != null);
              work.Push(a);
              total++;
              remaining_cost += a.Cost;
            }
            if (outcome != Outcome.Errors)
            {
              outcome = Outcome.Correct;
            }
          }
          else
          {
            Contract.Assert(outcome != Outcome.Correct);
            if (outcome == Outcome.TimedOut)
            {
              string msg = "some timeout";
              if (s.reporter != null && s.reporter.resourceExceededMessage != null)
              {
                msg = s.reporter.resourceExceededMessage;
              }
              callback.OnTimeout(msg);
            }
            else if (outcome == Outcome.OutOfMemory)
            {
              string msg = "out of memory";
              if (s.reporter != null && s.reporter.resourceExceededMessage != null)
              {
                msg = s.reporter.resourceExceededMessage;
              }
              callback.OnOutOfMemory(msg);
            } 
            else if (outcome == Outcome.OutOfResource) 
            {
              string msg = "out of resource";
              if (s.reporter != null && s.reporter.resourceExceededMessage != null) {
                msg = s.reporter.resourceExceededMessage;
              }
              callback.OnOutOfResource(msg);
            }

            break;
          }
        }
      }

      if (outcome == Outcome.Correct && smoke_tester != null) {
        smoke_tester.Test();
      }

      callback.OnProgress("done", 0, 0, 1.0);

#if PRINT_TIME
      watch.Stop();
      Console.WriteLine("Total time for this method: {0}", watch.Elapsed.ToString());
#endif

      return outcome;
    }

    public class ErrorReporter : ProverInterface.ErrorHandler {
      Dictionary<TransferCmd, ReturnCmd>/*!*/ gotoCmdOrigins;
      Dictionary<int, Absy>/*!*/ label2absy;
      List<Block/*!*/>/*!*/ blocks;
      protected Dictionary<Incarnation, Absy/*!*/>/*!*/ incarnationOriginMap;
      protected VerifierCallback/*!*/ callback;
      protected ModelViewInfo MvInfo;
      internal string resourceExceededMessage;
      static System.IO.TextWriter modelWriter;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(gotoCmdOrigins != null);
        Contract.Invariant(label2absy != null);
        Contract.Invariant(cce.NonNullElements(blocks));
        Contract.Invariant(cce.NonNullDictionaryAndValues(incarnationOriginMap));
        Contract.Invariant(callback != null);
        Contract.Invariant(context != null);
        Contract.Invariant(program != null);
      }


      public static TextWriter ModelWriter {
        get {
          Contract.Ensures(Contract.Result<TextWriter>() != null);

          if (ErrorReporter.modelWriter == null)
            ErrorReporter.modelWriter = CommandLineOptions.Clo.PrintErrorModelFile == null ? Console.Out : new StreamWriter(CommandLineOptions.Clo.PrintErrorModelFile, false);
          return ErrorReporter.modelWriter;
        }
      }

      protected ProverContext/*!*/ context;
      Program/*!*/ program;

      public IEnumerable<string> NecessaryAssumes
      {
        get { return program.NecessaryAssumes; }
      }

      public void AddNecessaryAssume(string id)
      {
        program.NecessaryAssumes.Add(id);
      }

      public ErrorReporter(Dictionary<TransferCmd, ReturnCmd>/*!*/ gotoCmdOrigins,
          Dictionary<int, Absy>/*!*/ label2absy,
          List<Block/*!*/>/*!*/ blocks,
          Dictionary<Incarnation, Absy/*!*/>/*!*/ incarnationOriginMap,
          VerifierCallback/*!*/ callback,
          ModelViewInfo mvInfo,
          ProverContext/*!*/ context,
          Program/*!*/ program) {
        Contract.Requires(gotoCmdOrigins != null);
        Contract.Requires(label2absy != null);
        Contract.Requires(cce.NonNullElements(blocks));
        Contract.Requires(cce.NonNullDictionaryAndValues(incarnationOriginMap));
        Contract.Requires(callback != null);
        Contract.Requires(context!=null);
        Contract.Requires(program!=null);
        this.gotoCmdOrigins = gotoCmdOrigins;
        this.label2absy = label2absy;
        this.blocks = blocks;
        this.incarnationOriginMap = incarnationOriginMap;
        this.callback = callback;
        this.MvInfo = mvInfo;

        this.context = context;
        this.program = program;
      }

      public override void OnModel(IList<string/*!*/>/*!*/ labels, Model model, ProverInterface.Outcome proverOutcome) {
        //Contract.Requires(cce.NonNullElements(labels));
        if (CommandLineOptions.Clo.PrintErrorModel >= 1 && model != null) {
          if (VC.ConditionGeneration.errorModelList != null)
          {
            VC.ConditionGeneration.errorModelList.Add(model);
          }
          
          model.Write(ErrorReporter.ModelWriter);
          ErrorReporter.ModelWriter.Flush();
        }

        // no counter examples reported.
        if (labels.Count == 0) return;

        Hashtable traceNodes = new Hashtable();
        foreach (string s in labels) {
          Contract.Assert(s != null);
          Absy absy = Label2Absy(s);
          Contract.Assert(absy != null);
          if (traceNodes.ContainsKey(absy))
            System.Console.WriteLine("Warning: duplicate label: " + s + " read while tracing nodes");
          else
            traceNodes.Add(absy, null);
        }

        List<Block> trace = new List<Block>();
        Block entryBlock = cce.NonNull(this.blocks[0]);
        Contract.Assert(traceNodes.Contains(entryBlock));
        trace.Add(entryBlock);

        Counterexample newCounterexample = TraceCounterexample(entryBlock, traceNodes, trace, model, MvInfo, incarnationOriginMap, context, new Dictionary<TraceLocation, CalleeCounterexampleInfo>());

        if (newCounterexample == null)
          return;

        #region Map passive program errors back to original program errors
        ReturnCounterexample returnExample = newCounterexample as ReturnCounterexample;
        if (returnExample != null) {
          foreach (Block b in returnExample.Trace) {
            Contract.Assert(b != null);
            Contract.Assume(b.TransferCmd != null);
            ReturnCmd cmd = gotoCmdOrigins.ContainsKey(b.TransferCmd) ? gotoCmdOrigins[b.TransferCmd] : null;
            if (cmd != null) {
              returnExample.FailingReturn = cmd;
              break;
            }
          }
        }
        #endregion
        callback.OnCounterexample(newCounterexample, null);
      }

      public override Absy Label2Absy(string label) {
        //Contract.Requires(label != null);
        Contract.Ensures(Contract.Result<Absy>() != null);

        int id = int.Parse(label);
        return cce.NonNull((Absy)label2absy[id]);
      }

      public override void OnResourceExceeded(string msg, IEnumerable<Tuple<AssertCmd, TransferCmd>> assertCmds = null) {
        //Contract.Requires(msg != null);
        resourceExceededMessage = msg;
        if (assertCmds != null)
        {
          foreach (var cmd in assertCmds)
          {
            Counterexample cex = AssertCmdToCounterexample(cmd.Item1, cmd.Item2 , new List<Block>(), null, null, context);
            cex.IsAuxiliaryCexForDiagnosingTimeouts = true;
            callback.OnCounterexample(cex, msg);
          }
        }
      }

      public override void OnProverWarning(string msg) {
        //Contract.Requires(msg != null);
        callback.OnWarning(msg);
      }
    }

    public class ErrorReporterLocal : ErrorReporter {
      public ErrorReporterLocal(Dictionary<TransferCmd, ReturnCmd>/*!*/ gotoCmdOrigins,
          Dictionary<int, Absy>/*!*/ label2absy,
          List<Block/*!*/>/*!*/ blocks,
          Dictionary<Incarnation, Absy/*!*/>/*!*/ incarnationOriginMap,
          VerifierCallback/*!*/ callback,
          ModelViewInfo mvInfo,
          ProverContext/*!*/ context,
          Program/*!*/ program)
        : base(gotoCmdOrigins, label2absy, blocks, incarnationOriginMap, callback, mvInfo, context, program) // here for aesthetic purposes //TODO: Maybe nix?
      {
        Contract.Requires(gotoCmdOrigins != null);
        Contract.Requires(label2absy != null);
        Contract.Requires(cce.NonNullElements(blocks));
        Contract.Requires(cce.NonNullDictionaryAndValues(incarnationOriginMap));
        Contract.Requires(callback != null);
        Contract.Requires(context != null);
        Contract.Requires(program != null);
      }

      public override void OnModel(IList<string/*!*/>/*!*/ labels, Model model, ProverInterface.Outcome proverOutcome) {
        //Contract.Requires(cce.NonNullElements(labels));
        // We ignore the error model here for enhanced error message purposes.
        // It is only printed to the command line.
        if (CommandLineOptions.Clo.PrintErrorModel >= 1 && model != null) {
          if (CommandLineOptions.Clo.PrintErrorModelFile != null) {
            model.Write(ErrorReporter.ModelWriter);
            ErrorReporter.ModelWriter.Flush();
          }
        }
        List<Block> traceNodes = new List<Block>();
        List<AssertCmd> assertNodes = new List<AssertCmd>();
        foreach (string s in labels) {
          Contract.Assert(s != null);
          Absy node = Label2Absy(s);
          if (node is Block) {
            Block b = (Block)node;
            traceNodes.Add(b);
          } else {
            AssertCmd a = (AssertCmd)node;
            assertNodes.Add(a);
          }
        }
        Contract.Assert(assertNodes.Count > 0);
        Contract.Assert(traceNodes.Count == assertNodes.Count);

        foreach (AssertCmd a in assertNodes) {
          // find the corresponding Block (assertNodes.Count is likely to be 1, or small in any case, so just do a linear search here)
          foreach (Block b in traceNodes) {
            if (b.Cmds.Contains(a)) {
              List<Block> trace = new List<Block>();
              trace.Add(b);
              Counterexample newCounterexample = AssertCmdToCounterexample(a, cce.NonNull(b.TransferCmd), trace, model, MvInfo, context);
              callback.OnCounterexample(newCounterexample, null);
              goto NEXT_ASSERT;
            }
          }
          Contract.Assert(false);
          throw new cce.UnreachableException();  // there was no block that contains the assert
        NEXT_ASSERT: {
          }
        }
      }
    }

      private void RecordCutEdge(Dictionary<Block,List<Block>> edgesCut, Block from, Block to){
          if (edgesCut != null)
          {
              if (!edgesCut.ContainsKey(from))
                  edgesCut.Add(from, new List<Block>());
              edgesCut[from].Add(to);
          }
      }

    public void ConvertCFG2DAG(Implementation impl, Dictionary<Block,List<Block>> edgesCut = null, int taskID = -1)
    {
      Contract.Requires(impl != null);
      impl.PruneUnreachableBlocks();  // This is needed for VCVariety.BlockNested, and is otherwise just an optimization

      CurrentLocalVariables = impl.LocVars;
      variable2SequenceNumber = new Dictionary<Variable, int>();
      incarnationOriginMap = new Dictionary<Incarnation, Absy>();

      #region Debug Tracing
      if (CommandLineOptions.Clo.TraceVerify) 
      {
        Console.WriteLine("original implementation");
        EmitImpl(impl, false);
      }
      #endregion

      #region Debug Tracing
      if (CommandLineOptions.Clo.TraceVerify) 
      {
        Console.WriteLine("after desugaring sugared commands like procedure calls");
        EmitImpl(impl, true);
      }
      #endregion

      // Recompute the predecessors, but first insert a dummy start node that is sure not to be the target of any goto (because the cutting of back edges
      // below assumes that the start node has no predecessor)
      impl.Blocks.Insert(0, new Block(new Token(-17, -4), "0", new List<Cmd>(), new GotoCmd(Token.NoToken, new List<String> { impl.Blocks[0].Label }, new List<Block> { impl.Blocks[0] })));
      ResetPredecessors(impl.Blocks);

      var k = Math.Max(CommandLineOptions.Clo.KInductionDepth, QKeyValue.FindIntAttribute(impl.Attributes, "kInductionDepth", -1));
      if(k < 0) {
        ConvertCFG2DAGStandard(impl, edgesCut, taskID);
      } else {
        ConvertCFG2DAGKInduction(impl, edgesCut, taskID, k);
      }
      
      #region Debug Tracing
      if (CommandLineOptions.Clo.TraceVerify) 
      {
        Console.WriteLine("after conversion into a DAG");
        EmitImpl(impl, true);
      }
      #endregion
    }

    private void ConvertCFG2DAGStandard(Implementation impl, Dictionary<Block, List<Block>> edgesCut, int taskID)
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
        for (int i = 0, n = header.Cmds.Count; i < n; i++)
        {
          PredicateCmd a = header.Cmds[i] as PredicateCmd;
          if (a != null)
          {
            if (a is AssertCmd)
            {
              AssertCmd c = (AssertCmd)a;
              AssertCmd b = null;

              if (CommandLineOptions.Clo.ConcurrentHoudini)
              {
                Contract.Assert(taskID >= 0);
                if (CommandLineOptions.Clo.Cho[taskID].DisableLoopInvEntryAssert)
                  b = new LoopInitAssertCmd(c.tok, Expr.True);
                else
                  b = new LoopInitAssertCmd(c.tok, c.Expr);
              }
              else
              {
                b = new LoopInitAssertCmd(c.tok, c.Expr);
              }

              b.Attributes = c.Attributes;
              b.ErrorData = c.ErrorData;
              prefixOfPredicateCmdsInit.Add(b);

              if (CommandLineOptions.Clo.ConcurrentHoudini)
              {
                Contract.Assert(taskID >= 0);
                if (CommandLineOptions.Clo.Cho[taskID].DisableLoopInvMaintainedAssert)
                  b = new Bpl.LoopInvMaintainedAssertCmd(c.tok, Expr.True);
                else
                  b = new Bpl.LoopInvMaintainedAssertCmd(c.tok, c.Expr);
              }
              else
              {
                b = new Bpl.LoopInvMaintainedAssertCmd(c.tok, c.Expr);
              }

              b.Attributes = c.Attributes;
              b.ErrorData = c.ErrorData;
              prefixOfPredicateCmdsMaintained.Add(b);
              header.Cmds[i] = new AssumeCmd(c.tok, c.Expr);
            }
            else
            {
              Contract.Assert(a is AssumeCmd);
              if (Bpl.CommandLineOptions.Clo.AlwaysAssumeFreeLoopInvariants)
              {
                // Usually, "free" stuff, like free loop invariants (and the assume statements
                // that stand for such loop invariants) are ignored on the checking side.  This
                // command-line option changes that behavior to always assume the conditions.
                prefixOfPredicateCmdsInit.Add(a);
                prefixOfPredicateCmdsMaintained.Add(a);
              }
            }
          }
          else if (header.Cmds[i] is CommentCmd)
          {
            // ignore
          }
          else
          {
            break; // stop when an assignment statement (or any other non-predicate cmd) is encountered
          }
        }
        #endregion

        #region Copy the prefix of predicate commands into each predecessor. Do this *before* cutting the backedge!!
        for (int predIndex = 0, n = header.Predecessors.Count; predIndex < n; predIndex++)
        {
          Block pred = cce.NonNull(header.Predecessors[predIndex]);

          // Create a block between header and pred for the predicate commands if pred has more than one successor 
          GotoCmd gotocmd = cce.NonNull((GotoCmd)pred.TransferCmd);
          Contract.Assert(gotocmd.labelNames != null);  // if "pred" is really a predecessor, it may be a GotoCmd with at least one label
          if (gotocmd.labelNames.Count > 1)
          {
            Block newBlock = CreateBlockBetween(predIndex, header);
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
          Debug.Assert(backEdgeNode.TransferCmd is GotoCmd, "An node was identified as the source for a backedge, but it does not have a goto command.");
          GotoCmd gtc = backEdgeNode.TransferCmd as GotoCmd;
          if (gtc != null && gtc.labelTargets != null && gtc.labelTargets.Count > 1)
          {
            // then remove the backedge by removing the target block from the list of gotos
            List<Block> remainingTargets = new List<Block>();
            List<String> remainingLabels = new List<String>();
            Contract.Assume(gtc.labelNames != null);
            for (int i = 0, n = gtc.labelTargets.Count; i < n; i++)
            {
              if (gtc.labelTargets[i] != header)
              {
                remainingTargets.Add(gtc.labelTargets[i]);
                remainingLabels.Add(gtc.labelNames[i]);
              }
              else
                RecordCutEdge(edgesCut, backEdgeNode, header);
            }
            gtc.labelTargets = remainingTargets;
            gtc.labelNames = remainingLabels;
          }
          else
          {
            // This backedge is the only out-going edge from this node.
            // Add an "assume false" statement to the end of the statements
            // inside of the block and change the goto command to a return command.
            AssumeCmd ac = new AssumeCmd(Token.NoToken, Expr.False);
            backEdgeNode.Cmds.Add(ac);
            backEdgeNode.TransferCmd = new ReturnCmd(Token.NoToken);
            if (gtc != null && gtc.labelTargets != null && gtc.labelTargets.Count == 1)
              RecordCutEdge(edgesCut, backEdgeNode, gtc.labelTargets[0]);
          }
          #region Remove the backedge node from the list of predecessor nodes in the header
          List<Block> newPreds = new List<Block>();
          foreach (Block p in header.Predecessors)
          {
            if (p != backEdgeNode)
              newPreds.Add(p);
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
            havocExprs.Add(ie);
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

    public static List<Variable> VarsAssignedInLoop(Graph<Block> g, Block header)
    {
      List<Variable> varsToHavoc = new List<Variable>();
      foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
      {
        Contract.Assert(backEdgeNode != null);
        foreach (Block b in g.NaturalLoops(header, backEdgeNode))
        {
          Contract.Assert(b != null);
          foreach (Cmd c in b.Cmds)
          {
            Contract.Assert(c != null);
            c.AddAssignedVariables(varsToHavoc);
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
            foreach(var v in Collector.usedVars) {
              referencedVars.Add(v);
            }
          }
        }
      }
      return referencedVars;
    }

    private void ConvertCFG2DAGKInduction(Implementation impl, Dictionary<Block, List<Block>> edgesCut, int taskID, int inductionK) {

      // K-induction has not been adapted to be aware of these parameters which standard CFG to DAG transformation uses
      Contract.Requires(edgesCut == null);
      Contract.Requires(taskID == -1);
      Contract.Requires(0 <= inductionK);

      bool contRuleApplication = true;
      while (contRuleApplication) {
        contRuleApplication = false;

        #region Use the graph library to figure out where the (natural) loops are

        #region Create the graph by adding the source node and each edge
        Graph<Block> g = Program.GraphFromImpl(impl);
        #endregion

        g.ComputeLoops(); // this is the call that does all of the processing
        if (!g.Reducible) {
          throw new VCGenException("Irreducible flow graphs are unsupported.");
        }

        #endregion

        foreach (Block header in cce.NonNull(g.Headers)) {
          Contract.Assert(header != null);

          #region Debug Tracing
          if (CommandLineOptions.Clo.TraceVerify)
          {
            Console.WriteLine("Applying k-induction rule with k=" + inductionK);
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
                havocExprs.Add(ie);
          }
          // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
          // the source location for this later on
          HavocCmd hc = new HavocCmd(newHeader.tok, havocExprs);
          List<Cmd> havocCmds = new List<Cmd>();
          havocCmds.Add(hc);

          Block havocBlock = new Block(newHeader.tok, newHeader.Label + "_havoc", havocCmds,
                                        new GotoCmd (newHeader.tok, new List<Block> { newHeader }));

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
                foreach (Block b in cce.NonNull(g.BackEdgeNodes(header))) { Contract.Assert(b != null); backEdgeNodes.Add(b, null); }

                for (int predIndex = 0, n = header.Predecessors.Count(); predIndex < n; predIndex++)
                {
                    Block pred = cce.NonNull(header.Predecessors[predIndex]);
                    if (!backEdgeNodes.ContainsKey(pred))
                    {
                        GotoCmd gc = pred.TransferCmd as GotoCmd;
                        Contract.Assert(gc != null);
                        for (int i = 0; i < gc.labelTargets.Count(); ++i)
                        {
                            if (gc.labelTargets[i] == header)
                            {
                                gc.labelTargets[i] = newHeader;
                                gc.labelNames[i] = newHeader.Label;
                                newHeader.Predecessors.Add(pred);
                            }
                        }
                    }
                }
                impl.PruneUnreachableBlocks();

                #endregion

                contRuleApplication = true;
                break;
            }

        }

        ResetPredecessors(impl.Blocks);
        impl.FreshenCaptureStates();

    }

    private Block DuplicateLoop(Implementation impl, Graph<Block> g,
                                Block header, Block nextHeader, bool cutExits,
                                bool toAssumptions, string suffix)
    {
        IDictionary<Block, Block> ori2CopiedBlocks = new Dictionary<Block, Block>();
        Duplicator duplicator = new Duplicator();

        #region create copies of all blocks in the loop
        foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
        {
            Contract.Assert(backEdgeNode != null);
            foreach (Block b in g.NaturalLoops(header, backEdgeNode))
            {
                Contract.Assert(b != null);
                if (!ori2CopiedBlocks.ContainsKey(b))
                {
                    Block copy = (Block)duplicator.Visit(b);
                    copy.Cmds = new List<Cmd>(copy.Cmds); // Philipp Ruemmer commented that this was necessary due to a bug in the Duplicator.  That was a long time; worth checking whether this has been fixed
                    copy.Predecessors = new List<Block>();
                    copy.Label = copy.Label + suffix;

                    #region turn asserts into assumptions
                    if (toAssumptions)
                    {
                        for (int i = 0; i < copy.Cmds.Count(); ++i)
                        {
                            AssertCmd ac = copy.Cmds[i] as AssertCmd;
                            if (ac != null)
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
        }
        #endregion

        #region adjust the transfer commands of the newly created blocks
        foreach (KeyValuePair<Block, Block> pair in ori2CopiedBlocks)
        {
            Block copy = pair.Value;
            GotoCmd gc = copy.TransferCmd as GotoCmd;
            if (gc != null)
            {
                List<Block> newTargets = new List<Block>();
                List<string> newLabels = new List<string>();

                for (int i = 0; i < gc.labelTargets.Count(); ++i)
                {
                    Block newTarget;
                    if (gc.labelTargets[i] == header)
                    {
                        if (nextHeader != null)
                        {
                            newTargets.Add(nextHeader);
                            newLabels.Add(nextHeader.Label);
                            nextHeader.Predecessors.Add(copy);
                        }
                    }
                    else if (ori2CopiedBlocks.TryGetValue(gc.labelTargets[i], out newTarget))
                    {
                        newTargets.Add(newTarget);
                        newLabels.Add(newTarget.Label);
                        newTarget.Predecessors.Add(copy);
                    }
                    else if (!cutExits)
                    {
                        newTargets.Add(gc.labelTargets[i]);
                        newLabels.Add(gc.labelNames[i]);
                        gc.labelTargets[i].Predecessors.Add(copy);
                    }
                }

                if (newTargets.Count() == 0)
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

    public void DesugarCalls(Implementation impl) {
      foreach (Block block in impl.Blocks) {
        List<Cmd> newCmds = new List<Cmd>();
        foreach (Cmd cmd in block.Cmds) {
          SugaredCmd sugaredCmd = cmd as SugaredCmd;
          if (sugaredCmd != null) {
            StateCmd stateCmd = sugaredCmd.Desugaring as StateCmd;
            foreach (Variable v in stateCmd.Locals) {
              impl.LocVars.Add(v);
            }
            newCmds.AddRange(stateCmd.Cmds);
          }
          else {
            newCmds.Add(cmd);
          }
        }
        block.Cmds = newCmds;
      }
    }

    public Dictionary<TransferCmd, ReturnCmd> PassifyImpl(Implementation impl, out ModelViewInfo mvInfo)
    {
      Contract.Requires(impl != null);
      Contract.Requires(program != null);
      Contract.Ensures(Contract.Result<Dictionary<TransferCmd, ReturnCmd>>() != null);

      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins = new Dictionary<TransferCmd, ReturnCmd>();
      Block exitBlock = GenerateUnifiedExit(impl, gotoCmdOrigins);
      
      #region Debug Tracing
      if (CommandLineOptions.Clo.TraceVerify) 
      {
        Console.WriteLine("after creating a unified exit block");
        EmitImpl(impl, true);
      }
      #endregion

      #region Insert pre- and post-conditions and where clauses as assume and assert statements
      {
        List<Cmd> cc = new List<Cmd>();
        // where clauses of global variables
        lock (program.TopLevelDeclarations)
        {
          foreach (var gvar in program.GlobalVariables)
          {
            if (gvar != null && gvar.TypedIdent.WhereExpr != null)
            {
              Cmd c = new AssumeCmd(gvar.tok, gvar.TypedIdent.WhereExpr);
              cc.Add(c);
            }
          }
        }
        // where clauses of in- and out-parameters
        cc.AddRange(GetParamWhereClauses(impl));
        // where clauses of local variables
        foreach (Variable lvar in impl.LocVars) {Contract.Assert(lvar != null);
          if (lvar.TypedIdent.WhereExpr != null) {
            Cmd c = new AssumeCmd(lvar.tok, lvar.TypedIdent.WhereExpr);
            cc.Add(c);
          } else if (QKeyValue.FindBoolAttribute(lvar.Attributes, "assumption")) {
            cc.Add(new AssumeCmd(lvar.tok, new IdentifierExpr(lvar.tok, lvar), new QKeyValue(lvar.tok, "assumption_variable_initialization", new List<object>(), null)));
          }
        }
        // add cc and the preconditions to new blocks preceding impl.Blocks[0]
        InjectPreconditions(impl, cc);

        // append postconditions, starting in exitBlock and continuing into other blocks, if needed
        InjectPostConditions(impl, exitBlock, gotoCmdOrigins);
      }
      #endregion
      
      #region Support for stratified inlining
      addExitAssert(impl.Name, exitBlock);
      #endregion

                 
      #region Debug Tracing
      if (CommandLineOptions.Clo.TraceVerify) 
      {
        Console.WriteLine("after inserting pre- and post-conditions");
        EmitImpl(impl, true);
      }
      #endregion

      AddBlocksBetween(impl.Blocks);
      
      #region Debug Tracing
      if (CommandLineOptions.Clo.TraceVerify) 
      {
        Console.WriteLine("after adding empty blocks as needed to catch join assumptions");
        EmitImpl(impl, true);
      }
      #endregion

      if (CommandLineOptions.Clo.LiveVariableAnalysis > 0) {
        Microsoft.Boogie.LiveVariableAnalysis.ComputeLiveVariables(impl);
      }

      mvInfo = new ModelViewInfo(program, impl);
      Convert2PassiveCmd(impl, mvInfo);

      if (QKeyValue.FindBoolAttribute(impl.Attributes, "may_unverified_instrumentation"))
      {
        InstrumentWithMayUnverifiedConditions(impl, exitBlock);
      }

      #region Peep-hole optimizations
      if (CommandLineOptions.Clo.RemoveEmptyBlocks){
        #region Get rid of empty blocks
        {
          RemoveEmptyBlocksIterative(impl.Blocks);
          impl.PruneUnreachableBlocks();
        }
        #endregion Get rid of empty blocks
        
        #region Debug Tracing
        if (CommandLineOptions.Clo.TraceVerify) 
        {
          Console.WriteLine("after peep-hole optimizations");
          EmitImpl(impl, true);
        }
        #endregion
      }
      #endregion Peep-hole optimizations

      HandleSelectiveChecking(impl);


//      #region Constant Folding
//      #endregion
//      #region Debug Tracing
//      if (CommandLineOptions.Clo.TraceVerify) 
//      {
//        Console.WriteLine("after constant folding");
//        EmitImpl(impl, true);
//      }
//      #endregion

      return gotoCmdOrigins;
    }

    #region Simplified May-Unverified Analysis and Instrumentation

    static void InstrumentWithMayUnverifiedConditions(Implementation impl, Block unifiedExitBlock)
    {
      var q = new Queue<Block>();
      q.Enqueue(unifiedExitBlock);
      var conditionOnBlockEntry = new Dictionary<Block, HashSet<Variable>>();
      while (q.Any())
      {
        var block = q.Dequeue();

        if (conditionOnBlockEntry.ContainsKey(block))
        {
          continue;
        }

        var gotoCmd = block.TransferCmd as GotoCmd;
        if (gotoCmd != null && gotoCmd.labelTargets.Any(b => !conditionOnBlockEntry.ContainsKey(b)))
        {
          q.Enqueue(block);
          continue;
        }

        HashSet<Variable> cond = new HashSet<Variable>();
        if (gotoCmd != null)
        {
          var mayInstrs = new List<Block>();
          bool noInstr = true;
          foreach (var succ in gotoCmd.labelTargets)
          {
            var c = conditionOnBlockEntry[succ];
            if (c != null)
            {
              mayInstrs.Add(succ);
            }
            else
            {
              noInstr = false;
            }
            cond = JoinVariableSets(cond, c);
          }
          if (!noInstr)
          {
            foreach (var instr in mayInstrs)
            {
              InstrumentWithCondition(instr, 0, conditionOnBlockEntry[instr]);
            }
          }
        }
        
        for (int i = block.Cmds.Count - 1; 0 <= i; i--)
        {
          var cmd = block.Cmds[i];
          if (cond == null) { break; }

          var assertCmd = cmd as AssertCmd;
          if (assertCmd != null)
          {
            var litExpr = assertCmd.Expr as LiteralExpr;
            if (litExpr != null && litExpr.IsTrue)
            {
              continue;
            }

            HashSet<Variable> vu = null;
            if (assertCmd.VerifiedUnder == null)
            {
              vu = null;
            }
            else
            {
              HashSet<Variable> vars;
              if (IsConjunctionOfAssumptionVariables(assertCmd.VerifiedUnder, out vars))
              {
                vu = vars;
                // TODO(wuestholz): Maybe drop the :verified_under attribute.
              }
              else
              {
                vu = null;
              }
            }

            if (vu == null)
            {
              InstrumentWithCondition(block, i + 1, cond);
            }

            cond = JoinVariableSets(cond, vu);
          }
        }

        if (cond != null && block.Predecessors.Count == 0)
        {
          // TODO(wuestholz): Should we rather instrument each block?
          InstrumentWithCondition(block, 0, cond);
        }

        foreach (var pred in block.Predecessors)
        {
          q.Enqueue(pred);
        }

        conditionOnBlockEntry[block] = cond;
      }
    }

    private static void InstrumentWithCondition(Block block, int idx, HashSet<Variable> condition)
    {
      var conj = Expr.BinaryTreeAnd(condition.Select(v => (Expr)new IdentifierExpr(Token.NoToken, v)).ToList());
      block.Cmds.Insert(idx, new AssumeCmd(Token.NoToken, Expr.Not(conj)));
    }

    static HashSet<Variable> JoinVariableSets(HashSet<Variable> c0, HashSet<Variable> c1)
    {
      // We use the following lattice:
      // - Top: null (i.e., true)
      // - Bottom: new HashSet<Variable>() (i.e., false)
      // - Other Elements: new HashSet<Variable>(...) (i.e., conjunctions of assumption variables)

      if (c0 == null || c1 == null)
      {
        return null;
      }
      var result = new HashSet<Variable>(c0);
      result.UnionWith(c1);
      return result;
    }

    static bool IsAssumptionVariableOrIncarnation(Variable v)
    {
      if (QKeyValue.FindBoolAttribute(v.Attributes, "assumption")) { return true; }
      var incar = v as Incarnation;
      return incar == null || QKeyValue.FindBoolAttribute(incar.OriginalVariable.Attributes, "assumption");
    }

    static bool IsConjunctionOfAssumptionVariables(Expr expr, out HashSet<Variable> variables)
    {
      Contract.Requires(expr != null);

      variables = null;
      var litExpr = expr as LiteralExpr;
      if (litExpr != null && (litExpr.IsFalse || litExpr.IsTrue))
      {
        if (litExpr.IsTrue)
        {
          variables = new HashSet<Variable>();
        }
        return true;
      }

      var idExpr = expr as IdentifierExpr;
      if (idExpr != null && IsAssumptionVariableOrIncarnation(idExpr.Decl))
      {
        variables = new HashSet<Variable>();
        variables.Add(idExpr.Decl);
        return true;
      }

      var andExpr = expr as NAryExpr;
      if (andExpr != null)
      {
        var fun = andExpr.Fun as BinaryOperator;
        if (fun != null && fun.Op == BinaryOperator.Opcode.And && andExpr.Args != null)
        {
          bool res = true;
          variables = new HashSet<Variable>();
          foreach (var op in andExpr.Args)
          {
            HashSet<Variable> vars;
            var r = IsConjunctionOfAssumptionVariables(op, out vars);
            res &= r;
            variables = JoinVariableSets(variables, vars);
            if (!res) { break; }
          }
          return res;
        }
      }

      return false;
    }

    #endregion

    private static void HandleSelectiveChecking(Implementation impl)
    {
      if (QKeyValue.FindBoolAttribute(impl.Attributes, "selective_checking") ||
          QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "selective_checking")) {

        var startPoints = new List<Block>();
        foreach (var b in impl.Blocks) {
          foreach (Cmd c in b.Cmds) {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "start_checking_here")) {
              startPoints.Add(b);
              break;
            }
          }
        }

        // Compute the set of blocks reachable from blocks containing "start_checking_here"
        var blocksToCheck = new HashSet<Block>();
        foreach (var b in startPoints) {
          var todo = new Stack<Block>();
          var wasThere = blocksToCheck.Contains(b);
          todo.Push(b);
          while (todo.Count > 0) {
            var x = todo.Pop();
            if (blocksToCheck.Contains(x)) continue;
            blocksToCheck.Add(x);
            var ex = x.TransferCmd as GotoCmd;
            if (ex != null)
              foreach (Block e in ex.labelTargets)
                todo.Push(e);
          }
          if (!wasThere) blocksToCheck.Remove(b);
        }
        
        // Convert asserts to assumes in "unreachable" blocks, as well as in portions of blocks before we reach "start_checking_here"
        foreach (var b in impl.Blocks) {
          if (blocksToCheck.Contains(b)) continue;  // All reachable blocks must be checked in their entirety, so don't change anything
          var newCmds = new List<Cmd>();
          var copyMode = false;
          foreach (Cmd c in b.Cmds) {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "start_checking_here"))
              copyMode = true;
            var asrt = c as AssertCmd;
            if (copyMode || asrt == null)
              newCmds.Add(c);
            else
              newCmds.Add(AssertTurnedIntoAssume(asrt));
          }

          b.Cmds = newCmds;
        }
      }
    }

    // Used by stratified inlining
    protected virtual void addExitAssert(string implName, Block exitBlock)
    {
    }

    public virtual Counterexample extractLoopTrace(Counterexample cex, string mainProcName, Program program, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
        // Construct the set of inlined procs in the original program
        var inlinedProcs = new HashSet<string>();
        foreach (var proc in program.Procedures)
        {
            if (!(proc is LoopProcedure))
            {
                inlinedProcs.Add(proc.Name);
            }
        }

        return extractLoopTraceRec(
            new CalleeCounterexampleInfo(cex, new List<object>()),
            mainProcName, inlinedProcs, extractLoopMappingInfo).counterexample;
    }

    protected CalleeCounterexampleInfo extractLoopTraceRec(
        CalleeCounterexampleInfo cexInfo, string currProc,
        HashSet<string> inlinedProcs, 
        Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
        Contract.Requires(currProc != null);
        if (cexInfo.counterexample == null) return cexInfo;

        var cex = cexInfo.counterexample;
        // Go through all blocks in the trace, map them back to blocks in the original program (if there is one)
        var ret = cex.Clone();
        ret.Trace = new List<Block>();
        ret.calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();

        for (int numBlock = 0; numBlock < cex.Trace.Count; numBlock ++ )
        {
            Block block = cex.Trace[numBlock];
            var origBlock = elGetBlock(currProc, block, extractLoopMappingInfo);
            if (origBlock != null) ret.Trace.Add(origBlock);
            var callCnt = 1;
            for (int numInstr = 0; numInstr < block.Cmds.Count; numInstr ++) {
                Cmd cmd = block.Cmds[numInstr];
                var loc = new TraceLocation(numBlock, numInstr);
                if (!cex.calleeCounterexamples.ContainsKey(loc))
                {
                    if (getCallee(cex.getTraceCmd(loc), inlinedProcs) != null) callCnt++;
                    continue;
                }
                string callee = cex.getCalledProcName(cex.getTraceCmd(loc));
                Contract.Assert(callee != null);
                var calleeTrace = cex.calleeCounterexamples[loc];
                Debug.Assert(calleeTrace != null);

                var origTrace = extractLoopTraceRec(calleeTrace, callee, inlinedProcs, extractLoopMappingInfo);

                if (elIsLoop(callee))
                {
                    // Absorb the trace into the current trace

                    int currLen = ret.Trace.Count;
                    ret.Trace.AddRange(origTrace.counterexample.Trace);

                    foreach (var kvp in origTrace.counterexample.calleeCounterexamples)
                    {
                        var newloc = new TraceLocation(kvp.Key.numBlock + currLen, kvp.Key.numInstr);
                        ret.calleeCounterexamples.Add(newloc, kvp.Value);
                    }

                }
                else
                {
                    var origLoc = new TraceLocation(ret.Trace.Count - 1, getCallCmdPosition(origBlock, callCnt, inlinedProcs, callee));
                    ret.calleeCounterexamples.Add(origLoc, origTrace);
                    callCnt++;
                }
            }
        }
        return new CalleeCounterexampleInfo(ret, cexInfo.args);
    }

    // return the position of the i^th CallCmd in the block (count only those Calls that call a procedure in inlinedProcs). 
    // Assert failure if there isn't any.
    // Assert that the CallCmd found calls "callee"
    private int getCallCmdPosition(Block block, int i, HashSet<string> inlinedProcs, string callee)
    {
        Debug.Assert(i >= 1);
        for (int pos = 0; pos < block.Cmds.Count; pos++)
        {
            Cmd cmd = block.Cmds[pos];
            string procCalled = getCallee(cmd, inlinedProcs);

            if (procCalled != null)
            {
                if (i == 1)
                {
                    Debug.Assert(procCalled == callee);
                    return pos;
                }
                i--;
            }
        }

        Debug.Assert(false, "Didn't find the i^th call cmd");
        return -1;
    }

    private string getCallee(Cmd cmd, HashSet<string> inlinedProcs)
    {
        string procCalled = null;
        if (cmd is CallCmd)
        {
            var cc = (CallCmd)cmd;
            if (inlinedProcs.Contains(cc.Proc.Name))
            {
                procCalled = cc.Proc.Name;
            }
        }

        if (cmd is AssumeCmd)
        {
            var expr = (cmd as AssumeCmd).Expr as NAryExpr;
            if (expr != null)
            {
                if (inlinedProcs.Contains(expr.Fun.FunctionName))
                {
                    procCalled = expr.Fun.FunctionName;
                }
            }
        }
        return procCalled;
    }

    protected virtual bool elIsLoop(string procname)
    {
      return false;
    }

    private Block elGetBlock(string procname, Block block, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
        Contract.Requires(procname != null);

        if (!extractLoopMappingInfo.ContainsKey(procname))
            return block;

        if (!extractLoopMappingInfo[procname].ContainsKey(block.Label))
            return null;

        return extractLoopMappingInfo[procname][block.Label];
    }

    static Counterexample TraceCounterexample(
                          Block/*!*/ b, Hashtable/*!*/ traceNodes, List<Block>/*!*/ trace, Model errModel, ModelViewInfo mvInfo,
                          Dictionary<Incarnation, Absy/*!*/>/*!*/ incarnationOriginMap,
                          ProverContext/*!*/ context,
                          Dictionary<TraceLocation/*!*/, CalleeCounterexampleInfo/*!*/>/*!*/ calleeCounterexamples)
    {
        Contract.Requires(b != null);
        Contract.Requires(traceNodes != null);
        Contract.Requires(trace != null);
        Contract.Requires(cce.NonNullDictionaryAndValues(incarnationOriginMap));
        Contract.Requires(context != null);
        Contract.Requires(cce.NonNullDictionaryAndValues(calleeCounterexamples));
        // After translation, all potential errors come from asserts.

        while (true)
        {
            List<Cmd> cmds = b.Cmds;
            Contract.Assert(cmds != null);
            TransferCmd transferCmd = cce.NonNull(b.TransferCmd);
            for (int i = 0; i < cmds.Count; i++)
            {
                Cmd cmd = cce.NonNull(cmds[i]);

                // Skip if 'cmd' not contained in the trace or not an assert
                if (cmd is AssertCmd && traceNodes.Contains(cmd))
                {
                    Counterexample newCounterexample = AssertCmdToCounterexample((AssertCmd)cmd, transferCmd, trace, errModel, mvInfo, context);
                    Contract.Assert(newCounterexample != null);
                    newCounterexample.AddCalleeCounterexample(calleeCounterexamples);
                    return newCounterexample;
                }
            }

            GotoCmd gotoCmd = transferCmd as GotoCmd;
            if (gotoCmd == null) return null;
            Block foundBlock = null;
            foreach (Block bb in cce.NonNull(gotoCmd.labelTargets))
            {
                Contract.Assert(bb != null);
                if (traceNodes.Contains(bb))
                {
                    foundBlock = bb;
                    break;
                }
            }
            if (foundBlock == null) return null;
            trace.Add(foundBlock);
            b = foundBlock;
        }
    }

    public static Counterexample AssertCmdToCounterexample(AssertCmd cmd, TransferCmd transferCmd, List<Block> trace, Model errModel, ModelViewInfo mvInfo, ProverContext context) 
    {
      Contract.Requires(cmd != null);
      Contract.Requires(transferCmd != null);
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      Contract.Ensures(Contract.Result<Counterexample>() != null);

      List<string> relatedInformation = new List<string>();
      
      // See if it is a special assert inserted in translation
      if (cmd is AssertRequiresCmd)
      {
        AssertRequiresCmd assertCmd = (AssertRequiresCmd)cmd;
        Contract.Assert(assertCmd != null);
        CallCounterexample cc = new CallCounterexample(trace, assertCmd.Call, assertCmd.Requires, errModel, mvInfo, context, assertCmd.Checksum);
        cc.relatedInformation = relatedInformation;
        return cc;
      }
      else if (cmd is AssertEnsuresCmd)
      {
        AssertEnsuresCmd assertCmd = (AssertEnsuresCmd)cmd;
        Contract.Assert(assertCmd != null);
        ReturnCounterexample rc = new ReturnCounterexample(trace, transferCmd, assertCmd.Ensures, errModel, mvInfo, context, cmd.Checksum);
        rc.relatedInformation = relatedInformation;
        return rc;
      }
      else 
      {
        AssertCounterexample ac = new AssertCounterexample(trace, (AssertCmd)cmd, errModel, mvInfo, context);
        ac.relatedInformation = relatedInformation;
        return ac;
      }
    }

    /// <summary>
    /// Returns a clone of "cex", but with the location stored in "cex" replaced by those from "assrt".
    /// </summary>
    public static Counterexample AssertCmdToCloneCounterexample(AssertCmd assrt, Counterexample cex, Block implEntryBlock, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins) {
      Contract.Requires(assrt != null);
      Contract.Requires(cex != null);
      Contract.Requires(implEntryBlock != null);
      Contract.Requires(gotoCmdOrigins != null);
      Contract.Ensures(Contract.Result<Counterexample>() != null);

      List<string> relatedInformation = new List<string>();

      Counterexample cc;
      if (assrt is AssertRequiresCmd) {
        var aa = (AssertRequiresCmd)assrt;
        cc = new CallCounterexample(cex.Trace, aa.Call, aa.Requires, cex.Model, cex.MvInfo, cex.Context, aa.Checksum);
      } else if (assrt is AssertEnsuresCmd && cex is ReturnCounterexample) {
        var aa = (AssertEnsuresCmd)assrt;
        var oldCex = (ReturnCounterexample)cex;
        // The first three parameters of ReturnCounterexample are: List<Block> trace, TransferCmd failingReturn, Ensures failingEnsures.
        // We have the "aa" version of failingEnsures, namely aa.Ensures.  The first two parameters take more work to reconstruct.
        // (The code here assumes the labels of blocks remain the same. If that's not the case, then it is possible that the trace
        // computed does not lead to where the error is, but at least the error will not be masked.)
        List<Block> reconstructedTrace = null;
        Block prevBlock = null;
        foreach (var blk in cex.Trace) {
          if (reconstructedTrace == null) {
            if (implEntryBlock.Label != blk.Label) {
              // labels have changed somehow; unable to reconstruct trace
              break;
            }
            reconstructedTrace = new List<Block>();
            reconstructedTrace.Add(implEntryBlock);
            prevBlock = implEntryBlock;
          } else if (prevBlock.TransferCmd is GotoCmd) {
            var gto = (GotoCmd)prevBlock.TransferCmd;
            Block nb = null;
            Contract.Assert(gto.labelNames.Count == gto.labelTargets.Count);  // follows from GotoCmd invariant and the fact that resolution should have made both lists non-null
            for (int i = 0; i < gto.labelNames.Count; i++) {
              if (gto.labelNames[i] == blk.Label) {
                nb = gto.labelTargets[i];
                break;
              }
            }
            if (nb == null) {
              // labels have changed somehow; unable to reconstruct trace
              reconstructedTrace = null;
              break;
            }
            reconstructedTrace.Add(nb);
            prevBlock = nb;
          } else {
            // old trace is longer somehow; unable to reconstruct trace
            reconstructedTrace = null;
            break;
          }
        }
        ReturnCmd returnCmd = null;
        if (reconstructedTrace != null) {
          // The reconstructed trace ends with a "return;" in the passive command, so we now try to convert it to the original (non-passive) "return;"
          foreach (Block b in reconstructedTrace) {
            Contract.Assert(b != null);
            Contract.Assume(b.TransferCmd != null);
            returnCmd = gotoCmdOrigins.ContainsKey(b.TransferCmd) ? gotoCmdOrigins[b.TransferCmd] : null;
            if (returnCmd != null) {
              break;
            }
          }
          if (returnCmd == null) {
            // As one last recourse, take the transfer command of the last block in the trace, if any
            returnCmd = reconstructedTrace.Last().TransferCmd as ReturnCmd;
          }
        }
        cc = new ReturnCounterexample(reconstructedTrace ?? cex.Trace, returnCmd ?? oldCex.FailingReturn, aa.Ensures, cex.Model, cex.MvInfo, cex.Context, aa.Checksum);
      } else {
        cc = new AssertCounterexample(cex.Trace, assrt, cex.Model, cex.MvInfo, cex.Context);
      }
      cc.relatedInformation = relatedInformation;
      return cc;
    }

    static VCExpr LetVC(Block startBlock,
                        VCExpr controlFlowVariableExpr,
                        Dictionary<int, Absy> label2absy,
                        ProverContext proverCtxt,
                        out int assertionCount) {
      Contract.Requires(startBlock != null);
      Contract.Requires(proverCtxt != null);

      Contract.Ensures(Contract.Result<VCExpr>() != null);

      Hashtable/*<Block, LetVariable!>*/ blockVariables = new Hashtable/*<Block, LetVariable!!>*/();
      List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
      VCExpr startCorrect = LetVC(startBlock, controlFlowVariableExpr, label2absy, blockVariables, bindings, proverCtxt, out assertionCount);
      return proverCtxt.ExprGen.Let(bindings, startCorrect);
    }

    static VCExpr LetVCIterative(List<Block> blocks,
                                 VCExpr controlFlowVariableExpr,
                                 Dictionary<int, Absy> label2absy,
                                 ProverContext proverCtxt,
                                 out int assertionCount,
                                 bool isPositiveContext = true)
    {
      Contract.Requires(blocks != null);
      Contract.Requires(proverCtxt != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      assertionCount = 0;

      Graph<Block> dag = new Graph<Block>();
      dag.AddSource(blocks[0]); 
      foreach (Block b in blocks) {
        GotoCmd gtc = b.TransferCmd as GotoCmd;
        if (gtc != null) {
          Contract.Assume(gtc.labelTargets != null);
          foreach (Block dest in gtc.labelTargets) {
            Contract.Assert(dest != null);
            dag.AddEdge(dest, b);
          }
        }
      }
      IEnumerable sortedNodes = dag.TopologicalSort();
      Contract.Assert(sortedNodes != null);

      Dictionary<Block, VCExprVar> blockVariables = new Dictionary<Block, VCExprVar>();
      List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
      VCExpressionGenerator gen = proverCtxt.ExprGen;
      Contract.Assert(gen != null);
      foreach (Block block in sortedNodes) {
        VCExpr SuccCorrect;
        GotoCmd gotocmd = block.TransferCmd as GotoCmd;
        if (gotocmd == null) {
          ReturnExprCmd re = block.TransferCmd as ReturnExprCmd;
          if (re == null) {
            SuccCorrect = VCExpressionGenerator.True;
          }
          else {
            SuccCorrect = proverCtxt.BoogieExprTranslator.Translate(re.Expr);
            if (isPositiveContext)
            {
                SuccCorrect = gen.Not(SuccCorrect);
            }
          }
        }
        else {
          Contract.Assert(gotocmd.labelTargets != null);
          List<VCExpr> SuccCorrectVars = new List<VCExpr>(gotocmd.labelTargets.Count);
          foreach (Block successor in gotocmd.labelTargets) {
            Contract.Assert(successor != null);
            VCExpr s = blockVariables[successor];
            if (controlFlowVariableExpr != null) {
              VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(controlFlowVariableExpr, gen.Integer(BigNum.FromInt(block.UniqueId)));
              VCExpr controlTransferExpr = gen.Eq(controlFlowFunctionAppl, gen.Integer(BigNum.FromInt(successor.UniqueId)));
              s = gen.Implies(controlTransferExpr, s);
            }
            SuccCorrectVars.Add(s);
          }
          SuccCorrect = gen.NAry(VCExpressionGenerator.AndOp, SuccCorrectVars);
        }

        VCContext context = new VCContext(label2absy, proverCtxt, controlFlowVariableExpr, isPositiveContext);
        VCExpr vc = Wlp.Block(block, SuccCorrect, context);
        assertionCount += context.AssertionCount;

        VCExprVar v = gen.Variable(block.Label + "_correct", Bpl.Type.Bool);
        bindings.Add(gen.LetBinding(v, vc));
        blockVariables.Add(block, v);
      }

      return proverCtxt.ExprGen.Let(bindings, blockVariables[blocks[0]]);
    }

    static VCExpr LetVC(Block block,
                        VCExpr controlFlowVariableExpr,
                        Dictionary<int, Absy> label2absy,
                        Hashtable/*<Block, VCExprVar!>*/ blockVariables,
                        List<VCExprLetBinding/*!*/>/*!*/ bindings,
                        ProverContext proverCtxt,
                        out int assertionCount)
    {
      Contract.Requires(block != null);
      Contract.Requires(blockVariables!= null);
      Contract.Requires(cce.NonNullElements(bindings));
      Contract.Requires(proverCtxt != null);

      Contract.Ensures(Contract.Result<VCExpr>() != null);

      assertionCount = 0;

      VCExpressionGenerator gen = proverCtxt.ExprGen;
      Contract.Assert(gen != null);
      VCExprVar v = (VCExprVar)blockVariables[block];
      if (v == null) {
        /*
         * For block A (= block), generate:
         *   LET_binding A_correct = wp(A_body, (/\ S \in Successors(A) :: S_correct))
         * with the side effect of adding the let bindings to "bindings" for any
         * successor not yet visited.
         */
        VCExpr SuccCorrect;
        GotoCmd gotocmd = block.TransferCmd as GotoCmd;
        if (gotocmd == null) {
          ReturnExprCmd re = block.TransferCmd as ReturnExprCmd;
          if (re == null) {
            SuccCorrect = VCExpressionGenerator.True;
          } else {
            SuccCorrect = proverCtxt.BoogieExprTranslator.Translate(re.Expr);
          }
        } else {
          Contract.Assert( gotocmd.labelTargets != null);
          List<VCExpr> SuccCorrectVars = new List<VCExpr>(gotocmd.labelTargets.Count);
          foreach (Block successor in gotocmd.labelTargets) {
            Contract.Assert(successor != null);
            int ac;
            VCExpr s = LetVC(successor, controlFlowVariableExpr, label2absy, blockVariables, bindings, proverCtxt, out ac);
            assertionCount += ac;
            if (controlFlowVariableExpr != null) 
            {
              VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(controlFlowVariableExpr, gen.Integer(BigNum.FromInt(block.UniqueId)));
              VCExpr controlTransferExpr = gen.Eq(controlFlowFunctionAppl, gen.Integer(BigNum.FromInt(successor.UniqueId)));
              s = gen.Implies(controlTransferExpr, s);
            }  
            SuccCorrectVars.Add(s);
          }
          SuccCorrect = gen.NAry(VCExpressionGenerator.AndOp, SuccCorrectVars);
        }

        
        VCContext context = new VCContext(label2absy, proverCtxt, controlFlowVariableExpr);
        VCExpr vc = Wlp.Block(block, SuccCorrect, context);
        assertionCount += context.AssertionCount;
        
        v = gen.Variable(block.Label + "_correct", Bpl.Type.Bool);
        bindings.Add(gen.LetBinding(v, vc));
        blockVariables.Add(block, v);
      }
      return v;
    }

    static VCExpr DagVC(Block block,
                         VCExpr controlFlowVariableExpr,
                         Dictionary<int, Absy> label2absy,
                         Hashtable/*<Block, VCExpr!>*/ blockEquations,
                         ProverContext proverCtxt,
                         out int assertionCount)
    {
      Contract.Requires(block != null);
      Contract.Requires(label2absy != null);
      Contract.Requires(blockEquations != null);
      Contract.Requires(proverCtxt != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      assertionCount = 0;
      VCExpressionGenerator gen = proverCtxt.ExprGen;
      Contract.Assert(gen != null);
      VCExpr vc = (VCExpr)blockEquations[block];
      if (vc != null) {
        return vc;
      }

      /* 
       * For block A (= block), generate:
       *   wp(A_body, (/\ S \in Successors(A) :: DagVC(S)))
       */
      VCExpr SuccCorrect = null;
      GotoCmd gotocmd = block.TransferCmd as GotoCmd;
      if (gotocmd != null)
      {
        foreach (Block successor in cce.NonNull(gotocmd.labelTargets)) {
          Contract.Assert(successor != null);
          int ac;
          VCExpr c = DagVC(successor, controlFlowVariableExpr, label2absy, blockEquations, proverCtxt, out ac);
          assertionCount += ac;
          if (controlFlowVariableExpr != null) {
            VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(controlFlowVariableExpr, gen.Integer(BigNum.FromInt(block.UniqueId)));
            VCExpr controlTransferExpr = gen.Eq(controlFlowFunctionAppl, gen.Integer(BigNum.FromInt(successor.UniqueId)));
            c = gen.Implies(controlTransferExpr, c);
          }  
          SuccCorrect = SuccCorrect == null ? c : gen.And(SuccCorrect, c);
        }
      }
      if (SuccCorrect == null) {
        SuccCorrect = VCExpressionGenerator.True;
      }

      VCContext context = new VCContext(label2absy, proverCtxt, controlFlowVariableExpr);
      vc = Wlp.Block(block, SuccCorrect, context);
      assertionCount += context.AssertionCount;
      
      //  gen.MarkAsSharedFormula(vc);  PR: don't know yet what to do with this guy

      blockEquations.Add(block, vc);
      return vc;
    }

    static VCExpr FlatBlockVC(Implementation impl,
                              Dictionary<int, Absy> label2absy,
                              bool local, bool reach, bool doomed,
                              ProverContext proverCtxt,
                              out int assertionCount)
    {
      Contract.Requires(impl != null);
      Contract.Requires(label2absy != null);
      Contract.Requires(proverCtxt != null);
      Contract.Requires( !local || !reach);  // "reach" must be false for local
    
      VCExpressionGenerator gen = proverCtxt.ExprGen;
      Contract.Assert(gen != null);
      Hashtable/* Block --> VCExprVar */ BlkCorrect = BlockVariableMap(impl.Blocks, "_correct", gen);
      Hashtable/* Block --> VCExprVar */ BlkReached = reach ? BlockVariableMap(impl.Blocks, "_reached", gen) : null;

      List<Block> blocks = impl.Blocks;
      Contract.Assert(blocks != null);
  // block sorting is now done on the VCExpr
  //    if (!local && (cce.NonNull(CommandLineOptions.Clo.TheProverFactory).NeedsBlockSorting) {
  //      blocks = SortBlocks(blocks);
  //    }

      VCExpr proofObligation;
      if (!local) {
        proofObligation = cce.NonNull((VCExprVar)BlkCorrect[impl.Blocks[0]]);
      } else {
        List<VCExpr> conjuncts = new List<VCExpr>(blocks.Count);
        foreach (Block b in blocks) {Contract.Assert(b != null);
          VCExpr v = cce.NonNull((VCExprVar)BlkCorrect[b]);
          conjuncts.Add(v);
        }
        proofObligation = gen.NAry(VCExpressionGenerator.AndOp, conjuncts);
      }

      VCContext context = new VCContext(label2absy, proverCtxt);
      Contract.Assert(context != null);

      List<VCExprLetBinding> programSemantics = new List<VCExprLetBinding>(blocks.Count);
      foreach (Block b in blocks) {Contract.Assert(b != null);
        /* 
         * In block mode,
         * For a return block A, generate:
         *   A_correct <== wp(A_body, true)  [post-condition has been translated into an assert]
         * For all other blocks, generate:
         *   A_correct <== wp(A_body, (/\ S \in Successors(A) :: S_correct))
         * 
         * In doomed mode, proceed as in block mode, except for a return block A, generate:
         *   A_correct <== wp(A_body, false)  [post-condition has been translated into an assert]
         *
         * In block reach mode, the wp(A_body,...) in the equations above change to:
         *   A_reached ==> wp(A_body,...)
         * and the conjunction above changes to:
         *   (/\ S \in Successors(A) :: S_correct \/ (\/ T \in Successors(A) && T != S :: T_reached))
         *
         * In local mode, generate:
         *   A_correct <== wp(A_body, true)
         */
        VCExpr SuccCorrect;
        if (local) {
          SuccCorrect = VCExpressionGenerator.True;
        } else {
          SuccCorrect = SuccessorsCorrect(b, BlkCorrect, BlkReached, doomed, gen);
        }

        VCExpr wlp = Wlp.Block(b, SuccCorrect, context);
        if (BlkReached != null) {
          wlp = gen.Implies(cce.NonNull((VCExprVar)BlkReached[b]), wlp);
        }
        
        VCExprVar okVar = cce.NonNull((VCExprVar)BlkCorrect[b]);
        VCExprLetBinding binding = gen.LetBinding(okVar, wlp);
        programSemantics.Add(binding);
      }

      assertionCount = context.AssertionCount;
      return gen.Let(programSemantics, proofObligation);
    }

    private static Hashtable/* Block --> VCExprVar */ BlockVariableMap(List<Block/*!*/>/*!*/ blocks, string suffix,
                                                                        Microsoft.Boogie.VCExpressionGenerator gen) {
      Contract.Requires(cce.NonNullElements(blocks));
      Contract.Requires(suffix != null);
      Contract.Requires(gen != null);
      Contract.Ensures(Contract.Result<Hashtable>() != null);

      Hashtable/* Block --> VCExprVar */ map = new Hashtable/* Block --> (Let)Variable */();
      foreach (Block b in blocks) {
        Contract.Assert(b != null);
        VCExprVar v = gen.Variable(b.Label + suffix, Bpl.Type.Bool);
        Contract.Assert(v != null);
        map.Add(b, v);
      }
      return map;
    }

    private static VCExpr SuccessorsCorrect(
        Block b,
        Hashtable/* Block --> VCExprVar */ BlkCorrect,
        Hashtable/* Block --> VCExprVar */ BlkReached,
        bool doomed,
        Microsoft.Boogie.VCExpressionGenerator gen) {
      Contract.Requires(b != null);
      Contract.Requires(BlkCorrect != null);
      Contract.Requires(gen != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      VCExpr SuccCorrect = null;
      GotoCmd gotocmd = b.TransferCmd as GotoCmd;
      if (gotocmd != null) {
        foreach (Block successor in cce.NonNull(gotocmd.labelTargets)) {
          Contract.Assert(successor != null);
          // c := S_correct
          VCExpr c = (VCExprVar)BlkCorrect[successor];
          Contract.Assert(c != null);
          if (BlkReached != null) {
            // c := S_correct \/ Sibling0_reached \/ Sibling1_reached \/ ...;
            foreach (Block successorSibling in gotocmd.labelTargets) {
              Contract.Assert(successorSibling != null);
              if (successorSibling != successor) {
                c = gen.Or(c, cce.NonNull((VCExprVar)BlkReached[successorSibling]));
              }
            }
          }
          SuccCorrect = SuccCorrect == null ? c : gen.And(SuccCorrect, c);
        }
      }
      if (SuccCorrect == null) {
        return VCExpressionGenerator.True;
      } else if (doomed) {
        return VCExpressionGenerator.False;
      } else {
        return SuccCorrect;
      }
    }

    static VCExpr NestedBlockVC(Implementation impl,
                                Dictionary<int, Absy> label2absy,
                                bool reach,
                                ProverContext proverCtxt,
                                out int assertionCount){
      Contract.Requires(impl != null);
      Contract.Requires(label2absy != null);
      Contract.Requires(proverCtxt != null);
      Contract.Requires( impl.Blocks.Count != 0);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      VCExpressionGenerator gen = proverCtxt.ExprGen;
      Contract.Assert(gen != null);
      Graph<Block> g = Program.GraphFromImpl(impl);

      Hashtable/* Block --> VCExprVar */ BlkCorrect = BlockVariableMap(impl.Blocks, "_correct", gen);
      Hashtable/* Block --> VCExprVar */ BlkReached = reach ? BlockVariableMap(impl.Blocks, "_reached", gen) : null;

      Block startBlock = cce.NonNull( impl.Blocks[0]);
      VCExpr proofObligation = (VCExprVar)BlkCorrect[startBlock];
      Contract.Assert(proofObligation != null);
      VCContext context = new VCContext(label2absy, proverCtxt);
      
      Hashtable/*Block->int*/ totalOrder = new Hashtable/*Block->int*/();
      {
        List<Block> blocks = impl.Blocks;
        
        // block sorting is now done on the VCExpr
        //   if (((!)CommandLineOptions.Clo.TheProverFactory).NeedsBlockSorting) {
        //     blocks = SortBlocks(blocks);
        //   }
        int i = 0;
        foreach (Block b in blocks) {
          Contract.Assert(b != null);
          totalOrder[b] = i;
          i++;
        }
      }
      
      VCExprLetBinding programSemantics = NestedBlockEquation(cce.NonNull(impl.Blocks[0]), BlkCorrect, BlkReached, totalOrder, context, g, gen);
      List<VCExprLetBinding> ps = new List<VCExprLetBinding>(1);
      ps.Add(programSemantics);

      assertionCount = context.AssertionCount;
      return gen.Let(ps, proofObligation);
    }

    private static VCExprLetBinding NestedBlockEquation(Block b,
        Hashtable/*Block-->VCExprVar*/ BlkCorrect,
        Hashtable/*Block-->VCExprVar*/ BlkReached,
        Hashtable/*Block->int*/ totalOrder,
        VCContext context,
        Graph<Block> g,
        Microsoft.Boogie.VCExpressionGenerator gen) {
      Contract.Requires(b != null);
      Contract.Requires(BlkCorrect != null);
      Contract.Requires(totalOrder != null);
      Contract.Requires(g != null);
      Contract.Requires(context != null);

      Contract.Ensures(Contract.Result<VCExprLetBinding>() != null);

      /*
      * For a block b, return:
      *   LET_BINDING b_correct = wp(b_body, X)
      * where X is:
      *   LET (THOSE d \in DirectDominates(b) :: BlockEquation(d))
      *   IN (/\ s \in Successors(b) :: s_correct)
      * 
      * When the VC-expression generator does not support LET expresions, this
      * will eventually turn into:
      *   b_correct <== wp(b_body, X)
      * where X is:
      *   (/\ s \in Successors(b) :: s_correct)
      *   <==
      *   (/\ d \in DirectDominatees(b) :: BlockEquation(d))
      *
      * In both cases above, if BlkReached is non-null, then the wp expression
      * is instead:
      *   b_reached ==> wp(b_body, X)
      */

      VCExpr SuccCorrect = SuccessorsCorrect(b, BlkCorrect, null, false, gen);
      Contract.Assert(SuccCorrect != null);

      List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
      foreach (Block dominee in GetSortedBlocksImmediatelyDominatedBy(g, b, totalOrder)) {
        Contract.Assert(dominee != null);
        VCExprLetBinding c = NestedBlockEquation(dominee, BlkCorrect, BlkReached, totalOrder, context, g, gen);
        bindings.Add(c);
      }

      VCExpr X = gen.Let(bindings, SuccCorrect);
      VCExpr wlp = Wlp.Block(b, X, context);
      if (BlkReached != null) {
        wlp = gen.Implies((VCExprVar)BlkReached[b], wlp);
        Contract.Assert(wlp != null);
      }
      VCExprVar okVar = cce.NonNull((VCExprVar)BlkCorrect[b]);
      return gen.LetBinding(okVar, wlp);
    }

    /// <summary>
    /// Returns a list of g.ImmediatelyDominatedBy(b), but in a sorted order, hoping to steer around
    /// the nondeterminism problems we've been seeing by using just this call.
    /// </summary>
    static List<Block/*!*/>/*!*/ GetSortedBlocksImmediatelyDominatedBy(Graph<Block>/*!*/ g, Block/*!*/ b, Hashtable/*Block->int*//*!*/ totalOrder) {
      Contract.Requires(g != null);
      Contract.Requires(b != null);
      Contract.Requires(totalOrder != null);
      Contract.Ensures(Contract.Result<List<Block>>() != null);

      List<Block> list = new List<Block>();
      foreach (Block dominee in g.ImmediatelyDominatedBy(b)) {
        Contract.Assert(dominee != null);
        list.Add(dominee);
      }
      list.Sort(new Comparison<Block>(delegate(Block x, Block y) {
        return (int)cce.NonNull(totalOrder[x]) - (int)cce.NonNull(totalOrder[y]);
      }));
      return list;
    }

    static VCExpr VCViaStructuredProgram
                  (Implementation impl, Dictionary<int, Absy> label2absy,
                   ProverContext proverCtxt,
                   out int assertionCount)
    {
      Contract.Requires(impl != null);
      Contract.Requires(label2absy != null);
      Contract.Requires(proverCtxt != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      #region Convert block structure back to a "regular expression"
      RE r = DAG2RE.Transform(cce.NonNull(impl.Blocks[0]));
      Contract.Assert(r != null);
      #endregion

      VCContext ctxt = new VCContext(label2absy, proverCtxt);
      Contract.Assert(ctxt != null);
      #region Send wlp(program,true) to Simplify
      var vcexp = Wlp.RegExpr(r, VCExpressionGenerator.True, ctxt);
      assertionCount = ctxt.AssertionCount;
      return vcexp;
      #endregion
    }

    /// <summary> 
    /// Remove empty blocks reachable from the startBlock of the CFG
    /// </summary>
    static void RemoveEmptyBlocksIterative(List<Block> blocks) {
      // postorder traversal of cfg
      //   noting loop heads in [keep] and
      //   generating token information in [renameInfo]
      Block startBlock = blocks[0];
      var postorder = new List<Block>();
      var keep = new HashSet<Block>();
      var visited = new HashSet<Block>();
      var grey = new HashSet<Block>();
      var stack = new Stack<Block>();
      Dictionary<Block, Block> renameInfo = new Dictionary<Block, Block>();

      stack.Push(startBlock);
      visited.Add(startBlock);
      while (stack.Count != 0) {
        var curr = stack.Pop();
        if (grey.Contains(curr)) {
          postorder.Add(curr);

          // generate renameInfoForStartBlock
          GotoCmd gtc = curr.TransferCmd as GotoCmd;
          renameInfo[curr] = null;
          if (gtc == null || gtc.labelTargets == null || gtc.labelTargets.Count == 0) {
            if (curr.Cmds.Count == 0 && curr.tok.IsValid) {
              renameInfo[curr] = curr;
            }
          } else {
            if (curr.Cmds.Count == 0 || curr == startBlock) {
              if (curr.tok.IsValid) {
                renameInfo[curr] = curr;
              } else {
                HashSet<Block> successorRenameInfo = new HashSet<Block>();
                foreach (Block s in gtc.labelTargets) {
                  if (keep.Contains(s)) {
                    successorRenameInfo.Add(null);
                  } else {
                    successorRenameInfo.Add(renameInfo[s]);
                  }
                }
                if (successorRenameInfo.Count == 1) {
                  renameInfo[curr] = successorRenameInfo.Single();
                }
              }
            }
          }
          // end generate renameInfoForStartBlock

        } else {
          grey.Add(curr);
          stack.Push(curr);
          GotoCmd gtc = curr.TransferCmd as GotoCmd;
          if (gtc == null || gtc.labelTargets == null || gtc.labelTargets.Count == 0) continue;
          foreach (Block s in gtc.labelTargets) {
            if (!visited.Contains(s)) {
              visited.Add(s);
              stack.Push(s);
            } else if (grey.Contains(s) && !postorder.Contains(s)) { // s is a loop head
              keep.Add(s);
            }
          }
        }
      }
      keep.Add(startBlock);

      foreach (Block b in postorder) {
        if (!keep.Contains(b) && b.Cmds.Count == 0) {
          GotoCmd bGtc = b.TransferCmd as GotoCmd;
          foreach (Block p in b.Predecessors) {
            GotoCmd pGtc = p.TransferCmd as GotoCmd;
            Contract.Assert(pGtc != null);
            pGtc.labelTargets.Remove(b);
            pGtc.labelNames.Remove(b.Label);
          }
          if (bGtc == null || bGtc.labelTargets == null || bGtc.labelTargets.Count == 0) {
            continue;
          }

          List<Block> successors = bGtc.labelTargets;

          // Try to push token information if possible
          if (b.tok.IsValid && successors.Count == 1 && b != renameInfo[startBlock]) {
            var s = successors.Single();
            if (!s.tok.IsValid) {
              foreach (Block p in s.Predecessors) {
                if (p != b) {
                  GotoCmd pGtc = p.TransferCmd as GotoCmd;
                  Contract.Assert(pGtc != null);
                  pGtc.labelTargets.Remove(s);
                  pGtc.labelNames.Remove(s.Label);
                  pGtc.labelTargets.Add(s);
                  pGtc.labelNames.Add(b.Label);
                }
              }
              s.tok = b.tok;
              s.Label = b.Label;
            }
          }

          foreach (Block p in b.Predecessors) {
            GotoCmd pGtc = p.TransferCmd as GotoCmd;
            Contract.Assert(pGtc != null);
            foreach (Block s in successors) {
              if (!pGtc.labelTargets.Contains(s)) {
                pGtc.labelTargets.Add(s);
                pGtc.labelNames.Add(s.Label);
              }
            }
          }
        }
      }

      if (!startBlock.tok.IsValid && startBlock.Cmds.All(c => c is AssumeCmd)) {
        if (renameInfo[startBlock] != null) {
          startBlock.tok = renameInfo[startBlock].tok;
          startBlock.Label = renameInfo[startBlock].Label;
        }
      }

    }

    /// <summary> 
    /// Remove the empty blocks reachable from the block.
    /// It changes the visiting state of the blocks, so that if you want to visit again the blocks, you have to reset them...
    /// </summary>
    static List<Block> RemoveEmptyBlocks(Block b) {
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<List<Block>>() != null);

      Contract.Assert(b.TraversingStatus == Block.VisitState.ToVisit);
      Block renameInfo;
      List<Block> retVal = removeEmptyBlocksWorker(b, true, out renameInfo);
      if (renameInfo != null && !b.tok.IsValid) {
        bool onlyAssumes = true;
        foreach (Cmd c in b.Cmds) {
          if (!(c is AssumeCmd)) {
            onlyAssumes = false;
            break;
          }
        }
        if (onlyAssumes) {
          b.tok = renameInfo.tok;
          b.Label = renameInfo.Label;
        }
      }
      return retVal;
    }

    /// <summary>
    /// For every not-yet-visited block n reachable from b, change n's successors to skip empty nodes.
    /// Return the *set* of blocks reachable from b without passing through a nonempty block.
    /// The target of any backedge is counted as a nonempty block.
    /// If renameInfoForStartBlock is non-null, it denotes an empty block with location information, and that
    /// information would be appropriate to display
    /// </summary>
    private static List<Block> removeEmptyBlocksWorker(Block b, bool startNode, out Block renameInfoForStartBlock)
  {
      Contract.Requires(b != null);
      Contract.Ensures(Contract.ValueAtReturn(out renameInfoForStartBlock) == null || Contract.ValueAtReturn(out renameInfoForStartBlock).tok.IsValid);
      // ensures: b in result ==> renameInfoForStartBlock == null;
    
      renameInfoForStartBlock = null;
      List<Block> bs = new List<Block>();
      GotoCmd gtc = b.TransferCmd as GotoCmd;

      // b has no successors
      if (gtc == null || gtc.labelTargets == null || gtc.labelTargets.Count == 0) 
      {
        if (b.Cmds.Count != 0){ // only empty blocks are removed...
          bs.Add(b);
        } else if (b.tok.IsValid) {
          renameInfoForStartBlock = b;
        }
        return bs;
      }
      else if (b.TraversingStatus == Block.VisitState.ToVisit)  // if b has some successors and we have not seen it so far...
      { 
        b.TraversingStatus = Block.VisitState.BeingVisited;

        // Before recursing down to successors, make a sobering observation:
        // If b has no commands and is not the start node, then it will see
        // extinction (because it will not be included in the "return setOfSuccessors"
        // statement below).  In that case, if b has a location, then the location
        // information would be lost.  Hence, make an attempt to save the location
        // by pushing the location onto b's successor.  This can be done if (0) b has
        // exactly one successor, (1) that successor has no location of its own, and
        // (2) that successor has no other predecessors.
        if (b.Cmds.Count == 0 && !startNode) {
          // b is about to become extinct; try to save its name and location, if possible
          if (b.tok.IsValid && gtc.labelTargets.Count == 1) {
            Block succ = cce.NonNull(gtc.labelTargets[0]);
            if (!succ.tok.IsValid && succ.Predecessors.Count == 1) {
              succ.tok = b.tok;
              succ.Label = b.Label;
            }
          }
        }

        // recursively call this method on each successor
        // merge result into a *set* of blocks
        HashSet<Block> mergedSuccessors = new HashSet<Block>();
        int m = 0;  // in the following loop, set renameInfoForStartBlock to the value that all recursive calls agree on, if possible; otherwise, null
        foreach (Block dest in gtc.labelTargets){Contract.Assert(dest != null);
          Block renameInfo;
          List<Block> ys = removeEmptyBlocksWorker(dest, false, out renameInfo);
          Contract.Assert(ys != null);
          if (m == 0) {
            renameInfoForStartBlock = renameInfo;
          } else if (renameInfoForStartBlock != renameInfo) {
            renameInfoForStartBlock = null;
          }
          foreach (Block successor in ys){
            if (!mergedSuccessors.Contains(successor))
              mergedSuccessors.Add(successor);
          }
          m++;
        }
        b.TraversingStatus = Block.VisitState.AlreadyVisited;

        List<Block> setOfSuccessors = new List<Block>();
        foreach (Block d in mergedSuccessors)
          setOfSuccessors.Add(d);
        if (b.Cmds.Count == 0 && !startNode) {
          // b is about to become extinct
          if (b.tok.IsValid) {
            renameInfoForStartBlock = b;
          }
          return setOfSuccessors;
        }
        // otherwise, update the list of successors of b to be the blocks in setOfSuccessors
        gtc.labelTargets = setOfSuccessors;
        gtc.labelNames = new List<String>();
        foreach (Block d in setOfSuccessors){
          Contract.Assert(d != null);
          gtc.labelNames.Add(d.Label);}
        if (!startNode) {
          renameInfoForStartBlock = null;
        }
        return new List<Block> { b };
      }
      else // b has some successors, but we are already visiting it, or we have already visited it...
      {
        return new List<Block> { b };
      }
    }

    static void DumpMap(Hashtable /*Variable->Expr*/ map) {
      Contract.Requires(map != null);
      foreach (DictionaryEntry de in map) {
        Variable v = (Variable)de.Key;
        Contract.Assert(v != null);
        Expr e = (Expr)de.Value;
        Contract.Assert(e != null);
        Console.Write("  ");
        v.Emit(new TokenTextWriter("<console>", Console.Out, /*setTokens=*/ false, /*pretty=*/ false), 0);
        Console.Write("  --> ");
        e.Emit(new TokenTextWriter("<console>", Console.Out, /*setTokens=*/ false, /*pretty=*/ false));
        Console.WriteLine();
      }
    }
  }
}
