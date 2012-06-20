//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;
using System.IO;
using Microsoft.Boogie;
using Graphing;
using AI = Microsoft.AbstractInterpretationFramework;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC {
  using Bpl = Microsoft.Boogie;

  public class VCGen : ConditionGeneration {
      private const bool _print_time = false;
    /// <summary>
    /// Constructor.  Initializes the theorem prover.
    /// </summary>
    [NotDelayed]
    public VCGen(Program program, string/*?*/ logFilePath, bool appendLogFile)
      : base(program)
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
        Contract.Invariant(program != null);
        Contract.Invariant(cce.NonNullDictionaryAndValues(copies));
        Contract.Invariant(cce.NonNull(visited));
        Contract.Invariant(callback != null);
      }

      VCGen parent;
      Implementation impl;
      Block initial;
      Program program;
      int id;
      Dictionary<Block, Block> copies = new Dictionary<Block, Block>();
      HashSet<Block> visited = new HashSet<Block>();
      VerifierCallback callback;

      internal SmokeTester(VCGen par, Implementation i, Program prog, VerifierCallback callback) {
        Contract.Requires(par != null);
        Contract.Requires(i != null);
        Contract.Requires(prog != null);
        Contract.Requires(callback != null);
        parent = par;
        impl = i;
        initial = i.Blocks[0];
        program = prog;
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
        Block res = new Block(b.tok, b.Label, new CmdSeq(b.Cmds), null);
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
        CmdSeq seq = new CmdSeq();
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
            GotoCmd copy = new GotoCmd(go.tok, new StringSeq(), new BlockSeq());
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

      bool CheckUnreachable(Block cur, CmdSeq seq) {
        Contract.Requires(cur != null);
        Contract.Requires(seq != null);
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        foreach (Cmd cmd in seq) {
          AssertCmd assrt = cmd as AssertCmd;
          if (assrt != null && QKeyValue.FindBoolAttribute(assrt.Attributes, "PossiblyUnreachable"))
            return false;
        }

        DateTime start = DateTime.UtcNow;
        if (CommandLineOptions.Clo.Trace) {
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
        if (CommandLineOptions.Clo.TraceVerify) {
          System.Console.WriteLine();
          System.Console.WriteLine(" --- smoke #{0}, before passify", id);
          Emit();
        }
        parent.CurrentLocalVariables = impl.LocVars;
        ModelViewInfo mvInfo;
        parent.PassifyImpl(impl, out mvInfo);
        Hashtable label2Absy;
        Checker ch = parent.FindCheckerFor(impl, CommandLineOptions.Clo.SmokeTimeout);
        Contract.Assert(ch != null);

        var exprGen = ch.TheoremProver.Context.ExprGen;
        VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : exprGen.Integer(BigNum.ZERO);

        VCExpr vc = parent.GenerateVC(impl, controlFlowVariableExpr, out label2Absy, ch.TheoremProver.Context);
        Contract.Assert(vc != null);

        if (!CommandLineOptions.Clo.UseLabels) {
          VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
          VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
          vc = exprGen.Implies(eqExpr, vc);
        }

        impl.Blocks = backup;

        if (CommandLineOptions.Clo.TraceVerify) {
          System.Console.WriteLine(" --- smoke #{0}, after passify", id);
          Emit();
        }
        ch.BeginCheck(cce.NonNull(impl.Name + "_smoke" + id++), vc, new ErrorHandler(label2Absy, this.callback));
        ch.ProverDone.WaitOne();
        ProverInterface.Outcome outcome = ch.ReadOutcome();
        parent.CurrentLocalVariables = null;

        DateTime end = DateTime.UtcNow;
        TimeSpan elapsed = end - start;
        if (CommandLineOptions.Clo.Trace) {
          System.Console.WriteLine("  [{0} s] {1}", elapsed.TotalSeconds,
            outcome == ProverInterface.Outcome.Valid ? "OOPS" :
              "OK" + (outcome == ProverInterface.Outcome.Invalid ? "" : " (" + outcome + ")"));
        }

        if (outcome == ProverInterface.Outcome.Valid) {
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

        CmdSeq seq = new CmdSeq();
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

        Contract.Assume(!(go != null && go.labelTargets == null && go.labelNames != null && go.labelNames.Length > 0));

        if (ret != null || (go != null && cce.NonNull(go.labelTargets).Length == 0)) {
          // we end in return, so there will be no more places to check
          CheckUnreachable(cur, seq);
        } else if (go != null) {
          bool needToCheck = true;
          // if all of our children have more than one parent, then
          // we're in the right place to check
          foreach (Block target in cce.NonNull(go.labelTargets)) {
            Contract.Assert(target != null);
            if (target.Predecessors.Length == 1) {
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
        Hashtable label2Absy;
        VerifierCallback callback;
        [ContractInvariantMethod]
        void ObjectInvariant() {
          Contract.Invariant(label2Absy != null);
          Contract.Invariant(callback != null);
        }


        public ErrorHandler(Hashtable label2Absy, VerifierCallback callback) {
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
      static int current_id;
      Block split_block;
      bool assert_to_assume;
      List<Block/*!*/>/*!*/ assumized_branches = new List<Block/*!*/>();

      double score;
      bool score_computed;
      double total_cost;
      int assertion_count;
      double assertion_cost; // without multiplication by paths
      Hashtable/*TransferCmd->ReturnCmd*//*!*/ gotoCmdOrigins;
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

      public Split(List<Block/*!*/>/*!*/ blocks, Hashtable/*TransferCmd->ReturnCmd*//*!*/ gotoCmdOrigins, VCGen/*!*/ par, Implementation/*!*/ impl) {
        Contract.Requires(cce.NonNullElements(blocks));
        Contract.Requires(gotoCmdOrigins != null);
        Contract.Requires(par != null);
        Contract.Requires(impl != null);
        this.blocks = blocks;
        this.gotoCmdOrigins = gotoCmdOrigins;
        this.parent = par;
        this.impl = impl;
        this.id = current_id++;
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
          impl.Emit(new TokenTextWriter(filename, sw, false), 0);
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
          if (next.Predecessors.Length > 1 || se.virtual_successors.Count != 1)
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
          BlockSeq targ = cce.NonNull(gt.labelTargets);
          if (targ.Length < 2)
            continue;
          // caution, we only consider two first exits

          double left0, right0, left1, right1;
          split_block = b;

          assumized_branches.Clear();
          assumized_branches.Add(cce.NonNull(targ[0]));
          left0 = DoComputeScore(true);
          right0 = DoComputeScore(false);

          assumized_branches.Clear();
          for (int idx = 1; idx < targ.Length; idx++) {
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

      CmdSeq SliceCmds(Block b) {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<CmdSeq>() != null);

        CmdSeq seq = b.Cmds;
        Contract.Assert(seq != null);
        if (!doing_slice && !ShouldAssumize(b))
          return seq;
        CmdSeq res = new CmdSeq();
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
          GotoCmd newGoto = new GotoCmd(gt.tok, new StringSeq(), new BlockSeq());
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
        Hashtable newGotoCmdOrigins = new Hashtable();
        foreach (Block b in blocks) {
          Contract.Assert(b != null);
          Block tmp;
          if (copies.TryGetValue(b, out tmp)) {
            newBlocks.Add(cce.NonNull(tmp));
            if (gotoCmdOrigins.ContainsKey(b)) {
              newGotoCmdOrigins[tmp] = gotoCmdOrigins[b];
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

        BlockSeq trace = new BlockSeq();
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
              best.SoundnessCheck(new HashSet<PureCollections.Tuple>(), best.blocks[0], ss);
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

      public Checker Checker {
        get {
          Contract.Ensures(Contract.Result<Checker>() != null);

          Contract.Assert(checker != null);
          return checker;
        }
      }

      public WaitHandle ProverDone {
        get {
          Contract.Assert(checker != null);
          return checker.ProverDone;
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
      public void BeginCheck(VerifierCallback callback, ModelViewInfo mvInfo, int no, int timeout) {
        Contract.Requires(callback != null);
        splitNo = no;

        impl.Blocks = blocks;

        checker = parent.FindCheckerFor(impl, timeout);
        Hashtable/*<int, Absy!>*/ label2absy = new Hashtable/*<int, Absy!>*/();

        ProverInterface tp = checker.TheoremProver;
        ProverContext ctx = tp.Context;
        Boogie2VCExprTranslator bet = ctx.BoogieExprTranslator;
        bet.SetCodeExprConverter(
          new CodeExprConverter(
          delegate (CodeExpr codeExpr, Hashtable/*<Block, VCExprVar!>*/ blockVariables, List<VCExprLetBinding/*!*/> bindings) {
            VCGen vcgen = new VCGen(new Program(), null, false);
            vcgen.variable2SequenceNumber = new Hashtable/*Variable -> int*/();
            vcgen.incarnationOriginMap = new Dictionary<Incarnation, Absy>();
            vcgen.CurrentLocalVariables = codeExpr.LocVars;
            // codeExpr.Blocks.PruneUnreachableBlocks();  // This is needed for VCVariety.BlockNested, and is otherwise just an optimization

            ResetPredecessors(codeExpr.Blocks);
            vcgen.AddBlocksBetween(codeExpr.Blocks);
            Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = vcgen.ConvertBlocks2PassiveCmd(codeExpr.Blocks, new IdentifierExprSeq(), new ModelViewInfo(codeExpr));
            int ac;  // computed, but then ignored for this CodeExpr
            VCExpr startCorrect = VCGen.LetVC(codeExpr.Blocks[0], null, label2absy, blockVariables, bindings, ctx, out ac);
            VCExpr vce = ctx.ExprGen.Let(bindings, startCorrect);

            if (vcgen.CurrentLocalVariables.Length != 0) {
              Boogie2VCExprTranslator translator = checker.TheoremProver.Context.BoogieExprTranslator;
              List<VCExprVar> boundVars = new List<VCExprVar>();
              foreach (Variable v in vcgen.CurrentLocalVariables) {
                Contract.Assert(v != null);
                VCExprVar ev = translator.LookupVariable(v);
                Contract.Assert(ev != null);
                boundVars.Add(ev);
                if (v.TypedIdent.Type.Equals(Bpl.Type.Bool)) {
                  // add an antecedent (tickleBool ev) to help the prover find a possible trigger
                  vce = checker.VCExprGen.Implies(checker.VCExprGen.Function(VCExpressionGenerator.TickleBoolOp, ev), vce);
                }
              }
              vce = checker.VCExprGen.Forall(boundVars, new List<VCTrigger>(), vce);
            }
            return vce;
          }
		  ));

        var exprGen = ctx.ExprGen;
        VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : exprGen.Integer(BigNum.ZERO);

        VCExpr vc = parent.GenerateVCAux(impl, controlFlowVariableExpr, label2absy, checker.TheoremProver.Context);
        Contract.Assert(vc != null);

        if (!CommandLineOptions.Clo.UseLabels) {
          VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
          VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
          vc = exprGen.Implies(eqExpr, vc);
        }
        
        if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local) {
          reporter = new ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, parent.incarnationOriginMap, callback, mvInfo, cce.NonNull(this.Checker.TheoremProver.Context), parent.program);
        } else {
          reporter = new ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, parent.incarnationOriginMap, callback, mvInfo, this.Checker.TheoremProver.Context, parent.program);
        }

        if (CommandLineOptions.Clo.TraceVerify && no >= 0) {
          Console.WriteLine("-- after split #{0}", no);
          Print();
        }

        string desc = cce.NonNull(impl.Name);
        if (no >= 0)
          desc += "_split" + no;
        checker.BeginCheck(desc, vc, reporter);
      }

      private void SoundnessCheck(HashSet<PureCollections.Tuple/*!*/>/*!*/ cache, Block/*!*/ orig, List<Block/*!*/>/*!*/ copies) {
        Contract.Requires(cce.NonNull(cache));
        Contract.Requires(orig != null);
        Contract.Requires(copies != null);
        {
          PureCollections.Tuple t = new PureCollections.Tuple(new PureCollections.Capacity(1 + copies.Count));
          int i = 0;
          t[i++] = orig;
          foreach (Block b in copies) {
            Contract.Assert(b != null);
            t[i++] = b;
          }
          if (cache.Contains(t)) {
            return;
          }
          cache.Add(t);
        }

        for (int i = 0; i < orig.Cmds.Length; ++i) {
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

    public VCExpr GenerateVC(Implementation/*!*/ impl, VCExpr controlFlowVariableExpr, out Hashtable/*<int, Absy!>*//*!*/ label2absy, ProverContext proverContext)
    {
      Contract.Requires(impl != null);
      Contract.Requires(proverContext != null);
      Contract.Ensures(Contract.ValueAtReturn(out label2absy) != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      label2absy = new Hashtable/*<int, Absy!>*/();
      return GenerateVCAux(impl, controlFlowVariableExpr, label2absy, proverContext);
    }

    protected VCExpr GenerateVCAux(Implementation/*!*/ impl, VCExpr controlFlowVariableExpr, Hashtable/*<int, Absy!>*//*!*/ label2absy, ProverContext proverContext) {
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
          if (cce.NonNull(CommandLineOptions.Clo.TheProverFactory).SupportsDags) {
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
      if (_print_time)
      {
          Console.WriteLine("Checking function {0}", impl.Name);
          watch.Reset();
          watch.Start();
      }

      ConvertCFG2DAG(impl);

      SmokeTester smoke_tester = null;
      if (CommandLineOptions.Clo.SoundnessSmokeTest) {
        smoke_tester = new SmokeTester(this, impl, program, callback);
        smoke_tester.Copy();
      }

      ModelViewInfo mvInfo;
      Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = PassifyImpl(impl, out mvInfo);

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

      int cores = CommandLineOptions.Clo.VcsCores;
      Stack<Split> work = new Stack<Split>();
      List<Split> currently_running = new List<Split>();
      ResetPredecessors(impl.Blocks);
      work.Push(new Split(impl.Blocks, gotoCmdOrigins, this, impl));

      bool keep_going = max_kg_splits > 1;
      int total = 0;
      int no = max_splits == 1 && !keep_going ? -1 : 0;
      bool first_round = true;
      bool do_splitting = keep_going || max_splits > 1;
      double remaining_cost = 0.0, proven_cost = 0.0;

      if (do_splitting) {
        remaining_cost = work.Peek().Cost;
      }

      while (work.Count > 0 || currently_running.Count > 0) {
        bool prover_failed = false;
        Split s;

        if (work.Count > 0 && currently_running.Count < cores) {
          s = work.Pop();

          if (first_round && max_splits > 1) {
            prover_failed = true;
            remaining_cost -= s.Cost;
          } else {
            if (CommandLineOptions.Clo.Trace && no >= 0) {
              System.Console.WriteLine("    checking split {1}/{2}, {3:0.00}%, {0} ...", 
                                   s.Stats, no + 1, total, 100 * proven_cost / (proven_cost + remaining_cost));
            }
            callback.OnProgress("VCprove", no < 0 ? 0 : no, total, proven_cost / (remaining_cost + proven_cost));

            Contract.Assert(s.parent == this);
            s.BeginCheck(callback, mvInfo, no, 
              (keep_going && s.LastChance) ? CommandLineOptions.Clo.VcsFinalAssertTimeout :
                keep_going ? CommandLineOptions.Clo.VcsKeepGoingTimeout :
                             CommandLineOptions.Clo.ProverKillTime);

            no++;

            currently_running.Add(s);
          }
        } else {
          WaitHandle[] handles = new WaitHandle[currently_running.Count];
          for (int i = 0; i < currently_running.Count; ++i) {
            handles[i] = currently_running[i].ProverDone;
          }
          int index = WaitHandle.WaitAny(handles);
          s = currently_running[index];
          currently_running.RemoveAt(index);

          if (do_splitting) {
            remaining_cost -= s.Cost;
          }

          s.ReadOutcome(ref outcome, out prover_failed);

          if (do_splitting) {
            if (prover_failed) {
              // even if the prover fails, we have learned something, i.e., it is 
              // annoying to watch Boogie say Timeout, 0.00% a couple of times
              proven_cost += s.Cost / 100;
            } else {
              proven_cost += s.Cost;
            }
          }
          callback.OnProgress("VCprove", no < 0 ? 0 : no, total, proven_cost / (remaining_cost + proven_cost));

          if (prover_failed && !first_round && s.LastChance) {
            string msg = "some timeout";
            if (s.reporter != null && s.reporter.resourceExceededMessage != null) {
              msg = s.reporter.resourceExceededMessage;
            }
            callback.OnCounterexample(s.ToCounterexample(s.Checker.TheoremProver.Context), msg);
            outcome = Outcome.Errors;
            break;
          }

          Contract.Assert( prover_failed || outcome == Outcome.Correct || outcome == Outcome.Errors || outcome == Outcome.Inconclusive);
        }

        if (prover_failed) { 
          int splits = first_round && max_splits > 1 ? max_splits : max_kg_splits;

          if (splits > 1) {
            List<Split> tmp = Split.DoSplit(s, max_vc_cost, splits);
            Contract.Assert(tmp != null);
            max_vc_cost = 1.0; // for future
            first_round = false;
            //tmp.Sort(new Comparison<Split!>(Split.Compare));
            foreach (Split a in tmp) {
              Contract.Assert(a != null);
              work.Push(a);
              total++;
              remaining_cost += a.Cost;
            }
            if (outcome != Outcome.Errors) {
              outcome = Outcome.Correct;
            }
          } else {
            Contract.Assert( outcome != Outcome.Correct);
            if (outcome == Outcome.TimedOut) {
              string msg = "some timeout";
              if (s.reporter != null && s.reporter.resourceExceededMessage != null) {
                msg = s.reporter.resourceExceededMessage;
              }
              callback.OnTimeout(msg);
            } else if (outcome == Outcome.OutOfMemory) {
              string msg = "out of memory";
              if (s.reporter != null && s.reporter.resourceExceededMessage != null) {
                msg = s.reporter.resourceExceededMessage;
              }
              callback.OnOutOfMemory(msg);
            }

            break;
          }
        }
      }

      if (outcome == Outcome.Correct && smoke_tester != null) {
        smoke_tester.Test();
      }

      callback.OnProgress("done", 0, 0, 1.0);

      if (_print_time)
      {
          watch.Stop();
          Console.WriteLine("Total time for this method: {0}", watch.Elapsed.ToString());
      }

      return outcome;
    }

    public class ErrorReporter : ProverInterface.ErrorHandler {
      Hashtable/*TransferCmd->ReturnCmd*//*!*/ gotoCmdOrigins;
      Hashtable/*<int, Absy!>*//*!*/ label2absy;
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

      public ErrorReporter(Hashtable/*TransferCmd->ReturnCmd*//*!*/ gotoCmdOrigins,
          Hashtable/*<int, Absy!>*//*!*/ label2absy,
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

      public override void OnModel(IList<string/*!*/>/*!*/ labels, Model model) {
        //Contract.Requires(cce.NonNullElements(labels));
        if (CommandLineOptions.Clo.PrintErrorModel >= 1 && model != null) {
          if (VC.ConditionGeneration.errorModelList != null)
          {
            VC.ConditionGeneration.errorModelList.Add(model);
          }
          
          model.Write(ErrorReporter.ModelWriter);
          ErrorReporter.ModelWriter.Flush();
        }

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

        BlockSeq trace = new BlockSeq();
        Block entryBlock = cce.NonNull(this.blocks[0]);
        Contract.Assert(traceNodes.Contains(entryBlock));
        trace.Add(entryBlock);

        Counterexample newCounterexample = TraceCounterexample(entryBlock, traceNodes, trace, model, MvInfo, incarnationOriginMap, context, program, new Dictionary<TraceLocation, CalleeCounterexampleInfo>());

        if (newCounterexample == null)
          return;

        #region Map passive program errors back to original program errors
        ReturnCounterexample returnExample = newCounterexample as ReturnCounterexample;
        if (returnExample != null) {
          foreach (Block b in returnExample.Trace) {
            Contract.Assert(b != null);
            Contract.Assume(b.TransferCmd != null);
            ReturnCmd cmd = (ReturnCmd)gotoCmdOrigins[b.TransferCmd];
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

      public override void OnResourceExceeded(string msg) {
        //Contract.Requires(msg != null);
        resourceExceededMessage = msg;
      }

      public override void OnProverWarning(string msg) {
        //Contract.Requires(msg != null);
        callback.OnWarning(msg);
      }
    }

    public class ErrorReporterLocal : ErrorReporter {
      public ErrorReporterLocal(Hashtable/*TransferCmd->ReturnCmd*//*!*/ gotoCmdOrigins,
          Hashtable/*<int, Absy!>*//*!*/ label2absy,
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

      public override void OnModel(IList<string/*!*/>/*!*/ labels, Model model) {
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
            if (b.Cmds.Has(a)) {
              BlockSeq trace = new BlockSeq();
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
    public void ConvertCFG2DAG(Implementation impl)
    {
    Contract.Requires(impl != null);
      impl.PruneUnreachableBlocks();  // This is needed for VCVariety.BlockNested, and is otherwise just an optimization

      CurrentLocalVariables = impl.LocVars;
      variable2SequenceNumber = new Hashtable/*Variable -> int*/();
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

      ResetPredecessors(impl.Blocks);
      
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
      foreach (Block header in cce.NonNull( g.Headers))
      {
        Contract.Assert(header != null);
        IDictionary<Block,object> backEdgeNodes = new Dictionary<Block,object>();
        foreach (Block b in cce.NonNull( g.BackEdgeNodes(header))) {Contract.Assert(b != null); backEdgeNodes.Add(b, null); }
      
        #region Find the (possibly empty) prefix of assert commands in the header, replace each assert with an assume of the same condition
        CmdSeq prefixOfPredicateCmdsInit = new CmdSeq();
        CmdSeq prefixOfPredicateCmdsMaintained = new CmdSeq();
        for (int i = 0, n = header.Cmds.Length; i < n; i++)
        {
          PredicateCmd a = header.Cmds[i] as PredicateCmd;
          if (a != null)
          {
            if (a is AssertCmd) {
              Bpl.AssertCmd c = (AssertCmd) a;
              Bpl.AssertCmd b = new Bpl.LoopInitAssertCmd(c.tok, c.Expr);
              b.ErrorData = c.ErrorData;
              prefixOfPredicateCmdsInit.Add(b);
              b = new Bpl.LoopInvMaintainedAssertCmd(c.tok, c.Expr);
              b.ErrorData = c.ErrorData;
              prefixOfPredicateCmdsMaintained.Add(b);
              header.Cmds[i] = new AssumeCmd(c.tok,c.Expr);
            } else {
              Contract.Assert( a is AssumeCmd);
              if (Bpl.CommandLineOptions.Clo.AlwaysAssumeFreeLoopInvariants) {
                // Usually, "free" stuff, like free loop invariants (and the assume statements
                // that stand for such loop invariants) are ignored on the checking side.  This
                // command-line option changes that behavior to always assume the conditions.
                prefixOfPredicateCmdsInit.Add(a);
                prefixOfPredicateCmdsMaintained.Add(a);
              }
            }
          }
          else if ( header.Cmds[i] is CommentCmd )
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
        for ( int predIndex = 0, n = header.Predecessors.Length; predIndex < n; predIndex++ )
        {
          Block pred = cce.NonNull(header.Predecessors[predIndex]);
          
          // Create a block between header and pred for the predicate commands if pred has more than one successor 
          GotoCmd gotocmd = cce.NonNull((GotoCmd)pred.TransferCmd);
          Contract.Assert( gotocmd.labelNames != null);  // if "pred" is really a predecessor, it may be a GotoCmd with at least one label
          if (gotocmd.labelNames.Length > 1)
          {
            Block newBlock = CreateBlockBetween(predIndex, header);
            impl.Blocks.Add(newBlock);
            
            // if pred is a back edge node, then now newBlock is the back edge node
            if (backEdgeNodes.ContainsKey(pred))
            {
              backEdgeNodes.Remove(pred);
              backEdgeNodes.Add(newBlock,null);
            }
            
            pred = newBlock;
          } 
          // Add the predicate commands
          if (backEdgeNodes.ContainsKey(pred)){
            pred.Cmds.AddRange(prefixOfPredicateCmdsMaintained);
          }
          else {
            pred.Cmds.AddRange(prefixOfPredicateCmdsInit);
          }
        }
        #endregion

        #region Cut the back edge
        foreach (Block backEdgeNode in cce.NonNull(backEdgeNodes.Keys))
        {Contract.Assert(backEdgeNode != null);
          Debug.Assert(backEdgeNode.TransferCmd is GotoCmd,"An node was identified as the source for a backedge, but it does not have a goto command.");
          GotoCmd gtc = backEdgeNode.TransferCmd as GotoCmd;
          if (gtc != null && gtc.labelTargets != null && gtc.labelTargets.Length > 1 )
          {
            // then remove the backedge by removing the target block from the list of gotos
            BlockSeq remainingTargets = new BlockSeq();
            StringSeq remainingLabels = new StringSeq();
            Contract.Assume( gtc.labelNames != null);
            for (int i = 0, n = gtc.labelTargets.Length; i < n; i++)
            {
              if ( gtc.labelTargets[i] != header )
              {
                remainingTargets.Add(gtc.labelTargets[i]);
                remainingLabels.Add(gtc.labelNames[i]);
              }
            }
            gtc.labelTargets = remainingTargets;
            gtc.labelNames = remainingLabels;
          }
          else
          {
            // This backedge is the only out-going edge from this node.
            // Add an "assume false" statement to the end of the statements
            // inside of the block and change the goto command to a return command.
            AssumeCmd ac = new AssumeCmd(Token.NoToken,Expr.False);
            backEdgeNode.Cmds.Add(ac);
            backEdgeNode.TransferCmd = new ReturnCmd(Token.NoToken);
          }
          #region Remove the backedge node from the list of predecessor nodes in the header
          BlockSeq newPreds = new BlockSeq();
          foreach ( Block p in header.Predecessors )
          {
            if ( p != backEdgeNode )
              newPreds.Add(p);
          }
          header.Predecessors = newPreds;
          #endregion
        }
        #endregion

        #region Collect all variables that are assigned to in all of the natural loops for which this is the header
        VariableSeq varsToHavoc = new VariableSeq();
        foreach (Block backEdgeNode in cce.NonNull( g.BackEdgeNodes(header)))
        {
          Contract.Assert(backEdgeNode != null);
          foreach ( Block b in g.NaturalLoops(header,backEdgeNode) )
          {
            Contract.Assert(b != null);
            foreach ( Cmd c in b.Cmds )
            {
              Contract.Assert(c != null);
              c.AddAssignedVariables(varsToHavoc);
            }
          }
        }
        IdentifierExprSeq havocExprs = new IdentifierExprSeq();
        foreach ( Variable v in varsToHavoc )
        {
          Contract.Assert(v != null);
          IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
          if(!havocExprs.Has(ie))
            havocExprs.Add(ie);
        }
        // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
        // the source location for this later on
        HavocCmd hc = new HavocCmd(header.tok,havocExprs);
        CmdSeq newCmds = new CmdSeq();
        newCmds.Add(hc);
        foreach ( Cmd c in header.Cmds )
        {
          newCmds.Add(c);
        }
        header.Cmds = newCmds;
        #endregion
      }
      #endregion
      #endregion Convert program CFG into a DAG
      
      #region Debug Tracing
      if (CommandLineOptions.Clo.TraceVerify) 
      {
        Console.WriteLine("after conversion into a DAG");
        EmitImpl(impl, true);
      }
      #endregion
    }

    public void DesugarCalls(Implementation impl) {
      foreach (Block block in impl.Blocks) {
        CmdSeq newCmds = new CmdSeq();
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

    public Hashtable/*TransferCmd->ReturnCmd*/ PassifyImpl(Implementation impl, out ModelViewInfo mvInfo)
    {
      Contract.Requires(impl != null);
      Contract.Requires(program != null);
      Contract.Ensures(Contract.Result<Hashtable>() != null);

      Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = new Hashtable/*TransferCmd->ReturnCmd*/();
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
        CmdSeq cc = new CmdSeq();
        // where clauses of global variables
        foreach (Declaration d in program.TopLevelDeclarations) {
          GlobalVariable gvar = d as GlobalVariable;
          if (gvar != null && gvar.TypedIdent.WhereExpr != null) {
            Cmd c = new AssumeCmd(gvar.tok, gvar.TypedIdent.WhereExpr);
            cc.Add(c);
          }
        }
        // where clauses of in- and out-parameters
        cc.AddRange(GetParamWhereClauses(impl));
        // where clauses of local variables
        foreach (Variable lvar in impl.LocVars) {Contract.Assert(lvar != null);
          if (lvar.TypedIdent.WhereExpr != null) {
            Cmd c = new AssumeCmd(lvar.tok, lvar.TypedIdent.WhereExpr);
            cc.Add(c);
          }
        }
        // add cc and the preconditions to new blocks preceding impl.Blocks[0]
        InjectPreconditions(impl, cc);

        // append postconditions, starting in exitBlock and continuing into other blocks, if needed
        exitBlock = InjectPostConditions(impl, exitBlock, gotoCmdOrigins);
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

      if (CommandLineOptions.Clo.DoPredication && CommandLineOptions.Clo.StratifiedInlining == 0) {
        DesugarCalls(impl);
        BlockPredicator.Predicate(program, impl);
        impl.ComputePredecessorsForBlocks();
      }

      if (CommandLineOptions.Clo.LiveVariableAnalysis > 0) {
        Microsoft.Boogie.LiveVariableAnalysis.ComputeLiveVariables(impl);
      }

      mvInfo = new ModelViewInfo(program, impl);
      Convert2PassiveCmd(impl, mvInfo);

      #region Peep-hole optimizations
      if (CommandLineOptions.Clo.RemoveEmptyBlocks){
        #region Get rid of empty blocks
        {
          Block entryBlock = cce.NonNull( impl.Blocks[0]);
          RemoveEmptyBlocks(entryBlock);
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

      if (CommandLineOptions.Clo.ExpandLambdas)
      {
        List<Expr> axioms;
        List<Function> functions;
        LambdaHelper.Desugar(impl, out axioms, out functions);
        program.TopLevelDeclarations.AddRange(functions);

        if (axioms.Count > 0) {
          CmdSeq cmds = new CmdSeq();
          foreach (Expr ax in axioms) {
            Contract.Assert(ax != null);
            cmds.Add(new AssumeCmd(ax.tok, ax));
          }
          Block entryBlock = cce.NonNull( impl.Blocks[0]);
          cmds.AddRange(entryBlock.Cmds);
          entryBlock.Cmds = cmds;
          // Make sure that all added commands are passive commands.
          Hashtable incarnationMap = ComputeIncarnationMap(entryBlock, new Hashtable());
          TurnIntoPassiveBlock(entryBlock, incarnationMap, mvInfo,
                               ComputeOldExpressionSubstitution(impl.Proc.Modifies));
        }
      }

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

        foreach (var b in impl.Blocks) {
          if (blocksToCheck.Contains(b)) continue;
          var newCmds = new CmdSeq();
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
        foreach (var decl in program.TopLevelDeclarations)
        {
            if (decl is Procedure)
            {  
                if (!(decl is LoopProcedure))
                {
                    var p = decl as Procedure;
                    inlinedProcs.Add(p.Name);
                }
            }
        }

        return extractLoopTraceRec(
            new CalleeCounterexampleInfo(cex, new List<Model.Element>()),
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
        ret.Trace = new BlockSeq();
        ret.calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();

        for (int numBlock = 0; numBlock < cex.Trace.Length; numBlock ++ )
        {
            Block block = cex.Trace[numBlock];
            var origBlock = elGetBlock(currProc, block, extractLoopMappingInfo);
            if (origBlock != null) ret.Trace.Add(origBlock);
            var callCnt = 1;
            for (int numInstr = 0; numInstr < block.Cmds.Length; numInstr ++) {
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

                    int currLen = ret.Trace.Length;
                    ret.Trace.AddRange(origTrace.counterexample.Trace);

                    foreach (var kvp in origTrace.counterexample.calleeCounterexamples)
                    {
                        var newloc = new TraceLocation(kvp.Key.numBlock + currLen, kvp.Key.numInstr);
                        ret.calleeCounterexamples.Add(newloc, kvp.Value);
                    }

                }
                else
                {
                    var origLoc = new TraceLocation(ret.Trace.Length - 1, getCallCmdPosition(origBlock, callCnt, inlinedProcs, callee));
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
        for (int pos = 0; pos < block.Cmds.Length; pos++)
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
                          Block/*!*/ b, Hashtable/*!*/ traceNodes, BlockSeq/*!*/ trace, Model errModel, ModelViewInfo mvInfo,
                          Dictionary<Incarnation, Absy/*!*/>/*!*/ incarnationOriginMap,
                          ProverContext/*!*/ context, Program/*!*/ program,
                          Dictionary<TraceLocation/*!*/, CalleeCounterexampleInfo/*!*/>/*!*/ calleeCounterexamples)
    {
      Contract.Requires(b != null);
      Contract.Requires(traceNodes != null);
      Contract.Requires(trace != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(incarnationOriginMap));
      Contract.Requires(context != null);
      Contract.Requires(program != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(calleeCounterexamples));
      // After translation, all potential errors come from asserts.
      CmdSeq cmds = b.Cmds;
      Contract.Assert(cmds != null);
      TransferCmd transferCmd = cce.NonNull(b.TransferCmd);
      for (int i = 0; i < cmds.Length; i++)
      {
        Cmd cmd = cce.NonNull( cmds[i]);
            
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
      if (gotoCmd != null)
      {
        foreach (Block bb in cce.NonNull(gotoCmd.labelTargets))
        {
          Contract.Assert(bb != null);
          if (traceNodes.Contains(bb)){
            trace.Add(bb);
            return TraceCounterexample(bb, traceNodes, trace, errModel, mvInfo, incarnationOriginMap, context, program, calleeCounterexamples);
          }
        }
      }

      return null;
    }

    public static Counterexample AssertCmdToCounterexample(AssertCmd cmd, TransferCmd transferCmd, BlockSeq trace, Model errModel, ModelViewInfo mvInfo, ProverContext context) 
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
        CallCounterexample cc = new CallCounterexample(trace, assertCmd.Call, assertCmd.Requires, errModel, mvInfo, context);
        cc.relatedInformation = relatedInformation;
        return cc;
      }
      else if (cmd is AssertEnsuresCmd)
      {
        AssertEnsuresCmd assertCmd = (AssertEnsuresCmd)cmd;
        Contract.Assert(assertCmd != null);
        ReturnCounterexample rc = new ReturnCounterexample(trace, transferCmd, assertCmd.Ensures, errModel, mvInfo, context);
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

    static VCExpr LetVC(Block startBlock,
                        VCExpr controlFlowVariableExpr,
                        Hashtable/*<int, Absy!>*/ label2absy,
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
                                 Hashtable label2absy,
                                 ProverContext proverCtxt,
                                 out int assertionCount) {
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
          }
        }
        else {
          Contract.Assert(gotocmd.labelTargets != null);
          List<VCExpr> SuccCorrectVars = new List<VCExpr>(gotocmd.labelTargets.Length);
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

        VCContext context = new VCContext(label2absy, proverCtxt, controlFlowVariableExpr);
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
                        Hashtable/*<int, Absy!>*/ label2absy,
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
          List<VCExpr> SuccCorrectVars = new List<VCExpr>(gotocmd.labelTargets.Length);
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
                         Hashtable/*<int, Absy!>*/ label2absy,
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
                              Hashtable/*<int, Absy!>*/ label2absy,
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
                                Hashtable/*<int, Absy!>*/ label2absy,
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
                  (Implementation impl, Hashtable/*<int, Absy!>*/ label2absy,
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
    /// Remove the empty blocks reachable from the block.
    /// It changes the visiting state of the blocks, so that if you want to visit again the blocks, you have to reset them...
    /// </summary>
    static BlockSeq RemoveEmptyBlocks(Block b) {
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<BlockSeq>() != null);

      Contract.Assert(b.TraversingStatus == Block.VisitState.ToVisit);
      Block renameInfo;
      BlockSeq retVal = removeEmptyBlocksWorker(b, true, out renameInfo);
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
    private static BlockSeq removeEmptyBlocksWorker(Block b, bool startNode, out Block renameInfoForStartBlock)
  {
      Contract.Requires(b != null);
      Contract.Ensures(Contract.ValueAtReturn(out renameInfoForStartBlock) == null || Contract.ValueAtReturn(out renameInfoForStartBlock).tok.IsValid);
      // ensures: b in result ==> renameInfoForStartBlock == null;
    
      renameInfoForStartBlock = null;
      BlockSeq bs = new BlockSeq();
      GotoCmd gtc = b.TransferCmd as GotoCmd;

      // b has no successors
      if (gtc == null || gtc.labelTargets == null || gtc.labelTargets.Length == 0) 
      {
        if (b.Cmds.Length != 0){ // only empty blocks are removed...
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
        if (b.Cmds.Length == 0 && !startNode) {
          // b is about to become extinct; try to save its name and location, if possible
          if (b.tok.IsValid && gtc.labelTargets.Length == 1) {
            Block succ = cce.NonNull(gtc.labelTargets[0]);
            if (!succ.tok.IsValid && succ.Predecessors.Length == 1) {
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
          BlockSeq ys = removeEmptyBlocksWorker(dest, false, out renameInfo);
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

        BlockSeq setOfSuccessors = new BlockSeq();
        foreach (Block d in mergedSuccessors)
          setOfSuccessors.Add(d);
        if (b.Cmds.Length == 0 && !startNode) {
          // b is about to become extinct
          if (b.tok.IsValid) {
            renameInfoForStartBlock = b;
          }
          return setOfSuccessors;
        }
        // otherwise, update the list of successors of b to be the blocks in setOfSuccessors
        gtc.labelTargets = setOfSuccessors;
        gtc.labelNames = new StringSeq();
        foreach (Block d in setOfSuccessors){
          Contract.Assert(d != null);
          gtc.labelNames.Add(d.Label);}
        if (!startNode) {
          renameInfoForStartBlock = null;
        }
        return new BlockSeq(b);
      }
      else // b has some successors, but we are already visiting it, or we have already visited it...
      {
        return new BlockSeq(b);
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
        v.Emit(new TokenTextWriter("<console>", Console.Out, false), 0);
        Console.Write("  --> ");
        e.Emit(new TokenTextWriter("<console>", Console.Out, false));
        Console.WriteLine();
      }
    }
  }
}
