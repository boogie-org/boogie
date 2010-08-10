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
  public class DCGen : ConditionGeneration {
    #region Attributes
    private Dictionary<Block, Variable/*!*/>/*!*/ m_BlockReachabilityMap;
    Dictionary<Block/*!*/, Block/*!*/>/*!*/ m_copiedBlocks = new Dictionary<Block/*!*/, Block/*!*/>();
    const string reachvarsuffix = "__ivebeenthere";
    List<Cmd/*!*/>/*!*/ m_doomedCmds = new List<Cmd/*!*/>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(m_BlockReachabilityMap));
      Contract.Invariant(cce.NonNullElements(m_copiedBlocks));
      Contract.Invariant(cce.NonNullElements(m_doomedCmds));
      Contract.Invariant(cce.NonNullElements(_copiedBlock));
    }

    #endregion
    /// <summary>
    /// Constructor.  Initializes the theorem prover.
    /// </summary>
    public DCGen(Program program, string/*?*/ logFilePath, bool appendLogFile)
      : base(program) {
      Contract.Requires(program != null);

      this.appendLogFile = appendLogFile;
      this.logFilePath = logFilePath;
      m_BlockReachabilityMap = new Dictionary<Block, Variable>();
    }


    private void Impl2Dot(Implementation impl, string filename) {
      Contract.Requires(impl != null);
      Contract.Requires(filename != null);
      List<string> nodes = new List<string>();
      List<string> edges = new List<string>();

      string nodestyle = "[shape=box];";

      foreach (Block b in impl.Blocks) {
        Contract.Assert(b != null);
        nodes.Add(string.Format("\"{0}\" {1}", b.Label, nodestyle));
        GotoCmd gc = b.TransferCmd as GotoCmd;
        if (gc != null) {
          Contract.Assert(gc.labelTargets != null);
          foreach (Block b_ in gc.labelTargets) {
            Contract.Assert(b_ != null);
            edges.Add(String.Format("\"{0}\" -> \"{1}\";", b.Label, b_.Label));
          }
        }
      }

      using (StreamWriter sw = new StreamWriter(filename)) {
        sw.WriteLine(String.Format("digraph {0} {{", impl.Name));
        //            foreach (string! s in nodes) {
        //                sw.WriteLine(s);
        //            }
        foreach (string s in edges) {
          Contract.Assert(s != null);
          sw.WriteLine(s);
        }
        sw.WriteLine("}}");
        sw.Close();
      }
    }

    private const string _copyPrefix = "Yeah";

    private Block CopyImplBlocks(Block b, ref List<Block> blocklist, Block targetBlock, ref Dictionary<Block, Block> alreadySeen) {
      Contract.Requires(b != null);
      Contract.Requires(targetBlock != null);
      Contract.Requires(cce.NonNullElements(alreadySeen));
      Contract.Requires(blocklist != null);
      Contract.Ensures(Contract.ValueAtReturn(out blocklist) != null);
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out alreadySeen)));
      Contract.Ensures(Contract.Result<Block>() != null);

      Block seen;
      if (alreadySeen.TryGetValue(b, out seen)) {
        Contract.Assert(seen != null);
        return seen;
      }

      GotoCmd gc = b.TransferCmd as GotoCmd;
      TransferCmd tcmd = null;
      if (gc != null) {
        BlockSeq bseq = new BlockSeq();
        Contract.Assert(gc.labelTargets != null);
        foreach (Block c in gc.labelTargets) {
          Contract.Assert(c != null);
          bseq.Add(CopyImplBlocks(c, ref blocklist, targetBlock, ref alreadySeen));
        }
        tcmd = new GotoCmd(gc.tok, bseq);
      } else {
        //            BlockSeq! bseq_ = new BlockSeq();
        //            bseq_.Add(targetBlock);
        Contract.Assert(b.TransferCmd != null);
        //            tcmd = new GotoCmd(b.TransferCmd.tok, bseq_);
        tcmd = new ReturnCmd(b.TransferCmd.tok);
      }

      CodeCopier codeCopier = new CodeCopier();
      CmdSeq cl = new CmdSeq();
      foreach (Cmd _c in b.Cmds) {
        Contract.Assert(_c != null);
        if (!ContainsReachVariable(_c))
          cl.Add(codeCopier.CopyCmd(_c));
      }

      Block b_ = new Block(b.tok, b.Label + _copyPrefix, cl, tcmd);
      Contract.Assert(b_ != null);
      blocklist.Add(b_);

      alreadySeen[b] = b_;

      return b_;
    }

    /*
        After adding a copy of the implementation in front of our code
        we remove all the edges leading from the copy to the original code
    */
    private void RemoveArtificialGoto(Block b, Block target) {
      Contract.Requires(b != null);
      Contract.Requires(target != null);
      GotoCmd gc = b.TransferCmd as GotoCmd;

      if (gc != null) {
        Contract.Assert(gc.labelTargets != null);
        foreach (Block gt in gc.labelTargets) {
          Contract.Assert(gt != null);
          if (gt == target) {
            Contract.Assert(gc.labelTargets.Length == 1);
            Contract.Assert(gc.labelTargets[0] != null);
            b.TransferCmd = new ReturnCmd(gc.tok);
            return;
          } else {
            RemoveArtificialGoto(gt, target);
          }
        }

      }
    }

    static public bool UseItAsDebugger = false;

    //    public static Implementation _tmpImpl = null; // (MsSchaef) HACK!

    public static Block firstNonDebugBlock = null;
    public static Block firstDebugBlock = null;

    private void ModifyImplForDebugging(Implementation impl) {
      Contract.Requires(impl != null);
      //List<Block!> backup_blocks=null;


      if (UseItAsDebugger) {
        #region Copy the Implementation /////////////////////

        ConsoleColor col = Console.ForegroundColor;
        Console.ForegroundColor = ConsoleColor.Magenta;
        Console.WriteLine("Warning you are using the Infinite Improbability Drive!");
        Console.ForegroundColor = col;

        List<Block/*!*/>/*!*/ blist = new List<Block/*!*/>();
        Dictionary<Block, Block> tmpdict = new Dictionary<Block, Block>();
        CopyImplBlocks(impl.Blocks[0], ref blist, impl.Blocks[0], ref tmpdict);
        blist.Reverse();
        //_tmpImpl = new Implementation(impl.tok, impl.Name, impl.TypeParameters, impl.InParams, impl.OutParams, impl.LocVars, blist);

        #endregion ////////////////////////////////////

        #region Add implementation copy in front of implementation
        // memorize where the original code starts
        firstNonDebugBlock = impl.Blocks[0];
        firstDebugBlock = blist[0];
        // now add the copied program in front of the original one
        blist.AddRange(impl.Blocks);
        //backup_blocks = new List<Block!>(impl.Blocks);

        BlockSeq newbseq = new BlockSeq();
        newbseq.Add(firstNonDebugBlock);
        newbseq.Add(firstDebugBlock);

        GotoCmd newtcmd = new GotoCmd(Token.NoToken, newbseq);
        Block newfirst = new Block(Token.NoToken, "MySuperFirstBlock", new CmdSeq(), newtcmd);


        impl.Blocks = new List<Block>();
        impl.Blocks.Add(newfirst);
        impl.Blocks.AddRange(blist);

        //Impl2Dot(impl, String.Format("c:/dot/{0}_copied.dot", impl.Name) );
        #endregion
      }
    }

    void RemoveReachVars(Block b) {
      Contract.Requires(b != null);
      GotoCmd gc = b.TransferCmd as GotoCmd;
      if (gc != null) {
        CmdSeq cs = new CmdSeq();
        foreach (Cmd c in b.Cmds) {
          Contract.Assert(c != null);
          if (!ContainsReachVariable(c))
            cs.Add(c);
        }
        b.Cmds = cs;

        foreach (Block c in gc.labelTargets) {
          Contract.Assert(c != null);
          if (c.Label != "GeneratedUnifiedExit") {
            RemoveReachVars(c);
          }
        }
      }
    }

    void RemoveLastBlock(Block b) {
      Contract.Requires(b != null);
      GotoCmd gc = b.TransferCmd as GotoCmd;
      if (gc == null) {
        //Console.WriteLine("WARNING: Check Node {0}", b.Label);
        return;
      }
      Contract.Assert(gc != null);
      Contract.Assert(gc.labelTargets != null);
      BlockSeq tmp = new BlockSeq();
      foreach (Block c in gc.labelTargets) {
        Contract.Assert(c != null);
        // Warning, we should not search by name!
        if (c.Label != "GeneratedUnifiedExit") {
          tmp.Add(c);
          RemoveLastBlock(c);
        } else {
          c.Predecessors.Remove(b);
        }
      }
      if (tmp.Length == 0) {
        b.TransferCmd = new ReturnCmd(gc.tok);
      } else {
        b.TransferCmd = new GotoCmd(gc.tok, tmp);
      }
    }

    void FindCopiedBlocks(Block b) {
      Contract.Requires(b != null);
      _copiedBlock.Add(b);
      GotoCmd gc = b.TransferCmd as GotoCmd;
      if (gc != null) {
        Contract.Assert(gc.labelTargets != null);
        foreach (Block c in gc.labelTargets) {
          Contract.Assert(c != null);
          FindCopiedBlocks(c);
        }
      }
    }

    private List<Block> _copiedBlock = new List<Block>();

    /// <summary>
    /// MSchaef: 
    /// - remove loops and add reach variables
    /// - make it a passive program
    /// - compute the wlp for each block
    /// - check if |= (reach=false) => wlp.S.false holds for each reach
    ///
    /// </summary>
    public override Outcome VerifyImplementation(Implementation impl, Program program, VerifierCallback callback) {
      Contract.Requires(impl != null);
      Contract.Requires(program != null);
      Contract.Requires(callback != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      UseItAsDebugger = CommandLineOptions.Clo.useDoomDebug;
      Stopwatch watch = new Stopwatch();

      //Impl2Dot(impl, String.Format("c:/dot/{0}_raw.dot", impl.Name) );

      if (CommandLineOptions.Clo.TraceVerify) {
        Console.WriteLine(">>> Checking function {0} for doomed points.", impl.Name);
      }
      Console.WriteLine("Checking function {0} for doomed points:", impl.Name);
      callback.OnProgress("doomdetector", 0, 0, 0);

      watch.Reset();
      watch.Start();



      #region Transform the Program into loop-free passive form
      variable2SequenceNumber = new Hashtable/*Variable -> int*/();
      incarnationOriginMap = new Dictionary<Incarnation, Absy>();
      List<Block> cblocks = new List<Block>();

      //List<Block!>! orig_blocks = new List<Block!>(impl.Blocks);

      Dictionary<Block, Block> copiedblocks;
      impl.Blocks = DCProgramTransformer.Convert2Dag(impl, program, cblocks, out copiedblocks);
      Contract.Assert(copiedblocks != null);

      //      List<Block!>! blist = new List<Block!>();
      //      blist.AddRange(impl.Blocks);

      if (UseItAsDebugger)
        ModifyImplForDebugging(impl);

      ComputePredecessors(impl.Blocks);

      m_BlockReachabilityMap = new Dictionary<Block, Variable>();
      GenerateReachVars(impl);

      if (UseItAsDebugger)
        RemoveReachVars(cce.NonNull(firstDebugBlock));

      PassifyProgram(impl);

      #endregion
      //EmitImpl(impl,false);


      //Impl2Dot(impl, String.Format("c:/dot/{0}_passive.dot", impl.Name) );

      // ---------------------------------------------------------------------------
      if (UseItAsDebugger) {
        Contract.Assert(firstNonDebugBlock != null && firstDebugBlock != null);
        firstNonDebugBlock.Predecessors.Remove(impl.Blocks[0]);
        firstDebugBlock.Predecessors.Remove(impl.Blocks[0]);
        //        impl.Blocks.Remove(impl.Blocks[0]); // remove the artificial first block
        RemoveLastBlock(firstDebugBlock); // remove the goto to the unified exit  
        _copiedBlock.Clear();
        FindCopiedBlocks(firstDebugBlock);
      }
      // ---------------------------------------------------------------------------      

      // EmitImpl(impl,false);

      //Impl2Dot(impl, String.Format("c:/dot/{0}_final.dot", impl.Name) );

      bool __debug = false;

      watch.Stop();
      if (__debug)
        Console.WriteLine("Transformation takes: {0}", watch.Elapsed.ToString());
      watch.Reset();

      Checker checker = FindCheckerFor(impl, 1000);
      Contract.Assert(checker != null);

      DoomCheck dc = new DoomCheck(impl, checker);

      int _totalchecks = 0;
      Block b = null;
      ProverInterface.Outcome outcome;
      dc.ErrorHandler = new DoomErrorHandler(dc.Label2Absy, callback);

      System.TimeSpan ts = watch.Elapsed;

      while (dc.GetNextBlock(out b)) {
        Contract.Assert(b != null);
        outcome = ProverInterface.Outcome.Undetermined;
        //Console.WriteLine("Checking block {0} ...",b.Label);
        Variable v = null;
        m_BlockReachabilityMap.TryGetValue(b, out v);
        Contract.Assert(v != null);
        _totalchecks++;


        watch.Start();
        if (!dc.CheckLabel(v, out outcome)) {
          return Outcome.Inconclusive;
        }
        watch.Stop();
        ts += watch.Elapsed;
        if (__debug)
          Console.WriteLine(" Time for Block {0}: {1} elapsed", b.Label, watch.Elapsed.ToString());
        watch.Reset();


        switch (outcome) {
          case ProverInterface.Outcome.Valid: {
              break;
            }
          case ProverInterface.Outcome.Invalid: {

              break;
            }
          default: {

              break;
            }
        }

      }
      checker.Close();

      if (__debug)
        Console.WriteLine("Number of Checked Blocks: {0} of {1}", _totalchecks, impl.Blocks.Count);
      if (__debug)
        Console.WriteLine("Total time for this method: {0}", ts.ToString());

      #region Try to produce a counter example (brute force)
      if (dc.DoomedSequences.Count > 0) {
        ConsoleColor col = Console.ForegroundColor;
        //        Console.ForegroundColor = ConsoleColor.Red;
        //        Console.WriteLine("  {0} is DOOMED!", impl.Name);
        //        foreach (List<Block!> bl in dc.DoomedSequences) {
        //            Console.Write("Doomed Blocks: ");
        //            foreach (Block! b_ in bl) {
        //                Console.Write("{0}, ", b_.Label);
        //                }
        //                Console.WriteLine();
        //        }        
        Console.ForegroundColor = col;

        int counter = 1;
        foreach (List<Block> bl in dc.DoomedSequences) {
          Contract.Assert(bl != null);
          Console.WriteLine("Doomed program point {0} of {1}", counter++, dc.DoomedSequences.Count);
          dc.ErrorHandler.m_DoomedBlocks = bl;
          foreach (Block b_ in bl) {
            Contract.Assert(b_ != null);
            if (m_BlockReachabilityMap.TryGetValue(b_, out dc.ErrorHandler.m_Reachvar))
              break;
          }
          SearchCounterexample(impl, dc.ErrorHandler, callback);
        }

        //SearchCounterexample(impl, dc.ErrorHandler, callback);
        Console.WriteLine("------------------------------ \n\n");
        return Outcome.Errors;
      }
      #endregion

      Console.WriteLine("------------------------------ \n\n");

      return Outcome.Correct;
    }



    private void SearchCounterexample(Implementation impl, DoomErrorHandler errh, VerifierCallback callback) {
      Contract.Requires(impl != null);
      Contract.Requires(errh != null);
      Contract.Requires(callback != null);
      Contract.Requires(errh.m_Reachvar != null);
      //if (errh.m_Reachvar==null) {
      //    Contract.Assert(false);throw new cce.UnreachableException();
      //}
      m_doomedCmds.Clear();

      Dictionary<Block, CmdSeq> cmdbackup = new Dictionary<Block, CmdSeq>();

      BruteForceCESearch(errh.m_Reachvar, impl, callback, cmdbackup, 0, impl.Blocks.Count / 2 - 1);
      BruteForceCESearch(errh.m_Reachvar, impl, callback, cmdbackup, impl.Blocks.Count / 2, impl.Blocks.Count - 1);

      List<Cmd> causals = CollectCausalStatements(impl.Blocks[0]);
      foreach (Cmd c in causals) {
        Contract.Assert(c != null);
        GenerateErrorMessage(c, causals);
      }

      #region Undo all modifications
      foreach (KeyValuePair<Block, CmdSeq> kvp in cmdbackup) {
        Contract.Assert(kvp.Key != null);
        Contract.Assert(kvp.Value != null);
        kvp.Key.Cmds = kvp.Value;
      }
      #endregion
    }

    #region Causal Statement Tree

    private void GenerateErrorMessage(Cmd causalStatement, List<Cmd> causals) {
      Contract.Requires(causalStatement != null);
      Contract.Requires(cce.NonNullElements(causals));
      AssumeCmd uc = causalStatement as AssumeCmd;
      AssertCmd ac = causalStatement as AssertCmd;
      ConsoleColor col = Console.ForegroundColor;

      // Trivial case. Must be either assume or assert false
      if (m_doomedCmds.Count == 1) {
        Console.WriteLine("Found a trivial error:");
        if (uc != null) {
          Console.Write("Trivial false assumption: ");
          Console.Write("({0};{1}):", uc.tok.line, uc.tok.col);
        }
        if (ac != null) {
          Console.Write("Trivial false assertion: ");
          Console.Write("({0};{1}):", ac.tok.line, ac.tok.col);
        }
        causalStatement.Emit(new TokenTextWriter("<console>", Console.Out, false), 0);
      } else {
        // Safety error
        if (ac != null) {
          Console.ForegroundColor = ConsoleColor.Red;
          Console.WriteLine("Safety error:");
          Console.ForegroundColor = col;
          Console.Write("This assertion is violated: ");
          Console.Write("({0};{1}):", ac.tok.line, ac.tok.col);
          ac.Emit(new TokenTextWriter("<console>", Console.Out, false), 0);
        }
        if (uc != null) {
          bool containsAssert = false;
          foreach (Cmd c in m_doomedCmds) {
            Contract.Assert(c != null);
            if (causals.Contains(c)) {
              continue;
            }
            AssertCmd asrt = c as AssertCmd;
            if (asrt != null) {
              containsAssert = true;
              break;
            }
          }
          // Plausibility error
          if (containsAssert) {
            Console.ForegroundColor = ConsoleColor.Yellow;
            Console.WriteLine("Plausibility error:");
            Console.ForegroundColor = col;
            Console.Write("There is no legal exeuction passing: ");
            Console.Write("({0};{1})", uc.tok.line, uc.tok.col);
            uc.Emit(new TokenTextWriter("<console>", Console.Out, false), 0);
          } else { // Reachability error
            Console.ForegroundColor = ConsoleColor.DarkRed;
            Console.WriteLine("Reachability error:");
            Console.ForegroundColor = col;
            Console.Write("No execution can reach: ");
            Console.Write("({0};{1})", uc.tok.line, uc.tok.col);
            uc.Emit(new TokenTextWriter("<console>", Console.Out, false), 0);
          }

        }

        Console.ForegroundColor = ConsoleColor.White;
        Console.WriteLine("...on any execution passing through:");
        foreach (Cmd c in m_doomedCmds) {
          Contract.Assert(c != null);
          if (causals.Contains(c)) {
            continue;
          }
          Console.ForegroundColor = col;
          Console.Write("In ({0};{1}): ", c.tok.line, c.tok.col);
          Console.ForegroundColor = ConsoleColor.DarkYellow;
          c.Emit(new TokenTextWriter("<console>", Console.Out, false), 0);
        }
        Console.ForegroundColor = col;
        Console.WriteLine("--");

      }
    }

    private List<Cmd> CollectCausalStatements(Block b) {
      Contract.Requires(b != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Cmd>>()));

      Cmd lastCausal = null;
      foreach (Cmd c in b.Cmds) {
        Contract.Assert(c != null);
        AssertCmd ac = c as AssertCmd;
        AssumeCmd uc = c as AssumeCmd;
        if (ac != null && !ContainsReachVariable(ac)) {
          if (ac.Expr != Expr.True) {
            lastCausal = c;
          }
        } else if (uc != null && !ContainsReachVariable(uc)) {
          lastCausal = c;
        }
      }

      List<Cmd> causals = new List<Cmd>();
      GotoCmd gc = b.TransferCmd as GotoCmd;
      if (gc != null && gc.labelTargets != null) {
        List<Cmd> tmp;
        //bool allcausal = true;
        foreach (Block b_ in gc.labelTargets) {
          Contract.Assert(b_ != null);
          tmp = CollectCausalStatements(b_);

          foreach (Cmd cau in tmp) {
            if (!causals.Contains(cau))
              causals.Add(cau);
          }
        }
        //if (allcausal) 
        if (causals.Count > 0)
          return causals;
      }
      if (lastCausal != null)
        causals.Add(lastCausal);
      return causals;
    }

    #endregion

    bool BruteForceCESearch(Variable reachvar, Implementation impl, VerifierCallback callback,
                        Dictionary<Block, CmdSeq> cmdbackup, int startidx, int endidx) {
      Contract.Requires(reachvar != null);
      Contract.Requires(impl != null);
      Contract.Requires(callback != null);
      Contract.Requires(cce.NonNullElements(cmdbackup));
      #region Modify implementation
      for (int i = startidx; i <= endidx; i++) {
        if (_copiedBlock.Contains(impl.Blocks[i]))
          continue;
        CmdSeq cs = new CmdSeq();
        cmdbackup.Add(impl.Blocks[i], impl.Blocks[i].Cmds);
        foreach (Cmd c in impl.Blocks[i].Cmds) {
          Contract.Assert(c != null);
          if (ContainsReachVariable(c)) {
            cs.Add(c);
            continue;
          }
          AssertCmd ac = c as AssertCmd;
          AssumeCmd uc = c as AssumeCmd;
          if (ac != null) {
            cs.Add(new AssertCmd(ac.tok, Expr.True));
          } else if (uc != null) {
            cs.Add(new AssertCmd(uc.tok, Expr.True));
          } else {
            cs.Add(c);
          }
        }
        impl.Blocks[i].Cmds = cs;
      }
      #endregion

      ProverInterface.Outcome outcome = ProverInterface.Outcome.Undetermined;
      if (!ReCheckImpl(reachvar, impl, callback, out outcome)) {
        UndoBlockModifications(impl, cmdbackup, startidx, endidx);
        return false;
      }
      if (outcome == ProverInterface.Outcome.Valid) {
        return true;
      } else if (outcome == ProverInterface.Outcome.Invalid) {
        UndoBlockModifications(impl, cmdbackup, startidx, endidx);
        int mid = startidx + (endidx - startidx) / 2;
        if (startidx >= endidx) {
          // Now we found an interesting Block and we have to
          // search for the interesting statements.
          int cmdcount = impl.Blocks[endidx].Cmds.Length;
          BruteForceCmd(impl.Blocks[endidx], 0, cmdcount / 2 - 1, reachvar, impl, callback);
          BruteForceCmd(impl.Blocks[endidx], cmdcount / 2, cmdcount - 1, reachvar, impl, callback);
          return true;
        } else {
          BruteForceCESearch(reachvar, impl, callback, cmdbackup, startidx, mid);
          BruteForceCESearch(reachvar, impl, callback, cmdbackup, mid + 1, endidx);
          return true;
        }
      } else {
        UndoBlockModifications(impl, cmdbackup, startidx, endidx);
        return false;
      }
    }

    bool BruteForceCmd(Block b, int startidx, int endidx, Variable reachvar,
                       Implementation impl, VerifierCallback callback) {
      Contract.Requires(b != null);
      Contract.Requires(reachvar != null);
      Contract.Requires(impl != null);
      Contract.Requires(callback != null);
      #region Modify Cmds
      CmdSeq backup = b.Cmds;
      Contract.Assert(backup != null);
      CmdSeq cs = new CmdSeq();
      for (int i = 0; i < startidx; i++) {
        cs.Add(b.Cmds[i]);
      }
      for (int i = startidx; i <= endidx; i++) {
        Cmd c = b.Cmds[i];
        if (ContainsReachVariable(c)) {
          cs.Add(c);
          continue;
        }
        cs.Add(new AssertCmd(c.tok, Expr.True));
      }
      for (int i = endidx + 1; i < b.Cmds.Length; i++) {
        cs.Add(b.Cmds[i]);
      }

      b.Cmds = cs;
      #endregion

      #region Recheck
      ProverInterface.Outcome outcome = ProverInterface.Outcome.Undetermined;
      if (!ReCheckImpl(reachvar, impl, callback, out outcome)) {
        b.Cmds = backup;
        return false;
      }
      #endregion

      if (outcome == ProverInterface.Outcome.Valid) {
        return true;
      } else if (outcome == ProverInterface.Outcome.Invalid) {
        b.Cmds = backup;
        if (startidx >= endidx) {
          if (!ContainsReachVariable(b.Cmds[endidx])) {
            //                    Console.Write("   Witness (");
            //                    
            //                    ConsoleColor col = Console.ForegroundColor;
            //                    Console.ForegroundColor = ConsoleColor.White;
            //                    Console.Write("{0};{1}", b.Cmds[endidx].tok.line, b.Cmds[endidx].tok.col );
            //                    Console.ForegroundColor = col;
            //                    Console.Write("):   ");
            //                    Console.ForegroundColor = ConsoleColor.Yellow;
            //                    b.Cmds[endidx].Emit(new TokenTextWriter("<console>", Console.Out, false), 0);
            //                    Console.ForegroundColor = col;

            m_doomedCmds.Add(b.Cmds[endidx]);
            return true;
          } else {
            return false;
          }
        } else {
          int mid = startidx + (endidx - startidx) / 2;
          BruteForceCmd(b, startidx, mid, reachvar, impl, callback);
          BruteForceCmd(b, mid + 1, endidx, reachvar, impl, callback);
          return false; // This is pure random
        }
      } else {
        b.Cmds = backup;
        return false;
      }

      return false;
    }

    void UndoBlockModifications(Implementation impl, Dictionary<Block/*!*/, CmdSeq/*!*/>/*!*/ cmdbackup,
                                int startidx, int endidx) {
      Contract.Requires(cce.NonNullElements(cmdbackup));
      Contract.Requires(impl != null);
      for (int i = startidx; i <= endidx; i++) {
        CmdSeq cs = null;
        if (cmdbackup.TryGetValue(impl.Blocks[i], out cs)) {
          Contract.Assert(cs != null);
          impl.Blocks[i].Cmds = cs;
          cmdbackup.Remove(impl.Blocks[i]);
        }
      }
    }

    bool ReCheckImpl(Variable reachvar, Implementation impl, VerifierCallback callback,
                     out ProverInterface.Outcome outcome) {
      Contract.Requires(reachvar != null);
      Contract.Requires(impl != null);
      Contract.Requires(callback != null);
      Checker checker = FindCheckerFor(impl, 1000);
      Contract.Assert(checker != null);
      DoomCheck dc = new DoomCheck(impl, checker);
      dc.ErrorHandler = new DoomErrorHandler(dc.Label2Absy, callback);
      outcome = ProverInterface.Outcome.Undetermined;
      if (!dc.CheckLabel(reachvar, out outcome)) {
        checker.Close();
        return false;
      }
      checker.Close();
      return true;
    }



    bool ContainsReachVariable(Cmd c) {
      Contract.Requires(c != null);
      AssertCmd artc = c as AssertCmd;
      AssumeCmd amec = c as AssumeCmd;
      Expr e;
      if (artc != null) {
        e = artc.Expr;
      } else if (amec != null) {
        e = amec.Expr;
      } else {
        return false;
      }
      Set freevars = new Set();
      e.ComputeFreeVariables(freevars);
      foreach (Variable v in freevars) {
        Contract.Assert(v != null);
        if (v.Name.Contains(reachvarsuffix))
          return true;
      }
      return false;
    }


    #region Loop Removal
    /// <summary>
    /// This class is accessed only via the static method Convert2Dag
    /// It converts the program into a loopfree one by unrolling the loop threetimes and adding the appropriate havoc
    /// statements. The first and the last unrolling represent the first and last iteration of the loop. The second
    /// unrolling stands for any other iteration.
    /// </summary>
    private class DCProgramTransformer {
      private List<Block> Blocks;
      private List<Block> m_checkableBlocks;
      private Dictionary<Block, Block> m_copyMap = new Dictionary<Block, Block>();
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullElements(Blocks));
        Contract.Invariant(cce.NonNullElements(m_checkableBlocks));
        Contract.Invariant(cce.NonNullElements(m_copyMap));
      }


      public static List<Block> Convert2Dag(Implementation impl, Program program, List<Block> checkableBlocks,
            out Dictionary<Block, Block> copiedblocks) {
        Contract.Requires(impl != null);
        Contract.Requires(program != null);
        Contract.Requires(cce.NonNullElements(checkableBlocks));
        Contract.Requires(1 <= impl.Blocks.Count);
        Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out copiedblocks)));

        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));

        Block start = impl.Blocks[0];
        Contract.Assert(start != null);
        Dictionary<Block, GraphNode> gd = new Dictionary<Block, GraphNode>();
        Set/*Block*/ beingVisited = new Set/*Block*/();
        GraphNode gStart = GraphNode.ComputeGraphInfo(null, start, gd, beingVisited);

        DCProgramTransformer pt = new DCProgramTransformer(checkableBlocks);
        pt.LoopUnrolling(gStart, new Dictionary<GraphNode, Block>(), true, "");
        pt.Blocks.Reverse();
        copiedblocks = pt.m_copyMap;
        return pt.Blocks;
      }


      DCProgramTransformer(List<Block> checkableBlocks) {
        Contract.Requires(cce.NonNullElements(checkableBlocks));
        Blocks = new List<Block>();
        m_checkableBlocks = checkableBlocks;
      }


      #region Loop Unrolling Methods

      private Block LoopUnrolling(GraphNode node, Dictionary<GraphNode, Block> visited, bool unrollable, String prefix) {
        Contract.Requires(node != null);
        Contract.Requires(cce.NonNullElements(visited));
        Contract.Requires(prefix != null);
        Contract.Ensures(Contract.Result<Block>() != null);

        Block newb;
        if (visited.TryGetValue(node, out newb)) {
          Contract.Assert(newb != null);
          return newb;
        } else {
          if (node.IsCutPoint) {
            // compute the loop body and the blocks leaving the loop

            List<GraphNode> loopNodes = new List<GraphNode>();
            GatherLoopBodyNodes(node, node, loopNodes);

            List<GraphNode> exitNodes = GatherLoopExitNodes(loopNodes);

            // Continue Unrolling after the current loop
            Dictionary<GraphNode, Block> _visited = new Dictionary<GraphNode, Block>();
            foreach (GraphNode g in exitNodes) {
              Contract.Assert(g != null);
              Block b = LoopUnrolling(g, visited, unrollable, prefix);
              _visited.Add(g, b);
            }
            newb = UnrollCurrentLoop(node, _visited, loopNodes, unrollable, prefix);
            visited.Add(node, newb);
          } else {
            BlockSeq newSuccs = new BlockSeq();
            foreach (GraphNode g in node.Succecessors) {
              Contract.Assert(g != null);
              newSuccs.Add(LoopUnrolling(g, visited, unrollable, prefix));
            }
            newb = new Block(node.Block.tok, node.Block.Label + prefix, node.Body, node.Block.TransferCmd);
            Block b;
            if (m_copyMap.TryGetValue(node.Block, out b)) {
              Contract.Assert(b != null);
              m_copyMap.Add(newb, b);
            } else {
              m_copyMap.Add(newb, node.Block);
            }


            Contract.Assert(newb != null);
            Contract.Assert(newb.TransferCmd != null);
            if (newSuccs.Length == 0)
              newb.TransferCmd = new ReturnCmd(newb.TransferCmd.tok);
            else
              newb.TransferCmd = new GotoCmd(newb.TransferCmd.tok, newSuccs);

            visited.Add(node, newb);
            Blocks.Add(newb);
            if (unrollable) {
              m_checkableBlocks.Add(newb);
            }
          }
        }
        Contract.Assert(newb != null);
        //newb.checkable = unrollable;
        return newb;
      }

      private Block UnrollCurrentLoop(GraphNode/*!*/ cutPoint, Dictionary<GraphNode, Block/*!*/>/*!*/ visited,
                  List<GraphNode/*!*/>/*!*/ loopNodes, bool unrollable, String/*!*/ prefix) {
        Contract.Requires(cutPoint != null);
        Contract.Requires(cce.NonNullElements(visited));
        Contract.Requires(cce.NonNullElements(loopNodes));
        Contract.Requires(prefix != null);
        if (unrollable) {
          Dictionary<GraphNode, Block> visited1 = new Dictionary<GraphNode, Block>(visited);
          Dictionary<GraphNode, Block> visited2 = new Dictionary<GraphNode, Block>(visited);
          Dictionary<GraphNode, Block> visited3 = new Dictionary<GraphNode, Block>(visited);

          Block loopend = ConstructLoopExitBlock(cutPoint, loopNodes, visited, prefix + "#Last");
          Contract.Assert(loopend != null);
          Block last = UnrollOnce(cutPoint, loopend, visited1, false, prefix + "#Last");
          Contract.Assert(last != null);
          AddHavocCmd(last, loopNodes);

          // You might use true for the unrollable flag as well. 					
          Block arb = UnrollOnce(cutPoint, last, visited2, false, prefix + "#Arb");
          Contract.Assert(arb != null);
          AddHavocCmd(arb, loopNodes);


          BlockSeq succ = new BlockSeq();
          succ.Add(last);
          succ.Add(arb);
          Contract.Assert(arb.TransferCmd != null);
          Block tmp = new Block(arb.tok, arb.Label + prefix + "#Dummy", new CmdSeq(), new GotoCmd(arb.TransferCmd.tok, succ));
          Contract.Assert(tmp != null);
          Blocks.Add(tmp);
          m_checkableBlocks.Add(tmp);

          // check if arb is already a copy of something else
          // if not then write to m_copyMap that tmp is a copy
          // of arb
          Block b = null;
          if (m_copyMap.TryGetValue(arb, out b)) {
            Contract.Assert(b != null);
            m_copyMap.Add(tmp, b);
          } else {
            m_copyMap.Add(tmp, arb);
          }

          Block first = UnrollOnce(cutPoint, tmp, visited3, false, prefix + "#First");
          Contract.Assert(first != null);

          return first;

        } else {
          Dictionary<GraphNode, Block> visited_ = new Dictionary<GraphNode, Block>(visited);
          Block loopend = AbstractIteration(cutPoint, prefix + "#UR");
          Block ret = UnrollOnce(cutPoint, loopend, visited_, false, prefix);
          AddHavocCmd(ret, loopNodes);
          return ret;
        }
      }

      private Block UnrollOnce(GraphNode node, Block nextIter, Dictionary<GraphNode, Block> visited, bool unrollable, String prefix) {
        Contract.Requires(node != null);
        Contract.Requires(nextIter != null);
        Contract.Requires(cce.NonNullElements(visited));
        Contract.Requires(prefix != null);


        Contract.Ensures(Contract.Result<Block>() != null);

        visited.Add(node, nextIter);
        Block newb, b;
        BlockSeq newSuccs = new BlockSeq();
        foreach (GraphNode g in node.Succecessors) {
          Contract.Assert(g != null);
          newSuccs.Add(LoopUnrolling(g, visited, unrollable, prefix));
        }
        newb = new Block(node.Block.tok, node.Block.Label + prefix, node.Body, node.Block.TransferCmd);
        if (m_copyMap.TryGetValue(node.Block, out b)) {
          Contract.Assert(b != null);
          m_copyMap.Add(newb, b);
        } else {
          m_copyMap.Add(newb, node.Block);
        }

        Contract.Assert(newb != null);
        Contract.Assert(newb.TransferCmd != null);
        if (newSuccs.Length == 0)
          newb.TransferCmd = new ReturnCmd(newb.TransferCmd.tok);
        else
          newb.TransferCmd = new GotoCmd(newb.TransferCmd.tok, newSuccs);

        Blocks.Add(newb);
        if (unrollable)
          m_checkableBlocks.Add(newb);
        return newb;
      }

      private Block AbstractIteration(GraphNode node, String prefix) {
        Contract.Requires(node != null);
        Contract.Requires(prefix != null);
        Contract.Ensures(Contract.Result<Block>() != null);

        CmdSeq body = new CmdSeq();
        foreach (Cmd c in node.Body) {
          Contract.Assert(c != null);
          if (c is PredicateCmd || c is CommentCmd)
            body.Add(c);
          else
            break;
        }
        body.Add(new AssumeCmd(node.Block.tok, Expr.False));
        TransferCmd tcmd = new ReturnCmd(node.Block.tok);
        Contract.Assert(tcmd != null);
        Block b = new Block(node.Block.tok, node.Block.Label + prefix, body, tcmd);
        Contract.Assert(b != null);
        Blocks.Add(b);
        Block tmp;
        if (m_copyMap.TryGetValue(node.Block, out tmp)) {
          Contract.Assert(tmp != null);
          m_copyMap.Add(b, tmp);
        } else {
          m_copyMap.Add(b, node.Block);
        }

        return b;
      }

      private Block ConstructLoopExitBlock(GraphNode cutPoint, List<GraphNode> loopNodes,
                          Dictionary<GraphNode, Block> visited, String prefix) {
        Contract.Requires(cutPoint != null);
        Contract.Requires(cce.NonNullElements(loopNodes));
        Contract.Requires(cce.NonNullElements(visited));
        Contract.Requires(prefix != null);

        Contract.Ensures(Contract.Result<Block>() != null);

        BlockSeq newSucc = new BlockSeq();
        Block orig = cutPoint.Block;

        // detect the block after the loop
        // FixMe: What happens when using break commands?
        foreach (GraphNode g in cutPoint.Succecessors) {
          Contract.Assert(g != null);
          if (!loopNodes.Contains(g)) {
            Block b;
            if (visited.TryGetValue(g, out b))
              newSucc.Add(b);
          }
        }
        TransferCmd tcmd;
        Contract.Assert(orig.TransferCmd != null);
        if (newSucc.Length == 0)
          tcmd = new ReturnCmd(orig.TransferCmd.tok);
        else
          tcmd = new GotoCmd(orig.TransferCmd.tok, newSucc);
        // FixMe: Genertate IToken for counterexample creation
        Block newb = new Block(orig.tok, orig.Label + prefix + "#Leave", orig.Cmds, tcmd);
        Contract.Assert(newb != null);
        Blocks.Add(newb);
        m_checkableBlocks.Add(newb);
        return newb;
      }


      private void GatherLoopBodyNodes(GraphNode current, GraphNode cutPoint, List<GraphNode> loopNodes) {
        Contract.Requires(current != null);
        Contract.Requires(cutPoint != null);
        Contract.Requires(cce.NonNullElements(loopNodes));
        loopNodes.Add(current);
        if (false)
          System.Diagnostics.Debugger.Break();
        foreach (GraphNode g in current.Predecessors) {
          Contract.Assert(g != null);
          if (cutPoint.firstPredecessor == g || g == cutPoint || loopNodes.Contains(g))
            continue;
          GatherLoopBodyNodes(g, cutPoint, loopNodes);
        }
      }

      private List<GraphNode> GatherLoopExitNodes(List<GraphNode> loopNodes) {
        Contract.Requires(cce.NonNullElements(loopNodes));
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<GraphNode>>()));
        List<GraphNode> exitnodes = new List<GraphNode>();

        foreach (GraphNode g in loopNodes) {
          Contract.Assert(g != null);
          foreach (GraphNode s in g.Succecessors) {
            Contract.Assert(s != null);
            if (!loopNodes.Contains(s) /*&& !exitnodes.Contains(s)*/ )
              exitnodes.Add(s);
          }
        }
        return exitnodes;
      }

      private void AddHavocCmd(Block b, List<GraphNode> loopNodes) {
        Contract.Requires(b != null);
        Contract.Requires(loopNodes != null);
        List<Block> loopBlocks = new List<Block>();
        foreach (GraphNode g in loopNodes) {
          Contract.Assert(g != null);
          loopBlocks.Add(g.Block);
        }
        HavocCmd hcmd = HavocLoopTargets(loopBlocks, b.tok);
        Contract.Assert(hcmd != null);
        CmdSeq body = new CmdSeq();
        body.Add(hcmd);
        body.AddRange(b.Cmds);
        b.Cmds = body;
      }

      private HavocCmd HavocLoopTargets(List<Block> bl, IToken tok) {
        Contract.Requires(bl != null);
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<HavocCmd>() != null);

        VariableSeq varsToHavoc = new VariableSeq();
        foreach (Block b in bl) {
          Contract.Assert(b != null);
          foreach (Cmd c in b.Cmds) {
            Contract.Assert(c != null);
            c.AddAssignedVariables(varsToHavoc);
          }
        }
        IdentifierExprSeq havocExprs = new IdentifierExprSeq();
        foreach (Variable v in varsToHavoc) {
          Contract.Assert(v != null);
          IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
          if (!havocExprs.Has(ie))
            havocExprs.Add(ie);
        }
        // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
        // the source location for this later on
        return new HavocCmd(tok, havocExprs);
      }

      #endregion


      #region GraphNode
      private class GraphNode {
        public readonly Block Block;
        public readonly CmdSeq Body;
        public bool IsCutPoint;  // is set during ComputeGraphInfo
        [Rep]
        public readonly List<GraphNode/*!*/>/*!*/ Predecessors = new List<GraphNode>();
        [Rep]
        public readonly List<GraphNode/*!*/>/*!*/ Succecessors = new List<GraphNode>();
        public GraphNode firstPredecessor;
        public List<GraphNode/*!*/>/*!*/ UnavoidableNodes = new List<GraphNode/*!*/>(); // should be done using a set

        [ContractInvariantMethod]
        void ObjectInvariant() {
          Contract.Invariant(Block != null);
          Contract.Invariant(Body != null);
          Contract.Invariant(cce.NonNullElements(Predecessors));
          Contract.Invariant(cce.NonNullElements(Succecessors));
          Contract.Invariant(cce.NonNullElements(UnavoidableNodes));
        }


        GraphNode(Block b, CmdSeq body) {
          Contract.Requires(b != null);
          Contract.Requires(body != null);
          Block = b;
          Body = body;
          IsCutPoint = false;

        }

        static CmdSeq GetOptimizedBody(CmdSeq cmds) {
          Contract.Requires(cmds != null);
          Contract.Ensures(Contract.Result<CmdSeq>() != null);

          int n = 0;
          foreach (Cmd c in cmds) {
            n++;
            PredicateCmd pc = c as PredicateCmd;
            if (pc != null && pc.Expr is LiteralExpr && ((LiteralExpr)pc.Expr).IsFalse) {
              // return a sequence consisting of the commands seen so far
              Cmd[] s = new Cmd[n];
              for (int i = 0; i < n; i++) {
                s[i] = cmds[i];
              }
              return new CmdSeq(s);
            }
          }
          return cmds;
        }

        private static List<GraphNode> Intersect(List<GraphNode> left, List<GraphNode> right) {
          Contract.Requires(left != null);
          Contract.Requires(right != null);
          Contract.Ensures(cce.NonNullElements(Contract.Result<List<GraphNode>>()));
          List<GraphNode> ret = new List<GraphNode>();
          List<GraphNode> tmp = left;
          tmp.AddRange(right);
          foreach (GraphNode gn in tmp) {
            Contract.Assert(gn != null);
            if (ret.Contains(gn))
              continue;
            if (left.Contains(gn) && right.Contains(gn))
              ret.Add(gn);
          }
          return ret;
        }

        public static GraphNode ComputeGraphInfo(GraphNode from, Block b, Dictionary<Block, GraphNode> gd, Set /*Block*/ beingVisited) {
          Contract.Requires(b != null);
          Contract.Requires(beingVisited != null);
          Contract.Requires(cce.NonNullElements(gd));

          Contract.Ensures(Contract.Result<GraphNode>() != null);

          GraphNode g;
          if (gd.TryGetValue(b, out g)) {
            Contract.Assume(from != null);
            Contract.Assert(g != null);

            g.UnavoidableNodes = Intersect(g.UnavoidableNodes, from.UnavoidableNodes);
            if (!g.UnavoidableNodes.Contains(g))
              g.UnavoidableNodes.Add(g);

            g.Predecessors.Add(from);
            if (g.firstPredecessor == null)
              g.firstPredecessor = from;

            if (beingVisited.Contains(b))
              g.IsCutPoint = true; // it's a cut point
          } else {
            CmdSeq body = GetOptimizedBody(b.Cmds);
            g = new GraphNode(b, body);
            gd.Add(b, g);
            if (from != null) {
              g.Predecessors.Add(from);
              if (from == null)
                g.firstPredecessor = g;

              if (g.firstPredecessor == null)
                g.firstPredecessor = from;

            }
            if (body != b.Cmds) {
              // the body was optimized -- there is no way through this block
            } else {
              beingVisited.Add(b);
              GotoCmd gcmd = b.TransferCmd as GotoCmd;
              if (gcmd != null) {
                Contract.Assume(gcmd.labelTargets != null);
                foreach (Block succ in gcmd.labelTargets) {
                  Contract.Assert(succ != null);
                  g.Succecessors.Add(ComputeGraphInfo(g, succ, gd, beingVisited));
                }
              }
              beingVisited.Remove(b);
            }
          }
          return g;
        }
      }

    }
      #endregion

    #endregion

    #region Program Passification
    private void GenerateReachVars(Implementation impl) {
      Contract.Requires(impl != null);
      Hashtable gotoCmdOrigins = new Hashtable();
      Block exitBlock = GenerateUnifiedExit(impl, gotoCmdOrigins);
      Contract.Assert(exitBlock != null);

      AddBlocksBetween(impl.Blocks);

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
        foreach (Variable lvar in impl.LocVars) {
          Contract.Assert(lvar != null);
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
      GenerateReachabilityPredicates(impl, exitBlock);
    }


    private Hashtable/*TransferCmd->ReturnCmd*/ PassifyProgram(Implementation impl) {
      Contract.Requires(impl != null);
      Contract.Ensures(Contract.Result<Hashtable>() != null);

      CurrentLocalVariables = impl.LocVars;
      Convert2PassiveCmd(impl);
      return new Hashtable();
    }

    /// <summary>
    /// Add additional variable to allow checking as described in the paper
    /// "It's doomed; we can prove it"
    /// </summary>
    private void GenerateReachabilityPredicates(Implementation impl, Block exitBlock) {
      Contract.Requires(impl != null);
      Contract.Requires(exitBlock != null);
      ExprSeq es = new ExprSeq();
      Cmd eblockcond = null;

      foreach (Block b in impl.Blocks) {
        Contract.Assert(b != null);
        //if (b.Predecessors.Length==0) continue;
        //if (b.Cmds.Length == 0 ) continue;

        Variable v_ = new LocalVariable(Token.NoToken,
                                new TypedIdent(b.tok, b.Label + reachvarsuffix, new BasicType(SimpleType.Bool)));

        impl.LocVars.Add(v_);

        m_BlockReachabilityMap[b] = v_;

        IdentifierExpr lhs = new IdentifierExpr(b.tok, v_);
        Contract.Assert(lhs != null);

        es.Add(new IdentifierExpr(b.tok, v_));

        List<AssignLhs> lhsl = new List<AssignLhs>();
        lhsl.Add(new SimpleAssignLhs(Token.NoToken, lhs));
        List<Expr> rhsl = new List<Expr>();
        rhsl.Add(Expr.True);

        if (b != exitBlock) {
          CmdSeq cs = new CmdSeq(new AssignCmd(Token.NoToken, lhsl, rhsl));
          cs.AddRange(b.Cmds);
          b.Cmds = cs;
        } else {
          eblockcond = new AssignCmd(Token.NoToken, lhsl, rhsl);
        }

        //checkBlocks.Add(new CheckableBlock(v_,b));
      }
      if (es.Length == 0)
        return;

      Expr aexp = null;

      if (es.Length == 1) {
        aexp = es[0];
      } else if (es.Length == 2) {
        aexp = Expr.Binary(Token.NoToken,
            BinaryOperator.Opcode.And,
            cce.NonNull(es[0]),
            cce.NonNull(es[1]));
      } else {
        aexp = Expr.True;
        foreach (Expr e_ in es) {
          aexp = Expr.Binary(Token.NoToken,
              BinaryOperator.Opcode.And,
              cce.NonNull(e_), aexp);
        }
      }
      Contract.Assert(aexp != null);
      Contract.Assert(eblockcond != null);

      AssumeCmd ac = new AssumeCmd(Token.NoToken, aexp);

      Contract.Assert(exitBlock != null);

      CmdSeq cseq = new CmdSeq(eblockcond);
      cseq.AddRange(exitBlock.Cmds);
      cseq.Add(ac);

      exitBlock.Cmds = cseq;
    }

    #endregion

  }
}
