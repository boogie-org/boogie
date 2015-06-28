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
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC {
  public partial class DCGen : ConditionGeneration {
      private bool _print_time = CommandLineOptions.Clo.DoomStrategy!=-1;
    #region Attributes
    static private Dictionary<Block, Variable/*!*/>/*!*/ m_BlockReachabilityMap;
    Dictionary<Block/*!*/, Block/*!*/>/*!*/ m_copiedBlocks = new Dictionary<Block/*!*/, Block/*!*/>();
    const string reachvarsuffix = "__ivebeenthere";
    List<Cmd/*!*/>/*!*/ m_doomedCmds = new List<Cmd/*!*/>();
    [ContractInvariantMethod]
    void ObjectInvariant() {

    }

    #endregion


    /// <summary>
    /// Constructor.  Initializes the theorem prover.
    /// </summary>
    public DCGen(Program program, string/*?*/ logFilePath, bool appendLogFile, List<Checker> checkers)
      : base(program, checkers) {
      Contract.Requires(program != null);

      this.appendLogFile = appendLogFile;
      this.logFilePath = logFilePath;
      m_BlockReachabilityMap = new Dictionary<Block, Variable>();
    }

    /// <summary>
    /// Debug method that prints a dot file of the 
    /// current set of blocks in impl to filename. 
    /// </summary>
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
        if (gc != null)
        {
            Contract.Assert(gc.labelTargets != null);
            foreach (Block b_ in gc.labelTargets)
            {
                Contract.Assert(b_ != null);
                edges.Add(String.Format("\"{0}\" -> \"{1}\";", b.Label, b_.Label));
            }
        }

        //foreach (Block b_ in b.Predecessors)
        //{              
        //    edges.Add(String.Format("\"{0}\" -> \"{1}\";", b.Label, b_.Label));
        //}
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
    private const string _copyPrefix = "CPY__";

    private List<Block> m_UncheckableBlocks = null;

      /// <summary>
    /// MSchaef: 
    /// - remove loops and add reach variables
    /// - make it a passive program
    /// - compute the wlp for each block
    /// - check if |= (reach=false) => wlp.S.false holds for each reach
    ///
    /// </summary>
    public override Outcome VerifyImplementation(Implementation impl, VerifierCallback callback) {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      
      Console.WriteLine();
      Console.WriteLine("Checking function {0}", impl.Name);
      callback.OnProgress("doomdetector", 0, 0, 0);

      bool restartTP = CommandLineOptions.Clo.DoomRestartTP ;

      //Impl2Dot(impl, String.Format("c:/dot/{0}_orig.dot", impl.Name));      

      Transform4DoomedCheck(impl);

      //Impl2Dot(impl, String.Format("c:/dot/{0}_fin.dot", impl.Name));
    
      Checker checker = FindCheckerFor(1000);
      Contract.Assert(checker != null);
      int assertionCount;
      DoomCheck dc = new DoomCheck(impl, this.exitBlock, checker, m_UncheckableBlocks, out assertionCount);
      CumulativeAssertionCount += assertionCount;

      //EmitImpl(impl, false);
      
      int _totalchecks = 0;

      ProverInterface.Outcome outcome;
      dc.ErrorHandler = new DoomErrorHandler(dc.Label2Absy, callback);

      System.TimeSpan ts = new TimeSpan();
      
      if (_print_time) Console.WriteLine("Total number of blocks {0}", impl.Blocks.Count);

      List<Block> lb;
      List<Variable> lv = new List<Variable>();
      
      while (dc.GetNextBlock(out lb))
      {
        Contract.Assert(lb != null);
        outcome = ProverInterface.Outcome.Undetermined;
        
        Variable v = null;
        lv.Clear();

        foreach (Block b_ in lb)
        {
            if (!m_BlockReachabilityMap.TryGetValue(b_, out v))
            {
                // This should cause an error
                continue;
            }
            //Console.Write("{0}, ",b_.Label);
            lv.Add(v);
        }
        //Console.WriteLine();
        Dictionary<Expr, int> finalreachvars = m_GetPostconditionVariables(impl.Blocks,lb);
        if (lv.Count < 1)
        {
            
            continue;
        }

        Contract.Assert(lv != null);
        _totalchecks++;


        if (!dc.CheckLabel(lv,finalreachvars, out outcome)) {
          return Outcome.Inconclusive;
        }
        ts += dc.DEBUG_ProverTime.Elapsed;

        if (restartTP)
        {
            checker.Close();
            checker = FindCheckerFor(1000);
            dc.RespawnChecker(impl, checker);
            dc.ErrorHandler = new DoomErrorHandler(dc.Label2Absy, callback);
        }

      }
      checker.Close();

      if (_print_time)
      {
          Console.WriteLine("Number of Checkes / #Blocks: {0} of {1}", _totalchecks, impl.Blocks.Count);
          dc.__DEBUG_PrintStatistics();
          Console.WriteLine("Total time for this method: {0}", ts.ToString());
      }
      #region Try to produce a counter example (brute force)
      if (dc.DoomedSequences.Count > 0) {
          int counter = 0;
          List<Block> _all = new List<Block>();
          foreach (List<Block> lb_ in dc.DoomedSequences)
          {              
              foreach (Block b_ in lb_)
              {
                  if (!_all.Contains(b_) && !m_UncheckableBlocks.Contains(b_)) 
                  { 
                      _all.Add(b_); counter++;
                      if (!_print_time)  Console.WriteLine(b_.Label);
                  }
              }
          }
          if (_all.Count > 0)
          {
              Console.WriteLine("#Dead Blocks found: {0}:  ", counter);
              return Outcome.Errors;
          }
      }
      #endregion


      return Outcome.Correct;
    }

    private Dictionary<Expr, int> m_GetPostconditionVariables(List<Block> allblock,  List<Block> passBlock)
    {
        Dictionary<Expr, int> r = new Dictionary<Expr, int>();        
        foreach (Block b in allblock)
        {            
            Variable v;
            if (m_BlockReachabilityMap.TryGetValue(b, out v))
            {
                if (passBlock.Contains(b))   r[m_LastReachVarIncarnation[v]] = 1;
            }
            else
            {
                Console.WriteLine("there is no reachability variable for {0}", b.Label);
            }
        }
        return r;
    }

#if false
    #region Error message construction
    private void SearchCounterexample(Implementation impl, DoomErrorHandler errh, VerifierCallback callback) {
      Contract.Requires(impl != null);
      Contract.Requires(errh != null);
      Contract.Requires(callback != null);
      Contract.Requires(errh.m_Reachvar != null);
      //if (errh.m_Reachvar==null) {
      //    Contract.Assert(false);throw new cce.UnreachableException();
      //}
      m_doomedCmds.Clear();

      Dictionary<Block, List<Cmd>> cmdbackup = new Dictionary<Block, List<Cmd>>();

      BruteForceCESearch(errh.m_Reachvar, impl, callback, cmdbackup, 0, impl.Blocks.Count / 2 - 1);
      BruteForceCESearch(errh.m_Reachvar, impl, callback, cmdbackup, impl.Blocks.Count / 2, impl.Blocks.Count - 1);

      List<Cmd> causals = CollectCausalStatements(impl.Blocks[0]);
      foreach (Cmd c in causals) {
        Contract.Assert(c != null);
        GenerateErrorMessage(c, causals);
      }

      #region Undo all modifications
      foreach (KeyValuePair<Block, List<Cmd>> kvp in cmdbackup) {
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
                        Dictionary<Block, List<Cmd>> cmdbackup, int startidx, int endidx) {
      Contract.Requires(reachvar != null);
      Contract.Requires(impl != null);
      Contract.Requires(callback != null);
      Contract.Requires(cce.NonNullElements(cmdbackup));
      #region Modify implementation
      for (int i = startidx; i <= endidx; i++) {
        if (_copiedBlock.Contains(impl.Blocks[i]))
          continue;
        List<Cmd> cs = new List<Cmd>();
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
      List<Cmd> backup = b.Cmds;
      Contract.Assert(backup != null);
      List<Cmd> cs = new List<Cmd>();
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
    }

    void UndoBlockModifications(Implementation impl, Dictionary<Block/*!*/, List<Cmd>/*!*/>/*!*/ cmdbackup,
                                int startidx, int endidx) {
      Contract.Requires(cce.NonNullElements(cmdbackup));
      Contract.Requires(impl != null);
      for (int i = startidx; i <= endidx; i++) {
        List<Cmd> cs = null;
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
      DoomCheck dc = new DoomCheck(impl, this.exitBlock,  checker, m_UncheckableBlocks);
      dc.ErrorHandler = new DoomErrorHandler(dc.Label2Absy, callback);
      outcome = ProverInterface.Outcome.Undetermined;
      List<Variable> rv = new List<Variable>();
      rv.Add(reachvar);
      if (!dc.CheckLabel(rv,null, out outcome)) {
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
#endregion
#endif


    Block exitBlock;

    #region Program Passification
    private void GenerateHelperBlocks(Implementation impl) {
      Contract.Requires(impl != null);
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins = new Dictionary<TransferCmd, ReturnCmd>();
      exitBlock = GenerateUnifiedExit(impl, gotoCmdOrigins);
      Contract.Assert(exitBlock != null);

      AddBlocksBetween(impl.Blocks);

      #region Insert pre- and post-conditions and where clauses as assume and assert statements
      {
        List<Cmd> cc = new List<Cmd>();
        // where clauses of global variables
        foreach (var gvar in program.GlobalVariables) {
          if (gvar.TypedIdent.WhereExpr != null) {
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
        InjectPostConditions(impl, exitBlock, gotoCmdOrigins);
      }
      #endregion     
    }


    private Dictionary<Variable, Expr> PassifyProgram(Implementation impl, ModelViewInfo mvInfo) {
      Contract.Requires(impl != null);
      Contract.Requires(mvInfo != null);
      Contract.Requires(this.exitBlock != null);
      Contract.Ensures(Contract.Result<Hashtable>() != null);
      
      CurrentLocalVariables = impl.LocVars;
      return Convert2PassiveCmd(impl, mvInfo);
      //return new Hashtable();
    }

    /// <summary>
    /// Add additional variable to allow checking as described in the paper
    /// "It's doomed; we can prove it"
    /// </summary>
    private List<Cmd> GenerateReachabilityPredicates(Implementation impl)
    {
        Contract.Requires(impl != null);        
        
        foreach (Block b in impl.Blocks)
        {
            Contract.Assert(b != null);
            //if (b.Predecessors.Length==0) continue;
            //if (b.Cmds.Length == 0 ) continue;
            
            Variable v_ = new LocalVariable(Token.NoToken,
                                    new TypedIdent(b.tok, b.Label + reachvarsuffix, new BasicType(SimpleType.Int )));

            impl.LocVars.Add(v_);                      
            
            m_BlockReachabilityMap[b] = v_;

            IdentifierExpr lhs = new IdentifierExpr(b.tok, v_);
            Contract.Assert(lhs != null);

            impl.Proc.Modifies.Add(lhs);
          
            List<AssignLhs> lhsl = new List<AssignLhs>();
            lhsl.Add(new SimpleAssignLhs(Token.NoToken, lhs));
            List<Expr> rhsl = new List<Expr>();
            rhsl.Add(Expr.Literal(1) );
            

            List<Cmd> cs = new List<Cmd> { new AssignCmd(Token.NoToken, lhsl, rhsl) };
            cs.AddRange(b.Cmds);
            b.Cmds = cs;

            //checkBlocks.Add(new CheckableBlock(v_,b));
        }

        List<Cmd> incReachVars = new List<Cmd>();
        foreach (KeyValuePair<Block, Variable> kvp in m_BlockReachabilityMap)
        {
            IdentifierExpr lhs = new IdentifierExpr(Token.NoToken, kvp.Value);
            impl.Proc.Modifies.Add(lhs);
            incReachVars.Add(new AssumeCmd(Token.NoToken, Expr.Le(lhs, Expr.Literal(1))));                        
        }

        return incReachVars;
    }
 
    #endregion

    #region Compute loop-free approximation

    // this might be redundant, but I didn't find a better place to get this information.     
    private Dictionary<Variable, Expr> m_LastReachVarIncarnation = new Dictionary<Variable, Expr>();

    private void Transform4DoomedCheck(Implementation impl)
    {
        variable2SequenceNumber = new Dictionary<Variable, int>();
        incarnationOriginMap = new Dictionary<Incarnation, Absy>();
        if (impl.Blocks.Count < 1) return;

        impl.PruneUnreachableBlocks();
        AddBlocksBetween(impl.Blocks);
        ResetPredecessors(impl.Blocks);        

        GraphAnalyzer ga = new GraphAnalyzer(impl.Blocks);
        LoopRemover lr = new LoopRemover(ga);
        lr.AbstractLoopUnrolling();

        impl.Blocks = ga.ToImplementation(out m_UncheckableBlocks);
        ResetPredecessors(impl.Blocks);

        // Check for the "BlocksBetween" if all their successors are in m_UncheckableBlocks
        List<Block> oldblocks = new List<Block>();
        oldblocks.AddRange(impl.Blocks);       
        GenerateHelperBlocks(impl);
        #region Check for the "BlocksBetween" if all their successors are in m_UncheckableBlocks
        foreach (Block b in impl.Blocks)
        {
            if (oldblocks.Contains(b)) continue;
            GotoCmd gc = b.TransferCmd as GotoCmd;
            if (gc != null)
            {
                bool allsuccUncheckable = true;
                foreach (Block _b in gc.labelTargets)
                {
                    if (!m_UncheckableBlocks.Contains(_b))
                    {
                        allsuccUncheckable = false; break;
                    }
                }
                if (allsuccUncheckable && !m_UncheckableBlocks.Contains(b)) m_UncheckableBlocks.Add(b);
            }
        }
        #endregion

        impl.Blocks = DeepCopyBlocks(impl.Blocks, m_UncheckableBlocks);

        m_BlockReachabilityMap = new Dictionary<Block, Variable>();       
        List<Cmd> cs = GenerateReachabilityPredicates(impl);
        
        //foreach (Block test in getTheFFinalBlock(impl.Blocks[0]))
        //{
        //    test.Cmds.AddRange(cs);
        //}
        
        ResetPredecessors(impl.Blocks);
        //EmitImpl(impl,false);

        Dictionary<Variable, Expr> var2Expr = PassifyProgram(impl, new ModelViewInfo(program, impl));

        // Collect the last incarnation of each reachability variable in the passive program
        foreach (KeyValuePair<Block, Variable> kvp in m_BlockReachabilityMap)
        {
            if (var2Expr.ContainsKey(kvp.Value))
            {
                m_LastReachVarIncarnation[kvp.Value] = (Expr)var2Expr[kvp.Value];
            }
        }
    }


    List<Block> getTheFFinalBlock(Block b)
    {
        List<Block> lb = new List<Block>();
        GotoCmd gc = b.TransferCmd as GotoCmd;
        if (gc == null) lb.Add(b);
        else
        {
            foreach (Block s in gc.labelTargets)
            {
                foreach (Block r in getTheFFinalBlock(s)) if (!lb.Contains(r)) lb.Add(r);
            }
        }
        return lb;
    }


    private List<Block> DeepCopyBlocks(List<Block> lb, List<Block> uncheckables)
    {
        List<Block> clones = new List<Block>();
        List<Block> uncheck_ = new List<Block>();
        Dictionary<Block, Block> clonemap = new Dictionary<Block, Block>();

        foreach (Block b in lb)
        {
            Block clone = CloneBlock(b);
            clones.Add(clone);
            clonemap[b] = clone;
            if (uncheckables.Contains(b)) uncheck_.Add(clone);
        }
        uncheckables.Clear();
        uncheckables.AddRange(uncheck_);
        // update the successors and predecessors
        foreach (Block b in lb)
        {
            List<Block> newpreds = new List<Block>();
            foreach (Block b_ in b.Predecessors)
            {
                newpreds.Add(clonemap[b_]);
            }
            clonemap[b].Predecessors = newpreds;
            GotoCmd gc = b.TransferCmd as GotoCmd;
            ReturnCmd rc = b.TransferCmd as ReturnCmd;
            if (gc != null)
            {
                List<String> lseq = new List<String>();
                List<Block> bseq = new List<Block>();
                foreach (string s in gc.labelNames) lseq.Add(s);
                foreach (Block b_ in gc.labelTargets) bseq.Add(clonemap[b_]);
                GotoCmd tcmd = new GotoCmd(gc.tok, lseq, bseq);
                clonemap[b].TransferCmd = tcmd;
            }
            else if (rc != null)
            {
                clonemap[b].TransferCmd = new ReturnCmd(rc.tok);
            }
        }
        return clones;
    }

    private Block CloneBlock(Block b)
    {
        Block clone = new Block(b.tok, b.Label, b.Cmds, b.TransferCmd);
        if (this.exitBlock == b) this.exitBlock = clone;
        return clone;
    }
    #endregion
  }
}
