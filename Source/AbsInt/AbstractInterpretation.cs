//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

namespace Microsoft.Boogie.AbstractInterpretation {
  using System;
  using System.Collections;
  using System.Collections.Generic;
  using System.Diagnostics;
  using System.Diagnostics.Contracts;
  using Microsoft.Boogie;
  using System.Linq;
  using AI = Microsoft.AbstractInterpretationFramework;


  /// <summary>
  /// Defines invariant propagation methods over ASTs for an abstract interpretation policy.
  /// </summary>
  public class AbstractionEngine {
    private AI.Lattice lattice;
    private Queue<ProcedureWorkItem> procWorkItems;  //PM: changed to generic queue
    private Queue/*<CallSite>*/ callReturnWorkItems;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(lattice != null);
      Contract.Invariant(procWorkItems != null);
      Contract.Invariant(callReturnWorkItems != null);
    }


    private class ProcedureWorkItem {
      [Rep]  // KRML: this doesn't seem like the right designation to me; but I'm not sure what is
      public Procedure Proc;

      public int Index; // pre state is Impl.Summary[Index]
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Proc != null);
        Contract.Invariant(0 <= Index && Index < Proc.Summary.Count);
        Contract.Invariant(log != null);
      }

      public ProcedureWorkItem([Captured] Procedure p, AI.Lattice.Element v, AI.Lattice lattice) {
        Contract.Requires(p != null);
        Contract.Requires(v != null);
        Contract.Requires(lattice != null);

        Contract.Ensures(p == Proc);
        this.Proc = p;
        p.Summary.Add(new ProcedureSummaryEntry(lattice, v));
        this.Index = p.Summary.Count - 1;
        // KRML: axioms are now in place:  assume 0 <= Index && Index < Proc.Summary.Count; //PM: Should not be necessary once axioms for pure methods are there
      }
    }

    private readonly static AI.Logger log = new AI.Logger("Engine");


    public AbstractionEngine(AI.Lattice lattice) {
      Contract.Requires(lattice != null);
      Contract.Assume(cce.IsExposable(log)); //PM: One would need static class invariants to prove this property
      cce.BeginExpose(log);
      log.Enabled = AI.Lattice.LogSwitch;
      cce.EndExpose();
      this.lattice = lattice;
      this.procWorkItems = new Queue<ProcedureWorkItem>();
      this.callReturnWorkItems = new Queue();
    }

    private Dictionary<Procedure, Implementation[]> ComputeProcImplMap(Program program) {
      Contract.Requires(program != null);
      // Since implementations call procedures (impl. signatures) 
      // rather than directly calling other implementations, we first
      // need to compute which implementations implement which
      // procedures and remember which implementations call which
      // procedures.

      return program
            .TopLevelDeclarations
            .Where(d => d is Implementation).Select(i => (Implementation)i)
            .GroupBy(i => i.Proc).Select(g => g.ToArray()).ToDictionary(a => a[0].Proc);

    }

    public AI.Lattice.Element ApplyProcedureSummary(CallCmd call, Implementation caller, AI.Lattice.Element knownAtCallSite, CallSite callSite) {
      Contract.Requires(call.Proc != null);
      Contract.Requires(call != null);
      Contract.Requires(caller != null);
      Contract.Requires(knownAtCallSite != null);
      Contract.Requires(callSite != null);

      Contract.Ensures(Contract.Result<AI.Lattice.Element>() != null);
      Procedure proc = call.Proc;//Precondition required that call.Proc !=null, therefore no assert necessarry.

      // NOTE: Here, we count on the fact that an implementation's variables
      // are distinct from an implementation's procedure's variables. So, even for
      // a recursive implementation, we're free to use the implementation's
      // procedure's input parameters as though they were temporary local variables.
      //
      // Hence, in the program
      //    procedure Foo (i:int);  implementation Foo (i':int) { ...call Foo(i'+1)... }
      // we can treat the recursive call as
      //    i:=i'+1; call Foo(i);
      // where the notation i' means a variable with the same (string) name as i, 
      // but a different identity.

      AI.Lattice.Element relevantToCall = knownAtCallSite; //Precondition of the method implies that this can never be null, therefore no need for an assert.
      for (int i = 0; i < proc.InParams.Length; i++) {
        // "Assign" the actual expressions to the corresponding formal variables.
        Contract.Assume(proc.InParams[i] != null);  //PM: this can be fixed once VariableSeq is replaced by List<Variable!>;
        Contract.Assume(call.Ins[i] != null);       //PM: this can be fixed once VariableSeq is replaced by List<Variable!>;
        Expr equality = Expr.Eq(Expr.Ident(cce.NonNull(proc.InParams[i])), cce.NonNull(call.Ins[i]));
        relevantToCall = lattice.Constrain(relevantToCall, equality.IExpr);
      }
      foreach (Variable var in caller.LocVars) {
        Contract.Assert(var != null);
        relevantToCall = this.lattice.Eliminate(relevantToCall, var);
      }

      ProcedureSummary summary = proc.Summary;
      Contract.Assert(summary != null);
      ProcedureSummaryEntry applicableEntry = null;

      for (int i = 0; i < summary.Count; i++) {
        ProcedureSummaryEntry current = cce.NonNull(summary[i]);

        if (lattice.Equivalent(current.OnEntry, relevantToCall)) {
          applicableEntry = current;
          break;
        }
      }

      // Not found in current map, so add new entry.
      if (applicableEntry == null) {
        ProcedureWorkItem newWorkItem = new ProcedureWorkItem(proc, relevantToCall, lattice);
        Contract.Assert(newWorkItem != null);
        this.procWorkItems.Enqueue(newWorkItem);
        applicableEntry = cce.NonNull(proc.Summary[newWorkItem.Index]);
      }
      applicableEntry.ReturnPoints.Add(callSite);


      AI.Lattice.Element atReturn = applicableEntry.OnExit;

      for (int i = 0; i < call.Outs.Count; i++) {
        atReturn = this.lattice.Rename(atReturn, cce.NonNull(call.Proc.OutParams[i]), cce.NonNull(cce.NonNull(call.Outs[i]).Decl));
        knownAtCallSite = this.lattice.Eliminate(knownAtCallSite, cce.NonNull(cce.NonNull(call.Outs[i]).Decl));
      }

      return this.lattice.Meet(atReturn, knownAtCallSite);
    }

      /*
    private Cci.IGraphNavigator callGraph;
    public Cci.IGraphNavigator CallGraph {
      get {
        return this.callGraph;
      }
    }
      */

    /// <summary>
    /// Compute the invariants for the program using the underlying abstract domain
    /// </summary>
    public void ComputeProgramInvariants(Program program) {
      Contract.Requires(program != null);

      Dictionary<Procedure, Implementation[]> procedureImplementations = ComputeProcImplMap(program);
      //the line above, ergo there is no need for
      //an assert after this statement to maintain
      //the non-null type.
      AI.Lattice.Element initialElement = this.lattice.Top;
      Contract.Assert(initialElement != null);
      // Gather all the axioms to create the initial lattice element
      // Differently stated, it is the \alpha from axioms (i.e. first order formulae) to the underlyng abstract domain

      foreach (Declaration decl in program.TopLevelDeclarations) {
        Axiom ax = decl as Axiom;
        if (ax != null) {
          initialElement = this.lattice.Constrain(initialElement, ax.Expr.IExpr);
        }
      }

      // propagate over all procedures...
      foreach (Declaration decl in program.TopLevelDeclarations) {
        Procedure proc = decl as Procedure;
        if (proc != null) {
          this.procWorkItems.Enqueue(new ProcedureWorkItem(proc, initialElement, this.lattice));
        }
      }

      // analyze all the procedures...
      while (this.procWorkItems.Count + this.callReturnWorkItems.Count > 0) {
        while (this.procWorkItems.Count > 0) {
          ProcedureWorkItem workItem = this.procWorkItems.Dequeue();

          ProcedureSummaryEntry summaryEntry = cce.NonNull(workItem.Proc.Summary[workItem.Index]);
          if (!procedureImplementations.ContainsKey(workItem.Proc)) {
            // This procedure has no given implementations.  We therefore treat the procedure
            // according to its specification only.

            if (!CommandLineOptions.Clo.IntraproceduralInfer) {
              AI.Lattice.Element post = summaryEntry.OnEntry;
              // BUGBUG.  Here, we should process "post" according to the requires, modifies, ensures
              // specification of the procedure, including any OLD expressions in the postcondition.
              AI.Lattice.Element atReturn = post;

              if (!this.lattice.LowerThan(atReturn, summaryEntry.OnExit)) {
                // If the results of this analysis are strictly worse than
                // what we previous knew for the same input assumptions,
                // update the summary and re-do the call sites.

                summaryEntry.OnExit = this.lattice.Join(summaryEntry.OnExit, atReturn);

                foreach (CallSite callSite in summaryEntry.ReturnPoints) {
                  this.callReturnWorkItems.Enqueue(callSite);
                }
              }
            }
          } else {
            // There are implementations, so do inference based on those implementations

            if (!CommandLineOptions.Clo.IntraproceduralInfer) {
              summaryEntry.OnExit = lattice.Bottom;
            }

            // For each implementation in the procedure...
            foreach (Implementation impl in cce.NonNull(procedureImplementations[workItem.Proc])) {
              // process each procedure implementation by recursively processing the first (entry) block...
              cce.NonNull(impl.Blocks[0]).Lattice = lattice;
              ComputeBlockInvariants(impl, cce.NonNull(impl.Blocks[0]), summaryEntry.OnEntry, summaryEntry);
              AdjustProcedureSummary(impl, summaryEntry);
            }
          }
        }


        while (this.callReturnWorkItems.Count > 0) {
          CallSite callSite = cce.NonNull((CallSite)this.callReturnWorkItems.Dequeue());

          PropagateStartingAtStatement(callSite.Impl, callSite.Block, callSite.Statement, callSite.KnownBeforeCall, callSite.SummaryEntry);
          AdjustProcedureSummary(callSite.Impl, callSite.SummaryEntry);
        }

      } // both queues

    }

    void AdjustProcedureSummary(Implementation impl, ProcedureSummaryEntry summaryEntry) {
      Contract.Requires(impl != null);
      Contract.Requires(summaryEntry != null);
      if (CommandLineOptions.Clo.IntraproceduralInfer) {
        return;  // no summary to adjust
      }

      // compute the procedure invariant by joining all terminal block invariants...
      AI.Lattice.Element post = lattice.Bottom;
      foreach (Block block in impl.Blocks) {
        if (block.TransferCmd is ReturnCmd) {
          // note: if program control cannot reach this block, then postValue will be null
          if (block.PostInvariant != null) {
            post = (AI.Lattice.Element)lattice.Join(post, block.PostInvariant);
          }
        }
      }

      AI.Lattice.Element atReturn = post;
      foreach (Variable var in impl.LocVars) {
        Contract.Assert(var != null);
        atReturn = this.lattice.Eliminate(atReturn, var);
      }
      foreach (Variable var in impl.InParams) {
        Contract.Assert(var != null);
        atReturn = this.lattice.Eliminate(atReturn, var);
      }

      if (!this.lattice.LowerThan(atReturn, summaryEntry.OnExit)) {
        // If the results of this analysis are strictly worse than
        // what we previous knew for the same input assumptions,
        // update the summary and re-do the call sites.

        summaryEntry.OnExit = this.lattice.Join(summaryEntry.OnExit, atReturn);

        foreach (CallSite callSite in summaryEntry.ReturnPoints) {
          Contract.Assert(callSite != null);
          this.callReturnWorkItems.Enqueue(callSite);
        }
      }
    }

    private static int freshVarId = 0;
    private static Variable FreshVar(Boogie.Type ty) {
      Contract.Requires(ty != null);
      Contract.Ensures(Contract.Result<Variable>() != null);

      Variable fresh = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "fresh" + freshVarId, ty));
      freshVarId++;
      return fresh;
    }

    private delegate CallSite/*!*/ MarkCallSite(AI.Lattice.Element/*!*/ currentValue);

    /// <summary>
    /// Given a basic block, it propagates the abstract state at the entry point through the exit point of the block
    /// <param name="impl"> The implementation that owns the block </param>
    /// <param name="block"> The from where we propagate </param>
    /// <param name="statementIndex">  </param> 
    /// <param name="currentValue"> The initial value </param>
    /// </summary>
    private void PropagateStartingAtStatement(Implementation/*!*/ impl, Block/*!*/ block, int statementIndex, AI.Lattice.Element/*!*/ currentValue,
                                               ProcedureSummaryEntry/*!*/ summaryEntry) {
      Contract.Requires(impl != null);
      Contract.Requires(block != null);
      Contract.Requires(currentValue != null);
      Contract.Requires(summaryEntry != null);
      Contract.Assume(cce.IsPeerConsistent(log));
      log.DbgMsg(string.Format("{0}:", block.Label));
      log.DbgMsgIndent();

      #region Apply the abstract transition relation to the statements in the block
      for (int cmdIndex = statementIndex; cmdIndex < block.Cmds.Length; cmdIndex++) {
        Cmd cmd = cce.NonNull(block.Cmds[cmdIndex]);              // Fetch the command
        currentValue = Step(cmd, currentValue, impl,      // Apply the transition function
                            delegate(AI.Lattice.Element cv) {
                              Contract.Requires(cv != null);
                              return new CallSite(impl, block, cmdIndex, cv, summaryEntry);
                            }
                           );
      }

      block.PostInvariant = currentValue;      // The invariant at the exit point of the block is that of the last statement

      log.DbgMsg(string.Format("pre   {0}", cce.NonNull(block.PreInvariant).ToString()));
      log.DbgMsg(string.Format("post  {0}", (block.PostInvariant).ToString()));
      log.DbgMsgUnindent();
      #endregion
      #region Propagate the post-condition to the successor nodes
      GotoCmd @goto = block.TransferCmd as GotoCmd;
      if (@goto != null) {
        // labelTargets is non-null after calling Resolve in a prior phase.
        Contract.Assume(@goto.labelTargets != null);

        // For all the successors of this block, propagate the abstract state
        foreach (Block succ in @goto.labelTargets) {
          Contract.Assert(succ != null);
          if (impl.Blocks.Contains(succ)) {
            succ.Lattice = block.Lattice;         // The lattice is the same
            // Propagate the post-abstract state of this block to the successor
            ComputeBlockInvariants(impl, succ, block.PostInvariant, summaryEntry);
          }
        }
      }
      #endregion
    }

    /// <summary>
    /// The abstract transition relation.
    /// </summary>
    private AI.Lattice.Element Step(Cmd cmd, AI.Lattice.Element pre, Implementation impl, MarkCallSite/*?*/ callSiteMarker) {
      Contract.Requires(cmd != null);
      Contract.Requires(pre != null);
      Contract.Requires(impl != null);
      Contract.Ensures(Contract.Result<AI.Lattice.Element>() != null);

      Contract.Assume(cce.IsPeerConsistent(log));
      log.DbgMsg(string.Format("{0}", cmd));
      log.DbgMsgIndent();

      AI.Lattice.Element currentValue = pre;//Nonnullability was a precondition

      // Case split...
      #region AssignCmd
      if (cmd is AssignCmd) { // parallel assignment
        // we first eliminate map assignments
        AssignCmd assmt = cce.NonNull((AssignCmd)cmd).AsSimpleAssignCmd;
        //PM: Assume variables have been resolved
        Contract.Assume(Contract.ForAll<AssignLhs>(assmt.Lhss, lhs => lhs.DeepAssignedVariable != null));//TODO: Check my work, please, Mike.

        List<IdentifierExpr/*!>!*/> freshLhs = new List<IdentifierExpr/*!*/>();
        foreach (AssignLhs lhs in assmt.Lhss) {
          Contract.Assert(lhs != null);
          freshLhs.Add(Expr.Ident(FreshVar(cce.NonNull(lhs.DeepAssignedVariable)
                                           .TypedIdent.Type)));
        }

        for (int i = 0; i < freshLhs.Count; ++i)
          currentValue =
            this.lattice.Constrain(currentValue,
                                   Expr.Eq(freshLhs[i], assmt.Rhss[i]).IExpr);
        foreach (AssignLhs lhs in assmt.Lhss) {
          Contract.Assert(lhs != null);
          currentValue =
            this.lattice.Eliminate(currentValue, cce.NonNull(lhs.DeepAssignedVariable));
        }
        for (int i = 0; i < freshLhs.Count; ++i)
          currentValue =
            this.lattice.Rename(currentValue, cce.NonNull(freshLhs[i].Decl),
                                cce.NonNull(assmt.Lhss[i].DeepAssignedVariable));
      }

      /*
      if (cmd is SimpleAssignCmd)
      {
        SimpleAssignCmd! assmt = (SimpleAssignCmd)cmd;
        assume assmt.Lhs.Decl != null; //PM: Assume variables have been resolved
        Variable! dest = assmt.Lhs.Decl;
        Variable! fresh = FreshVar(dest.TypedIdent.Type);
        IdentifierExpr newLhs = Expr.Ident(fresh);
        Expr equality = Expr.Eq(newLhs, assmt.Rhs);

        currentValue = this.lattice.Constrain(currentValue, equality.IExpr);
        currentValue = this.lattice.Eliminate(currentValue, dest);
        currentValue = this.lattice.Rename(currentValue, fresh, dest);
      }
      #endregion
      #region ArrayAssignCmd
      else if (cmd is ArrayAssignCmd)
      {
        ArrayAssignCmd assmt = (ArrayAssignCmd)cmd;
        
        assume assmt.Array.Type != null;  //PM: assume that type checker has run
        ArrayType! arrayType = (ArrayType)assmt.Array.Type;
        
        Variable newHeapVar = FreshVar(arrayType);
        IdentifierExpr newHeap = Expr.Ident(newHeapVar);
        IdentifierExpr oldHeap = assmt.Array;
        assume oldHeap.Decl != null; //PM: assume that variable has been resolved

        // For now, we only know how to handle heaps
        if (arrayType.IndexType0.IsRef && arrayType.IndexType1 != null && arrayType.IndexType1.IsName)
        {
          //PM: The following assertion follows from a nontrivial invariant of ArrayAssignCmd,
          //PM: which we do not have yet. Therefore, we put in an assume fo now.
          assume assmt.Index1 != null;
          assert assmt.Index1 != null;
          // heap succession predicate
          Expr heapsucc = Expr.HeapSucc(oldHeap, newHeap, assmt.Index0, assmt.Index1);

          currentValue = this.lattice.Constrain(currentValue, heapsucc.IExpr);
       
        }   
        else
        {
          // TODO: We can do this case as well if the heap succession array can handle non-heap arrays
        }
        // new select expression
        IndexedExpr newLhs = new IndexedExpr(Token.NoToken, newHeap, assmt.Index0, assmt.Index1);
        Expr equality = Expr.Eq(newLhs, assmt.Rhs);
        
        currentValue = this.lattice.Constrain(currentValue, equality.IExpr);
        currentValue = this.lattice.Eliminate(currentValue, oldHeap.Decl);
        currentValue = this.lattice.Rename(currentValue, newHeapVar, oldHeap.Decl);
       
     
        } */
      #endregion
      #region Havoc
      else if (cmd is HavocCmd) {
        HavocCmd havoc = (HavocCmd)cmd;
        foreach (IdentifierExpr id in havoc.Vars) {
          Contract.Assert(id != null);
          currentValue = this.lattice.Eliminate(currentValue, cce.NonNull(id.Decl));
        }
      }
      #endregion
      #region PredicateCmd
 else if (cmd is PredicateCmd) {
        //System.Console.WriteLine("Abstract State BEFORE " + ((PredicateCmd) cmd).Expr + " : " +this.lattice.ToPredicate(currentValue));

        Expr embeddedExpr = cce.NonNull((PredicateCmd)cmd).Expr;
        List<Expr/*!>!*/> conjuncts = flatConjunction(embeddedExpr);           // Handle "assume P && Q" as if it was "assume P; assume Q"
        Contract.Assert(conjuncts != null);
        foreach (Expr c in conjuncts) {
          Contract.Assert(c != null);
          currentValue = this.lattice.Constrain(currentValue, c.IExpr);
        }

        //System.Console.WriteLine("Abstract State AFTER assert/assume "+ this.lattice.ToPredicate(currentValue));
      }
      #endregion
      #region CallCmd
 else if (cmd is CallCmd) {
        CallCmd call = (CallCmd)cmd;

        if (!CommandLineOptions.Clo.IntraproceduralInfer) {
          // Interprocedural analysis

          if (callSiteMarker == null) {
            throw new System.InvalidOperationException("INTERNAL ERROR: Context does not allow CallCmd.");
          }

          CallSite here = callSiteMarker(currentValue);
          currentValue = ApplyProcedureSummary(call, impl, currentValue, here);
        } else {
          // Intraprocedural analysis

          StateCmd statecmd = call.Desugaring as StateCmd;
          if (statecmd != null) {
            // Iterate the abstract transition on all the commands in the desugaring of the call
            foreach (Cmd callDesug in statecmd.Cmds) {
              Contract.Assert(callDesug != null);
              currentValue = Step(callDesug, currentValue, impl, null);
            }

            // Now, project out the local variables
            foreach (Variable local in statecmd.Locals) {
              Contract.Assert(local != null);
              currentValue = this.lattice.Eliminate(currentValue, local);
            }
          } else
            throw new System.InvalidOperationException("INTERNAL ERROR: CallCmd does not desugar to StateCmd.");
        }
      }
      #endregion
      #region CommentCmd
 else if (cmd is CommentCmd) {
        // skip
      }
      #endregion
 else if (cmd is SugaredCmd) {
        // other sugared commands are treated like their desugaring
        SugaredCmd sugar = (SugaredCmd)cmd;
        Cmd desugaring = sugar.Desugaring;
        if (desugaring is StateCmd) {
          StateCmd statecmd = (StateCmd)desugaring;
          // Iterate the abstract transition on all the commands in the desugaring of the call
          foreach (Cmd callDesug in statecmd.Cmds) {
            Contract.Assert(callDesug != null);
            currentValue = Step(callDesug, currentValue, impl, null);
          }
          // Now, project out the local variables
          foreach (Variable local in statecmd.Locals) {
            Contract.Assert(local != null);
            currentValue = this.lattice.Eliminate(currentValue, local);
          }
        } else {
          currentValue = Step(desugaring, currentValue, impl, null);
        }
      } else {
        Contract.Assert(false);  // unknown command
        throw new cce.UnreachableException();
      }

      log.DbgMsgUnindent();

      return currentValue;
    }

    /// <summary>
    /// Flat an expresion in the form P AND Q ... AND R into a list [P, Q, ..., R]
    /// </summary>
    private List<Expr/*!>!*/> flatConjunction(Expr embeddedExpr) {
      Contract.Requires(embeddedExpr != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Expr>>()));


      List<Expr/*!>!*/> retValue = new List<Expr/*!*/>();//No asserts necessarry.  It is the return value, and thus will be subject to the postcondition
      NAryExpr e = embeddedExpr as NAryExpr;
      if (e != null && e.Fun.FunctionName.CompareTo("&&") == 0) {    // if it is a conjunction
        foreach (Expr arg in e.Args) {
          Contract.Assert(arg != null);
          List<Expr/*!*/>/*!*/  newConjuncts = flatConjunction(arg);
          Contract.Assert(cce.NonNullElements(newConjuncts));
          retValue.AddRange(newConjuncts);
        }
      } else {
        retValue.Add(embeddedExpr);
      }
      return retValue;
    }

    /// <summary>
    /// Compute the invariants for a basic block 
    /// <param name="impl"> The implementation the block belongs to </param>
    /// <param name="block">  The block for which we compute the invariants </param>
    /// <param name="incomingValue">  The "init" abstract state for the block </param>
    /// </summary>
    private void ComputeBlockInvariants(Implementation impl, Block block, AI.Lattice.Element incomingValue, ProcedureSummaryEntry summaryEntry) {
      Contract.Requires(impl != null);
      Contract.Requires(block != null);
      Contract.Requires(incomingValue != null);
      Contract.Requires(summaryEntry != null);
      if (block.PreInvariant == null) // block has not yet been processed
      {
        Contract.Assert(block.PostInvariant == null);

        // To a first approximation the block is unreachable
        block.PreInvariant = this.lattice.Bottom;
        block.PostInvariant = this.lattice.Bottom;
      }

      Contract.Assert(block.PreInvariant != null);
      Contract.Assert(block.PostInvariant != null);

      #region Check if we have reached a postfixpoint

      if (lattice.LowerThan(incomingValue, block.PreInvariant)) {
        // We have reached a post-fixpoint, so we are done...
#if DEBUG_PRINT
        System.Console.WriteLine("@@ Compared for block {0}:", block.Label);
        System.Console.WriteLine("@@ {0}", lattice.ToPredicate(incomingValue));
        System.Console.WriteLine("@@ {0}", lattice.ToPredicate(block.PreInvariant));
        System.Console.WriteLine("@@ result = True");
        System.Console.WriteLine("@@ end Compare");
#endif
        return;
      }
#if DEBUG_PRINT
      // Compute the free variables in incoming and block.PreInvariant
      FreeVariablesVisitor freeVarsVisitorForA = new FreeVariablesVisitor();
      FreeVariablesVisitor freeVarsVisitorForB = new FreeVariablesVisitor();

      lattice.ToPredicate(incomingValue).DoVisit(freeVarsVisitorForA);
      lattice.ToPredicate(block.PreInvariant).DoVisit(freeVarsVisitorForB);
      
      List<AI.IVariable!>! freeVarsOfA = freeVarsVisitorForA.FreeVariables;
      List<AI.IVariable!>! freeVarsOfB = freeVarsVisitorForB.FreeVariables;

      System.Console.WriteLine("@@ Compared for block {0}:", block.Label);
      System.Console.WriteLine("@@ Incoming: {0}", lattice.ToPredicate((!) incomingValue));
      System.Console.WriteLine("@@ Free Variables : {0}", ToString(freeVarsOfA));
      System.Console.WriteLine("@@ Previous: {0}", lattice.ToPredicate(block.PreInvariant));
      System.Console.WriteLine("@@ Free Variables : {0}", ToString(freeVarsOfB));
      System.Console.WriteLine("@@ result = False");
      System.Console.WriteLine("@@ end Compare");
      string operation = "";
#endif
      #endregion
      #region If it is not the case, then join or widen the incoming abstract state with the previous one
      if (block.widenBlock)     // If the considered block is the entry point of a loop
      {
        if (block.iterations <= CommandLineOptions.Clo.StepsBeforeWidening + 1) {
#if DEBUG_PRINT 
    operation = "join";
#endif
          block.PreInvariant = (AI.Lattice.Element)lattice.Join(block.PreInvariant, incomingValue);
        } else {
#if DEBUG_PRINT
      operation = "widening";
#endif

          // The default is to have have a widening that perform a (approximation of) the closure of the operands, so to improve the precision
          //    block.PreInvariant =  WideningWithClosure.MorePreciseWiden(lattice, (!) block.PreInvariant, incomingValue);
          block.PreInvariant = (AI.Lattice.Element)lattice.Widen(block.PreInvariant, incomingValue);
        }
        block.iterations++;
      } else {
#if DEBUG_PRINT
  operation = "join";
#endif
        block.PreInvariant = (AI.Lattice.Element)lattice.Join(block.PreInvariant, incomingValue);
      }

#if DEBUG_PRINT
      System.Console.WriteLine("@@ {0} for block {1}:", operation, block.Label);
      System.Console.WriteLine("@@ {0}", lattice.ToPredicate(block.PreInvariant));
      System.Console.WriteLine("@@ end");
#endif
      #endregion
      #region Propagate the entry abstract state through the method
      PropagateStartingAtStatement(impl, block, 0, cce.NonNull(block.PreInvariant.Clone()), summaryEntry);
      #endregion
    }

#if DEBUG_PRINT
    private string! ToString(List<AI.IVariable!>! vars) 
    {
      string s = "";
        
      foreach(AI.IVariable! v in vars) 
      {
        s += v.Name +" ";
      }
      return s;
    }
#endif

  } // class


  /// <summary>
  /// Defines a class for building the abstract domain according to the parameters switch
  /// </summary>
  public class AbstractDomainBuilder {

    private AbstractDomainBuilder() { /* do nothing */
    }

    /// <summary>
    /// Return a fresh instance of the abstract domain of intervals
    /// </summary>
    static public AbstractAlgebra BuildIntervalsAbstractDomain() {
      Contract.Ensures(Contract.Result<AbstractAlgebra>() != null);

      AI.IQuantPropExprFactory propfactory = new BoogiePropFactory();
      AI.ILinearExprFactory linearfactory = new BoogieLinearFactory();
      AI.IValueExprFactory valuefactory = new BoogieValueFactory();
      IComparer variableComparer = new VariableComparer();

      AbstractAlgebra retAlgebra;
      AI.Lattice intervals = new AI.VariableMapLattice(propfactory, valuefactory, new AI.IntervalLattice(linearfactory), variableComparer);
      Contract.Assert(intervals != null);
      retAlgebra = new AbstractAlgebra(intervals, propfactory, linearfactory, null, valuefactory, null, variableComparer);

      return retAlgebra;
    }

    /// <summary>
    /// Return a fresh abstract domain, according to the parameters specified by the command line
    /// </summary>
    static public AbstractAlgebra BuildAbstractDomain() {
      Contract.Ensures(Contract.Result<AbstractAlgebra>() != null);

      AbstractAlgebra retAlgebra;

      AI.Lattice returnLattice;

      AI.IQuantPropExprFactory propfactory = new BoogiePropFactory();
      AI.ILinearExprFactory linearfactory = new BoogieLinearFactory();
      AI.IIntExprFactory intfactory = new BoogieIntFactory();
      AI.IValueExprFactory valuefactory = new BoogieValueFactory();
      AI.INullnessFactory nullfactory = new BoogieNullnessFactory();
      IComparer variableComparer = new VariableComparer();

      AI.MultiLattice multilattice = new AI.MultiLattice(propfactory, valuefactory);

      if (CommandLineOptions.Clo.Ai.Intervals)        // Intervals
        {
        multilattice.AddLattice(new AI.VariableMapLattice(propfactory, valuefactory,
                                new AI.IntervalLattice(linearfactory),
                                variableComparer));
      }
      if (CommandLineOptions.Clo.Ai.Constant)         // Constant propagation

        {
        multilattice.AddLattice(new AI.VariableMapLattice(propfactory, valuefactory,
                                new AI.ConstantLattice(intfactory),
                                variableComparer));
      }
      if (CommandLineOptions.Clo.Ai.DynamicType)      // Class types
        {
        BoogieTypeFactory typeFactory = new BoogieTypeFactory();
        multilattice.AddLattice(new AI.VariableMapLattice(propfactory, valuefactory,
                                                  new AI.DynamicTypeLattice(typeFactory, propfactory),
                                                  variableComparer));
      }
      if (CommandLineOptions.Clo.Ai.Nullness)       // Nullness
        {
        multilattice.AddLattice(new AI.VariableMapLattice(propfactory, valuefactory,
                                                  new AI.NullnessLattice(nullfactory),
                                                  variableComparer));
      }
      if (CommandLineOptions.Clo.Ai.Polyhedra)    // Polyhedra
        {
        multilattice.AddLattice(new AI.PolyhedraLattice(linearfactory, propfactory));
      }


      returnLattice = multilattice;
      if (CommandLineOptions.Clo.Ai.DebugStatistics) {
        returnLattice = new AI.StatisticsLattice(returnLattice);
      }

      returnLattice.Validate();

      retAlgebra = new AbstractAlgebra(returnLattice, propfactory, linearfactory, intfactory, valuefactory, nullfactory,
                                                      variableComparer);

      return retAlgebra;

    }
  }

  /// <summary>
  /// An Abstract Algebra is a tuple made of a Lattice and several factories
  /// </summary>
  public class AbstractAlgebra {
    [Peer]
    private AI.Lattice lattice;
    [Peer]
    private AI.IQuantPropExprFactory propFactory;
    [Peer]
    private AI.ILinearExprFactory linearFactory;
    [Peer]
    private AI.IIntExprFactory intFactory;
    [Peer]
    private AI.IValueExprFactory valueFactory;
    [Peer]
    private AI.INullnessFactory nullFactory;
    [Peer]
    private IComparer variableComparer;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(lattice != null);
    }

    public AI.Lattice Lattice {
      get {
        Contract.Ensures(Contract.Result<AI.Lattice>() != null);

        return lattice;
      }
    }

    public AI.IQuantPropExprFactory PropositionFactory {
      get {
        return this.propFactory;
      }
    }

    public AI.ILinearExprFactory LinearExprFactory {
      get {
        return this.linearFactory;
      }
    }

    public AI.IIntExprFactory IntExprFactory {
      get {
        return this.intFactory;
      }
    }

    public AI.IValueExprFactory ValueFactory {
      get {
        return this.valueFactory;
      }
    }

    public AI.INullnessFactory NullFactory {
      get {
        return this.nullFactory;
      }
    }

    public IComparer VariableComparer {
      get {
        return this.variableComparer;
      }
    }

    [Captured]
    public AbstractAlgebra(AI.Lattice lattice,
                          AI.IQuantPropExprFactory propFactory,
                          AI.ILinearExprFactory linearFactory,
                          AI.IIntExprFactory intFactory,
                          AI.IValueExprFactory valueFactory,
                          AI.INullnessFactory nullFactory,
                          IComparer variableComparer) {
      Contract.Requires(propFactory == null || cce.Owner.Same(lattice, propFactory));//TODO: Owner is Microsoft.Contracts (mscorlib.Contracts).Owner
      Contract.Requires(linearFactory == null || cce.Owner.Same(lattice, linearFactory));
      Contract.Requires(intFactory == null || cce.Owner.Same(lattice, intFactory));
      Contract.Requires(valueFactory == null || cce.Owner.Same(lattice, valueFactory));
      Contract.Requires(nullFactory == null || cce.Owner.Same(lattice, nullFactory));
      Contract.Requires(variableComparer == null || cce.Owner.Same(lattice, variableComparer));
      // ensures Owner.Same(this, lattice);  // KRML: 

      Contract.Requires(lattice != null);
      this.lattice = lattice;

      this.propFactory = propFactory;
      this.linearFactory = linearFactory;
      this.intFactory = intFactory;
      this.valueFactory = valueFactory;
      this.nullFactory = nullFactory;
      this.variableComparer = variableComparer;
    }

  }

  public class AbstractInterpretation {
    /// <summary>
    /// Run the abstract interpretation.
    /// It has two entry points. One is the RunBoogie method. The other is the CCI PlugIn
    /// </summary>
    public static void RunAbstractInterpretation(Program program) {
      Contract.Requires(program != null);
      Helpers.ExtraTraceInformation("Starting abstract interpretation");

      if (CommandLineOptions.Clo.UseAbstractInterpretation) {
        DateTime start = new DateTime();  // to please compiler's definite assignment rules
        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine();
          Console.WriteLine("Running abstract interpretation...");
          start = DateTime.Now;
        }

        WidenPoints.Compute(program);

        if (CommandLineOptions.Clo.Ai.AnySet) // if there is some user defined domain we override the default (= intervals)
      {
          AI.Lattice lattice = AbstractDomainBuilder.BuildAbstractDomain().Lattice;
          ApplyAbstractInterpretation(program, lattice);

          if (CommandLineOptions.Clo.Ai.DebugStatistics) {
            Console.Error.WriteLine(lattice);
          }
        } else    // Otherwise the default is the use of the abstract domain of intervals (useful for simple for loops)
      {
          AI.Lattice lattice = AbstractDomainBuilder.BuildIntervalsAbstractDomain().Lattice;
          Contract.Assert(lattice != null);
          ApplyAbstractInterpretation(program, lattice);
        }

        program.InstrumentWithInvariants();

        if (CommandLineOptions.Clo.Trace) {
          DateTime end = DateTime.Now;
          TimeSpan elapsed = end - start;
          Console.WriteLine("  [{0} s]", elapsed.TotalSeconds);
          Console.Out.Flush();
        }
      }
    }

    static void ApplyAbstractInterpretation(Program program, AI.Lattice lattice) {
      Contract.Requires(program != null);
      Contract.Requires(lattice != null);
      AbstractionEngine engine = new AbstractionEngine(lattice);
      engine.ComputeProgramInvariants(program);
    }
  }

} // namespace