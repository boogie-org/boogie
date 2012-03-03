//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Diagnostics.Contracts;
using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using System.Collections;
using System.IO;
using Microsoft.AbstractInterpretationFramework;
using Graphing;

namespace Microsoft.Boogie.Houdini {

  class ReadOnlyDictionary<K, V> {
    private Dictionary<K, V> dictionary;
    public ReadOnlyDictionary(Dictionary<K, V> dictionary) {
      this.dictionary = dictionary;
    }

    public Dictionary<K, V>.KeyCollection Keys {
      get { return this.dictionary.Keys; }
    }

    public bool TryGetValue(K k, out V v) {
      return this.dictionary.TryGetValue(k, out v);
    }

    public bool ContainsKey(K k) {
      return this.dictionary.ContainsKey(k);
    }
  }

  public abstract class HoudiniObserver {
    public virtual void UpdateStart(Program program, int numConstants) { }
    public virtual void UpdateIteration() { }
    public virtual void UpdateImplementation(Implementation implementation) { }
    public virtual void UpdateAssignment(Dictionary<string, bool> assignment) { }
    public virtual void UpdateOutcome(ProverInterface.Outcome outcome) { }
    public virtual void UpdateEnqueue(Implementation implementation) { }
    public virtual void UpdateDequeue() { }
    public virtual void UpdateConstant(string constantName) { }
    public virtual void UpdateEnd(bool isNormalEnd) { }
    public virtual void UpdateFlushStart() { }
    public virtual void UpdateFlushFinish() { }
    public virtual void SeeException(string msg) { }
  }

  public class IterationTimer<K> {
    private Dictionary<K, List<double>> times;

    public IterationTimer() {
      times = new Dictionary<K, List<double>>();
    }

    public void AddTime(K key, double timeMS) {
      List<double> oldList;
      times.TryGetValue(key, out oldList);
      if (oldList == null) {
        oldList = new List<double>();
      }
      else {
        times.Remove(key);
      }
      oldList.Add(timeMS);
      times.Add(key, oldList);
    }

    public void PrintTimes(TextWriter wr) {
      wr.WriteLine("Total procedures: {0}", times.Count);
      double total = 0;
      int totalIters = 0;
      foreach (KeyValuePair<K, List<double>> kv in times) {
        int curIter = 0;
        wr.WriteLine("Times for {0}:", kv.Key);
        foreach (double v in kv.Value) {
          wr.WriteLine("  ({0})\t{1}ms", curIter, v);
          total += v;
          curIter++;
        }
        totalIters += curIter;
      }
      total = total / 1000.0;
      wr.WriteLine("Total time: {0} (s)", total);
      wr.WriteLine("Avg: {0} (s/iter)", total / totalIters);
    }
  }

  public class HoudiniTimer : HoudiniObserver {
    private DateTime startT;
    private Implementation curImp;
    private IterationTimer<string> times;
    private TextWriter wr;

    public HoudiniTimer(TextWriter wr) {
      this.wr = wr;
      times = new IterationTimer<string>();
    }
    public override void UpdateIteration() {
      startT = DateTime.UtcNow;
    }
    public override void UpdateImplementation(Implementation implementation) {
      curImp = implementation;
    }
    public override void UpdateOutcome(ProverInterface.Outcome o) {
      Contract.Assert(curImp != null);
      DateTime endT = DateTime.UtcNow;
      times.AddTime(curImp.Name, (endT - startT).TotalMilliseconds); // assuming names are unique
    }
    public void PrintTimes() {
      wr.WriteLine("-----------------------------------------");
      wr.WriteLine("Times for each iteration for each procedure");
      wr.WriteLine("-----------------------------------------");
      times.PrintTimes(wr);
    }
  }

  public class HoudiniTextReporter : HoudiniObserver {
    private TextWriter wr;
    private int currentIteration = -1;

    public HoudiniTextReporter(TextWriter wr) {
      this.wr = wr;
    }
    public override void UpdateStart(Program program, int numConstants) {
      wr.WriteLine("Houdini started:" + program.ToString() + " #constants: " + numConstants.ToString());
      currentIteration = -1;
      wr.Flush();
    }
    public override void UpdateIteration() {
      currentIteration++;
      wr.WriteLine("---------------------------------------");
      wr.WriteLine("Houdini iteration #" + currentIteration);
      wr.Flush();
    }
    public override void UpdateImplementation(Implementation implementation) {
      wr.WriteLine("implementation under analysis :" + implementation.Name);
      wr.Flush();
    }
    public override void UpdateAssignment(Dictionary<string, bool> assignment) {
      bool firstTime = true;
      wr.Write("assignment under analysis : axiom (");
      foreach (KeyValuePair<string, bool> kv in assignment) {
        if (!firstTime) wr.Write(" && "); else firstTime = false;
        string valString; // ugliness to get it lower cased
        if (kv.Value) valString = "true"; else valString = "false";
        wr.Write(kv.Key + " == " + valString);
      }
      wr.WriteLine(");");
      wr.Flush();
    }
    public override void UpdateOutcome(ProverInterface.Outcome outcome) {
      wr.WriteLine("analysis outcome :" + outcome);
      wr.Flush();
    }
    public override void UpdateEnqueue(Implementation implementation) {
      wr.WriteLine("worklist enqueue :" + implementation.Name);
      wr.Flush();
    }
    public override void UpdateDequeue() {
      wr.WriteLine("worklist dequeue");
      wr.Flush();
    }
    public override void UpdateConstant(string constantName) {
      wr.WriteLine("constant disabled : " + constantName);
      wr.Flush();
    }
    public override void UpdateEnd(bool isNormalEnd) {
      wr.WriteLine("Houdini ended: " + (isNormalEnd ? "Normal" : "Abnormal"));
      wr.WriteLine("Number of iterations: " + (this.currentIteration + 1));
      wr.Flush();
    }
    public override void UpdateFlushStart() {
      wr.WriteLine("***************************************");
      wr.WriteLine("Flushing remaining implementations");
      wr.Flush();
    }
    public override void UpdateFlushFinish() {
      wr.WriteLine("***************************************");
      wr.WriteLine("Flushing finished");
      wr.Flush();
    }
    public override void SeeException(string msg) {
      wr.WriteLine("Caught exception: " + msg);
      wr.Flush();
    }

  }

  public abstract class ObservableHoudini {
    private List<HoudiniObserver> observers = new List<HoudiniObserver>();

    public void AddObserver(HoudiniObserver observer) {
      if (!observers.Contains(observer))
        observers.Add(observer);
    }
    private delegate void NotifyDelegate(HoudiniObserver observer);

    private void Notify(NotifyDelegate notifyDelegate) {
      foreach (HoudiniObserver observer in observers) {
        notifyDelegate(observer);
      }
    }
    protected void NotifyStart(Program program, int numConstants) {
      NotifyDelegate notifyDelegate = (NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateStart(program, numConstants); };
      Notify(notifyDelegate);
    }
    protected void NotifyIteration() {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateIteration(); });
    }
    protected void NotifyImplementation(Implementation implementation) {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateImplementation(implementation); });
    }
    protected void NotifyAssignment(Dictionary<string, bool> assignment) {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateAssignment(assignment); });
    }
    protected void NotifyOutcome(ProverInterface.Outcome outcome) {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateOutcome(outcome); });
    }
    protected void NotifyEnqueue(Implementation implementation) {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateEnqueue(implementation); });
    }
    protected void NotifyDequeue() {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateDequeue(); });
    }
    protected void NotifyConstant(string constantName) {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateConstant(constantName); });
    }
    protected void NotifyEnd(bool isNormalEnd) {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateEnd(isNormalEnd); });
    }
    protected void NotifyFlushStart() {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateFlushStart(); });
    }
    protected void NotifyFlushFinish() {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.UpdateFlushFinish(); });
    }

    protected void NotifyException(string msg) {
      Notify((NotifyDelegate)delegate(HoudiniObserver r) { r.SeeException(msg); });
    }
  }

  public class InlineRequiresVisitor : StandardVisitor {
    public override CmdSeq VisitCmdSeq(CmdSeq cmdSeq) {
      Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<CmdSeq>() != null);
      CmdSeq newCmdSeq = new CmdSeq();
      for (int i = 0, n = cmdSeq.Length; i < n; i++) {
        Cmd cmd = cmdSeq[i];
        CallCmd callCmd = cmd as CallCmd;
        if (callCmd != null) {
          newCmdSeq.AddRange(InlineRequiresForCallCmd(callCmd));
        }
        else {
          newCmdSeq.Add((Cmd)this.Visit(cmd));
        }
      }
      return newCmdSeq;
    }
    private CmdSeq InlineRequiresForCallCmd(CallCmd node) {
      Hashtable substMap = new Hashtable();
      for (int i = 0; i < node.Proc.InParams.Length; i++) {
        substMap.Add(node.Proc.InParams[i], node.Ins[i]);
      }
      Substitution substitution = Substituter.SubstitutionFromHashtable(substMap);
      CmdSeq cmds = new CmdSeq();
      foreach (Requires requires in node.Proc.Requires) {
        if (requires.Free) continue;
        Requires requiresCopy = new Requires(false, Substituter.Apply(substitution, requires.Condition));
        cmds.Add(new AssertRequiresCmd(node, requiresCopy));
      }
      cmds.Add(node);
      return cmds;
    }
  }

  public class FreeRequiresVisitor : StandardVisitor {
    public override Requires VisitRequires(Requires requires) {
      if (requires.Free)
        return base.VisitRequires(requires);
      else 
        return new Requires(true, requires.Condition);
    }

    public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node) {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Requires = base.VisitRequires(node.Requires);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }
  }

  public class Houdini : ObservableHoudini {
    private Program program;
    private ReadOnlyDictionary<string, IdentifierExpr> houdiniConstants;
    private ReadOnlyDictionary<Implementation, HoudiniSession> houdiniSessions;
    private VCGen vcgen;
    private Checker checker;
    private Graph<Implementation> callGraph;
    private bool continueAtError;
    private HashSet<Implementation> vcgenFailures;

    public Houdini(Program program, bool continueAtError) {
      this.program = program;
      this.continueAtError = continueAtError;

      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Collecting existential constants...");
      this.houdiniConstants = CollectExistentialConstants();
      
      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Building call graph...");
      this.callGraph = BuildCallGraph();
      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Number of implementations = {0}", callGraph.Nodes.Count);

      Inline();
      
      this.vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);
      this.checker = new Checker(vcgen, program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, CommandLineOptions.Clo.ProverKillTime);

      vcgenFailures = new HashSet<Implementation>();
      Dictionary<Implementation, HoudiniSession> houdiniSessions = new Dictionary<Implementation, HoudiniSession>();
      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Beginning VC generation for Houdini...");
      foreach (Implementation impl in callGraph.Nodes) {
        try {
          if (CommandLineOptions.Clo.Trace)
            Console.WriteLine("Generating VC for {0}", impl.Name);
          HoudiniSession session = new HoudiniSession(vcgen, checker, program, impl);
          houdiniSessions.Add(impl, session);
        }
        catch (VCGenException) {
          if (CommandLineOptions.Clo.Trace)
            Console.WriteLine("VC generation failed");
          vcgenFailures.Add(impl);
        }
      }
      this.houdiniSessions = new ReadOnlyDictionary<Implementation, HoudiniSession>(houdiniSessions);
    }

    private void Inline() {
      if (CommandLineOptions.Clo.InlineDepth < 0)
        return;

      foreach (Implementation impl in callGraph.Nodes) {
        InlineRequiresVisitor inlineRequiresVisitor = new InlineRequiresVisitor();
        inlineRequiresVisitor.Visit(impl);
      }

      foreach (Implementation impl in callGraph.Nodes) {
        FreeRequiresVisitor freeRequiresVisitor = new FreeRequiresVisitor();
        freeRequiresVisitor.Visit(impl);
      }

      foreach (Implementation impl in callGraph.Nodes) {
        impl.OriginalBlocks = impl.Blocks;
        impl.OriginalLocVars = impl.LocVars;
      }
      foreach (Implementation impl in callGraph.Nodes) {
        CommandLineOptions.Inlining savedOption = CommandLineOptions.Clo.ProcedureInlining;
        CommandLineOptions.Clo.ProcedureInlining = CommandLineOptions.Inlining.Spec;
        Inliner.ProcessImplementationForHoudini(program, impl);
        CommandLineOptions.Clo.ProcedureInlining = savedOption;
      }
      foreach (Implementation impl in callGraph.Nodes) {
        impl.OriginalBlocks = null;
        impl.OriginalLocVars = null;
      }

      Graph<Implementation> oldCallGraph = callGraph;
      callGraph = new Graph<Implementation>();
      foreach (Implementation impl in oldCallGraph.Nodes) {
        callGraph.AddSource(impl);
      }
      foreach (Tuple<Implementation, Implementation> edge in oldCallGraph.Edges) {
        callGraph.AddEdge(edge.Item1, edge.Item2);
      }
      int count = CommandLineOptions.Clo.InlineDepth;
      while (count > 0) {
        foreach (Implementation impl in oldCallGraph.Nodes) {
          List<Implementation> newNodes = new List<Implementation>();
          foreach (Implementation succ in callGraph.Successors(impl)) {
            newNodes.AddRange(oldCallGraph.Successors(succ));
          }
          foreach (Implementation newNode in newNodes) {
            callGraph.AddEdge(impl, newNode);
          }
        }
        count--;
      }
    }

    private ReadOnlyDictionary<string, IdentifierExpr> CollectExistentialConstants() {
      Dictionary<string, IdentifierExpr> existentialConstants = new Dictionary<string, IdentifierExpr>();
      foreach (Declaration decl in program.TopLevelDeclarations) {
        Constant constant = decl as Constant;
        if (constant != null) {
          bool result = false;
          if (constant.CheckBooleanAttribute("existential", ref result)) {
            if (result == true)
              existentialConstants.Add(constant.Name, new IdentifierExpr(Token.NoToken, constant));
          }
        }
      }
      return new ReadOnlyDictionary<string, IdentifierExpr>(existentialConstants);
    }

    private Graph<Implementation> BuildCallGraph() {
      Graph<Implementation> callGraph = new Graph<Implementation>();
      Dictionary<Procedure, HashSet<Implementation>> procToImpls = new Dictionary<Procedure, HashSet<Implementation>>();
      foreach (Declaration decl in program.TopLevelDeclarations) {
        Procedure proc = decl as Procedure;
        if (proc == null) continue;
        procToImpls[proc] = new HashSet<Implementation>();
      } 
      foreach (Declaration decl in program.TopLevelDeclarations) {
        Implementation impl = decl as Implementation;
        if (impl == null || impl.SkipVerification) continue;
        callGraph.AddSource(impl);
        procToImpls[impl.Proc].Add(impl);
      }
      foreach (Declaration decl in program.TopLevelDeclarations) {
        Implementation impl = decl as Implementation;
        if (impl == null || impl.SkipVerification) continue;
        foreach (Block b in impl.Blocks) {
          foreach (Cmd c in b.Cmds) {
            CallCmd cc = c as CallCmd;
            if (cc == null) continue;
            foreach (Implementation callee in procToImpls[cc.Proc]) {
              callGraph.AddEdge(impl, callee);
            }
          }
        }
      }
      return callGraph;
    }
    
    private WorkQueue BuildWorkList(Program program) {
      // adding implementations to the workqueue from the bottom of the call graph upwards
      WorkQueue queue = new WorkQueue();
      StronglyConnectedComponents<Implementation> sccs =
        new StronglyConnectedComponents<Implementation>(callGraph.Nodes,
          new Adjacency<Implementation>(callGraph.Predecessors),
          new Adjacency<Implementation>(callGraph.Successors));
      sccs.Compute();
      foreach (SCC<Implementation> scc in sccs) {
        foreach (Implementation impl in scc) {
          if (vcgenFailures.Contains(impl)) continue;
          queue.Enqueue(impl);
        }
      }
      return queue;
      
      /*
      Queue<Implementation> queue = new Queue<Implementation>();
      foreach (Declaration decl in program.TopLevelDeclarations) {
        Implementation impl = decl as Implementation;
        if (impl == null || impl.SkipVerification) continue;
        queue.Enqueue(impl);
      }
      return queue;
       */
    }

    private bool MatchCandidate(Expr boogieExpr, out string candidateConstant) {
      candidateConstant = null;
      IExpr antecedent;
      IExpr expr = boogieExpr as IExpr;
      if (expr != null && ExprUtil.Match(expr, Prop.Implies, out antecedent)) {
        IdentifierExpr.ConstantFunApp constantFunApp = antecedent as IdentifierExpr.ConstantFunApp;
        if (constantFunApp != null && houdiniConstants.ContainsKey(constantFunApp.IdentifierExpr.Name)) {
          candidateConstant = constantFunApp.IdentifierExpr.Name;
          return true;
        }
      }
      return false;
    }

    private VCExpr BuildAxiom(Dictionary<string, bool> currentAssignment) {
      DeclFreeProverContext proverContext = (DeclFreeProverContext)checker.TheoremProver.Context;
      Boogie2VCExprTranslator exprTranslator = proverContext.BoogieExprTranslator;
      VCExpressionGenerator exprGen = checker.VCExprGen;

      VCExpr expr = VCExpressionGenerator.True;
      foreach (KeyValuePair<string, bool> kv in currentAssignment) {
        IdentifierExpr constantExpr;
        houdiniConstants.TryGetValue(kv.Key, out constantExpr);
        Contract.Assume(constantExpr != null);
        VCExprVar exprVar = exprTranslator.LookupVariable(constantExpr.Decl);
        if (kv.Value) {
          expr = exprGen.And(expr, exprVar);
        }
        else {
          expr = exprGen.And(expr, exprGen.Not(exprVar));
        }
      }
      return expr;
    }

    private Dictionary<string, bool> BuildAssignment(Dictionary<string, IdentifierExpr>.KeyCollection constants) {
      Dictionary<string, bool> initial = new Dictionary<string, bool>();
      foreach (string constant in constants)
        initial.Add(constant, true);
      return initial;
    }

    private ProverInterface.Outcome VerifyUsingAxiom(HoudiniSession session, Implementation implementation, VCExpr axiom, out List<Counterexample> errors) {
      if (vcgen == null)
        throw new Exception("HdnVCGen not found for implementation: " + implementation.Name);
      ProverInterface.Outcome outcome = TryCatchVerify(session, axiom, out errors);
      return outcome;
    }

    // the main procedure that checks a procedure and updates the
    // assignment and the worklist
    private ProverInterface.Outcome HoudiniVerifyCurrent(
                                        HoudiniSession session,
                                        HoudiniState current,
                                        Program program,
                                        out List<Counterexample> errors,
                                        out bool exc) {
      if (current.Implementation == null)
        throw new Exception("HoudiniVerifyCurrent has null implementation");

      Implementation implementation = current.Implementation;
      if (vcgen == null)
        throw new Exception("HdnVCGen not found for implementation: " + implementation.Name);

      ProverInterface.Outcome outcome = HoudiniVerifyCurrentAux(session, current, program, out errors, out exc);
      return outcome;
    }

    private bool IsOutcomeNotHoudini(ProverInterface.Outcome outcome, List<Counterexample> errors) {
      switch (outcome) {
        case ProverInterface.Outcome.Valid:
          return false;
        case ProverInterface.Outcome.Invalid:
          Contract.Assume(errors != null);
          foreach (Counterexample error in errors) {
            if (ExtractRefutedAnnotation(error) == null)
              return true;
          }
          return false;
        default:
          return true;
      }
    }

    // returns true if at least one of the violations is non-candidate
    private bool AnyNonCandidateViolation(ProverInterface.Outcome outcome, List<Counterexample> errors) {
      switch (outcome) {
        case ProverInterface.Outcome.Invalid:
          Contract.Assert(errors != null);
          foreach (Counterexample error in errors) {
            if (ExtractRefutedAnnotation(error) == null)
              return true;
          }
          return false;
        default:
          return false;
      }
    }

    private List<Counterexample> emptyList = new List<Counterexample>();

    // Record most current Non-Candidate errors found by Boogie, etc.
    private void UpdateHoudiniOutcome(HoudiniOutcome houdiniOutcome,
                                      Implementation implementation,
                                      ProverInterface.Outcome verificationOutcome,
                                      List<Counterexample> errors) {
      string implName = implementation.ToString();
      houdiniOutcome.implementationOutcomes.Remove(implName);
      List<Counterexample> nonCandidateErrors = new List<Counterexample>();

      switch (verificationOutcome) {
        case ProverInterface.Outcome.Invalid:
          Contract.Assume(errors != null);
          foreach (Counterexample error in errors) {
            if (ExtractRefutedAnnotation(error) == null)
              nonCandidateErrors.Add(error);
          }
          break;
        default:
          break;
      }
      houdiniOutcome.implementationOutcomes.Add(implName, new VCGenOutcome(verificationOutcome, nonCandidateErrors));
    }

    private void FlushWorkList(HoudiniState current) {
      this.NotifyFlushStart();
      VCExpr axiom = BuildAxiom(current.Assignment);
      while (current.WorkQueue.Count > 0) {
        this.NotifyIteration();

        current.Implementation = current.WorkQueue.Peek();
        this.NotifyImplementation(current.Implementation);

        HoudiniSession session;
        houdiniSessions.TryGetValue(current.Implementation, out session);
        List<Counterexample> errors;
        ProverInterface.Outcome outcome = VerifyUsingAxiom(session, current.Implementation, axiom, out errors);
        UpdateHoudiniOutcome(current.Outcome, current.Implementation, outcome, errors);
        this.NotifyOutcome(outcome);

        current.WorkQueue.Dequeue();
        this.NotifyDequeue();

      }
      this.NotifyFlushFinish();
    }

    private void UpdateAssignment(HoudiniState current, RefutedAnnotation refAnnot) {
      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Removing " + refAnnot.Constant);
      }
      current.Assignment.Remove(refAnnot.Constant);
      current.Assignment.Add(refAnnot.Constant, false);
      this.NotifyConstant(refAnnot.Constant);
    }

    private void AddToWorkList(HoudiniState current, Implementation imp) {
      if (!current.WorkQueue.Contains(imp) && !current.isBlackListed(imp.Name)) {
        current.WorkQueue.Enqueue(imp);
        this.NotifyEnqueue(imp);
      }
    }

    private void AddRelatedToWorkList(HoudiniState current, RefutedAnnotation refutedAnnotation) {
      Contract.Assume(current.Implementation != null);
      foreach (Implementation implementation in FindImplementationsToEnqueue(refutedAnnotation, current.Implementation)) {
        AddToWorkList(current, implementation);
      }
    }


    // Updates the worklist and current assignment
    // @return true if the current function is kept on the queue
    private bool UpdateAssignmentWorkList(HoudiniState current,
                                          ProverInterface.Outcome outcome,
                                          List<Counterexample> errors) {
      Contract.Assume(current.Implementation != null);
      bool dequeue = true;

      switch (outcome) {
        case ProverInterface.Outcome.Valid:
          //yeah, dequeue
          break;
        case ProverInterface.Outcome.Invalid:
          Contract.Assume(errors != null);
          foreach (Counterexample error in errors) {
            RefutedAnnotation refutedAnnotation = ExtractRefutedAnnotation(error);
            if (refutedAnnotation != null) { // some candidate annotation removed
              AddRelatedToWorkList(current, refutedAnnotation);
              UpdateAssignment(current, refutedAnnotation);
              dequeue = false;
            }
          }
          break;

        case ProverInterface.Outcome.TimeOut:
          // TODO: reset session instead of blocking timed out funcs?
          current.addToBlackList(current.Implementation.Name);
          break;
        case ProverInterface.Outcome.Undetermined:
        case ProverInterface.Outcome.OutOfMemory:
          break;
        default:
          throw new Exception("Unknown vcgen outcome");
      }
      if (dequeue) {
        current.WorkQueue.Dequeue();
        this.NotifyDequeue();
      }
      return !dequeue;
    }

    private class WorkQueue {
      private Queue<Implementation> queue;
      private HashSet<Implementation> set;
      public WorkQueue() {
        queue = new Queue<Implementation>();
        set = new HashSet<Implementation>();
      }
      public void Enqueue(Implementation impl) {
        if (set.Contains(impl))
          return;
        queue.Enqueue(impl);
        set.Add(impl);
      }
      public Implementation Dequeue() {
        Implementation impl = queue.Dequeue();
        set.Remove(impl);
        return impl;
      }
      public Implementation Peek() {
        return queue.Peek();
      }
      public int Count {
        get { return queue.Count; }
      }
      public bool Contains(Implementation impl) {
        return set.Contains(impl);
      }
    }

    private class HoudiniState {
      private WorkQueue _workQueue;
      private HashSet<string> blackList;
      private Dictionary<string, bool> _assignment;
      private Implementation _implementation;
      private HoudiniOutcome _outcome;

      public HoudiniState(WorkQueue workQueue, Dictionary<string, bool> currentAssignment) {
        this._workQueue = workQueue;
        this._assignment = currentAssignment;
        this._implementation = null;
        this._outcome = new HoudiniOutcome();
        this.blackList = new HashSet<string>();
      }

      public WorkQueue WorkQueue {
        get { return this._workQueue; }
      }
      public Dictionary<string, bool> Assignment {
        get { return this._assignment; }
      }
      public Implementation Implementation {
        get { return this._implementation; }
        set { this._implementation = value; }
      }
      public HoudiniOutcome Outcome {
        get { return this._outcome; }
      }
      public bool isBlackListed(string funcName) {
        return blackList.Contains(funcName);
      }
      public void addToBlackList(string funcName) {
        blackList.Add(funcName);
      }
    }

    //Clean houdini (Based on "Houdini Spec in Boogie" email 10/22/08
    //Aborts when there is a violation of non-candidate assertion
    //This can be used in eager mode (continueAfterError) by simply making
    //all non-candidate annotations as unchecked (free requires/ensures, assumes)
    public HoudiniOutcome PerformHoudiniInference() {
      HoudiniState current = new HoudiniState(BuildWorkList(program), BuildAssignment(houdiniConstants.Keys));
      this.NotifyStart(program, houdiniConstants.Keys.Count);
      foreach (Implementation impl in vcgenFailures) {
        current.addToBlackList(impl.Name);
      }

      while (current.WorkQueue.Count > 0) {
        bool exceptional = false;
        //System.GC.Collect();
        this.NotifyIteration();

        current.Implementation = current.WorkQueue.Peek();
        this.NotifyImplementation(current.Implementation);

        List<Counterexample> errors;
        HoudiniSession session;
        this.houdiniSessions.TryGetValue(current.Implementation, out session);
        ProverInterface.Outcome outcome = HoudiniVerifyCurrent(session, current, program, out errors, out exceptional);

        // updates to worklist already done in VerifyCurrent, unless there was an exception
        if (exceptional) {
          this.NotifyOutcome(outcome);
          UpdateHoudiniOutcome(current.Outcome, current.Implementation, outcome, errors);
          if (AnyNonCandidateViolation(outcome, errors)) { //abort
            current.WorkQueue.Dequeue();
            this.NotifyDequeue();
            FlushWorkList(current);
          }
          else { //continue
            UpdateAssignmentWorkList(current, outcome, errors);
          }
        }
      }
      this.NotifyEnd(true);
      current.Outcome.assignment = current.Assignment;
      return current.Outcome;
    }

    private List<Implementation> FindImplementationsToEnqueue(RefutedAnnotation refutedAnnotation, Implementation currentImplementation) {
      List<Implementation> implementations = new List<Implementation>();
      switch (refutedAnnotation.Kind) {
        case RefutedAnnotationKind.REQUIRES:
          foreach (Implementation callee in callGraph.Successors(currentImplementation)) {
            Contract.Assume(callee.Proc != null);
            if (callee.Proc.Equals(refutedAnnotation.CalleeProc))
              implementations.Add(callee);
          }
          break;
        case RefutedAnnotationKind.ENSURES:
          foreach (Implementation caller in callGraph.Predecessors(currentImplementation))
            implementations.Add(caller);
          break;
        case RefutedAnnotationKind.ASSERT: //the implementation is already in queue
          break;
        default:
          throw new Exception("Unknown Refuted annotation kind:" + refutedAnnotation.Kind);
      }
      return implementations;
    }

    private enum RefutedAnnotationKind { REQUIRES, ENSURES, ASSERT };

    private class RefutedAnnotation {
      private string _constant;
      private RefutedAnnotationKind _kind;
      private Procedure _callee;

      private RefutedAnnotation(string constant, RefutedAnnotationKind kind, Procedure callee) {
        this._constant = constant;
        this._kind = kind;
        this._callee = callee;
      }
      public RefutedAnnotationKind Kind {
        get { return this._kind; }
      }
      public string Constant {
        get { return this._constant; }
      }
      public Procedure CalleeProc {
        get { return this._callee; }
      }
      public static RefutedAnnotation BuildRefutedRequires(string constant, Procedure callee) {
        return new RefutedAnnotation(constant, RefutedAnnotationKind.REQUIRES, callee);
      }
      public static RefutedAnnotation BuildRefutedEnsures(string constant) {
        return new RefutedAnnotation(constant, RefutedAnnotationKind.ENSURES, null);
      }
      public static RefutedAnnotation BuildRefutedAssert(string constant) {
        return new RefutedAnnotation(constant, RefutedAnnotationKind.ASSERT, null);
      }

    }

    private void PrintRefutedCall(CallCounterexample err, XmlSink xmlOut) {
      Expr cond = err.FailingRequires.Condition;
      string houdiniConst;
      if (MatchCandidate(cond, out houdiniConst)) {
        xmlOut.WriteError("precondition violation", err.FailingCall.tok, err.FailingRequires.tok, err.Trace);
      }
    }

    private void PrintRefutedReturn(ReturnCounterexample err, XmlSink xmlOut) {
      Expr cond = err.FailingEnsures.Condition;
      string houdiniConst;
      if (MatchCandidate(cond, out houdiniConst)) {
        xmlOut.WriteError("postcondition violation", err.FailingReturn.tok, err.FailingEnsures.tok, err.Trace);
      }
    }

    private void PrintRefutedAssert(AssertCounterexample err, XmlSink xmlOut) {
      Expr cond = err.FailingAssert.OrigExpr;
      string houdiniConst;
      if (MatchCandidate(cond, out houdiniConst)) {
        xmlOut.WriteError("postcondition violation", err.FailingAssert.tok, err.FailingAssert.tok, err.Trace);
      }
    }


    private void DebugRefutedCandidates(Implementation curFunc, List<Counterexample> errors) {
      XmlSink xmlRefuted = CommandLineOptions.Clo.XmlRefuted;
      if (xmlRefuted != null && errors != null) {
        DateTime start = DateTime.UtcNow;
        xmlRefuted.WriteStartMethod(curFunc.ToString(), start);

        foreach (Counterexample error in errors) {
          CallCounterexample ce = error as CallCounterexample;
          if (ce != null) PrintRefutedCall(ce, xmlRefuted);
          ReturnCounterexample re = error as ReturnCounterexample;
          if (re != null) PrintRefutedReturn(re, xmlRefuted);
          AssertCounterexample ae = error as AssertCounterexample;
          if (ae != null) PrintRefutedAssert(ae, xmlRefuted);
        }

        DateTime end = DateTime.UtcNow;
        xmlRefuted.WriteEndMethod("errors", end, end.Subtract(start));
      }
    }

    private RefutedAnnotation ExtractRefutedAnnotation(Counterexample error) {
      string houdiniConstant;
      CallCounterexample callCounterexample = error as CallCounterexample;
      if (callCounterexample != null) {
        Procedure failingProcedure = callCounterexample.FailingCall.Proc;
        Requires failingRequires = callCounterexample.FailingRequires;
        if (MatchCandidate(failingRequires.Condition, out houdiniConstant)) {
          Contract.Assert(houdiniConstant != null);
          return RefutedAnnotation.BuildRefutedRequires(houdiniConstant, failingProcedure);
        }
      }
      ReturnCounterexample returnCounterexample = error as ReturnCounterexample;
      if (returnCounterexample != null) {
        Ensures failingEnsures = returnCounterexample.FailingEnsures;
        if (MatchCandidate(failingEnsures.Condition, out houdiniConstant)) {
          Contract.Assert(houdiniConstant != null);
          return RefutedAnnotation.BuildRefutedEnsures(houdiniConstant);
        }
      }
      AssertCounterexample assertCounterexample = error as AssertCounterexample;
      if (assertCounterexample != null) {
        AssertCmd failingAssert = assertCounterexample.FailingAssert;
        if (MatchCandidate(failingAssert.OrigExpr, out houdiniConstant)) {
          Contract.Assert(houdiniConstant != null);
          return RefutedAnnotation.BuildRefutedAssert(houdiniConstant);
        }
      }

      return null;
    }

    private ProverInterface.Outcome TryCatchVerify(HoudiniSession session, VCExpr axiom, out List<Counterexample> errors) {
      ProverInterface.Outcome outcome;
      try {
        outcome = session.Verify(checker, axiom, out errors);
      }
      catch (VCGenException e) {
        Contract.Assume(e != null);
        errors = null;
        outcome = ProverInterface.Outcome.Undetermined;
      }
      catch (UnexpectedProverOutputException upo) {
        Contract.Assume(upo != null);
        errors = null;
        outcome = ProverInterface.Outcome.Undetermined;
      }
      return outcome;
    }

    

    //Similar to TrySpinSameFunc except no Candidate logic
    private ProverInterface.Outcome HoudiniVerifyCurrentAux(
                                          HoudiniSession session,
                                          HoudiniState current,
                                          Program program,
                                          out List<Counterexample> errors,
                                          out bool exceptional) {
      Contract.Assert(current.Implementation != null);
      ProverInterface.Outcome outcome;
      // the following initialization is there just to satisfy the compiler 
      // which apparently does not understand the semantics of do-while statements
      errors = null;
      outcome = ProverInterface.Outcome.Undetermined;

      try {
        bool trySameFunc = true;
        bool pastFirstIter = false; //see if this new loop is even helping

        do {
          errors = null;
          outcome = ProverInterface.Outcome.Undetermined;

          if (pastFirstIter) {
            //System.GC.Collect();
            this.NotifyIteration();
          }

          VCExpr currentAx = BuildAxiom(current.Assignment);
          this.NotifyAssignment(current.Assignment);

          //check the VC with the current assignment
          outcome = session.Verify(checker, currentAx, out errors);
          this.NotifyOutcome(outcome);

          DebugRefutedCandidates(current.Implementation, errors);
          UpdateHoudiniOutcome(current.Outcome, current.Implementation, outcome, errors);

          if (AnyNonCandidateViolation(outcome, errors)) { //abort
            current.WorkQueue.Dequeue();
            this.NotifyDequeue();
            trySameFunc = false;
            FlushWorkList(current);
          }
          else { //continue
            trySameFunc = UpdateAssignmentWorkList(current, outcome, errors);
          }
          pastFirstIter = true;
        } while (trySameFunc && current.WorkQueue.Count > 0);
      }
      catch (VCGenException e) {
        Contract.Assume(e != null);
        NotifyException("VCGen");
        exceptional = true;
        return outcome;
      }
      catch (UnexpectedProverOutputException upo) {
        Contract.Assume(upo != null);
        NotifyException("UnexpectedProverOutput");
        exceptional = true;
        return outcome;
      }
      exceptional = false;
      return outcome;
    }
  }

  public enum HoudiniOutcomeKind { Done, FatalError, VerificationCompleted }

  public class VCGenOutcome {
    public VCGen.Outcome outcome;
    public List<Counterexample> errors;
    public VCGenOutcome(ProverInterface.Outcome outcome, List<Counterexample> errors) {
      switch (outcome) {
        case ProverInterface.Outcome.Invalid:
          this.outcome = ConditionGeneration.Outcome.Errors;
          break;
        case ProverInterface.Outcome.OutOfMemory:
          this.outcome = ConditionGeneration.Outcome.OutOfMemory;
          break;
        case ProverInterface.Outcome.TimeOut:
          this.outcome = ConditionGeneration.Outcome.TimedOut;
          break;
        case ProverInterface.Outcome.Undetermined:
          this.outcome = ConditionGeneration.Outcome.Inconclusive;
          break;
        case ProverInterface.Outcome.Valid:
          this.outcome = ConditionGeneration.Outcome.Correct;
          break;
      }
      this.errors = errors;
    }
  }

  public class HoudiniOutcome {
    // final assignment
    public Dictionary<string, bool> assignment = new Dictionary<string, bool>();
    // boogie errors
    public Dictionary<string, VCGenOutcome> implementationOutcomes = new Dictionary<string, VCGenOutcome>();
    // outcome kind    
    public HoudiniOutcomeKind kind;

    // statistics 

    private int CountResults(VCGen.Outcome outcome) {
      int outcomeCount = 0;
      foreach (VCGenOutcome verifyOutcome in implementationOutcomes.Values) {
        if (verifyOutcome.outcome == outcome)
          outcomeCount++;
      }
      return outcomeCount;
    }

    private List<string> ListOutcomeMatches(VCGen.Outcome outcome) {
      List<string> result = new List<string>();
      foreach (KeyValuePair<string, VCGenOutcome> kvpair in implementationOutcomes) {
        if (kvpair.Value.outcome == outcome)
          result.Add(kvpair.Key);
      }
      return result;
    }

    public int ErrorCount {
      get {
        return CountResults(VCGen.Outcome.Errors);
      }
    }
    public int Verified {
      get {
        return CountResults(VCGen.Outcome.Correct);
      }
    }
    public int Inconclusives {
      get {
        return CountResults(VCGen.Outcome.Inconclusive);
      }
    }
    public int TimeOuts {
      get {
        return CountResults(VCGen.Outcome.TimedOut);
      }
    }
    public List<string> ListOfTimeouts {
      get {
        return ListOutcomeMatches(VCGen.Outcome.TimedOut);
      }
    }
    public List<string> ListOfInconclusives {
      get {
        return ListOutcomeMatches(VCGen.Outcome.Inconclusive);
      }
    }
    public List<string> ListOfErrors {
      get {
        return ListOutcomeMatches(VCGen.Outcome.Errors);
      }
    }
  }

}
