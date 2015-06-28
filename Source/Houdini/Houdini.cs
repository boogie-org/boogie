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
using Microsoft.Boogie.GraphUtil;
using System.Linq;
using System.Diagnostics;

namespace Microsoft.Boogie.Houdini {

  internal class ReadOnlyDictionary<K, V> {
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
    public virtual void UpdateAssignment(Dictionary<Variable, bool> assignment) { }
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
    public override void UpdateAssignment(Dictionary<Variable, bool> assignment) {
      bool firstTime = true;
      wr.Write("assignment under analysis : axiom (");
      foreach (KeyValuePair<Variable, bool> kv in assignment) {
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
    protected void NotifyAssignment(Dictionary<Variable, bool> assignment) {
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

  public class InlineEnsuresVisitor : ReadOnlyVisitor {
      public override Ensures VisitEnsures(Ensures ensures)
      {
          if (!ensures.Free)
          {
              ensures.Attributes = new QKeyValue(Token.NoToken, "InlineAssume", new List<object>(), ensures.Attributes);
          }
          return base.VisitEnsures(ensures);
      }
  }

  public class Houdini : ObservableHoudini {
    protected Program program;
    protected HashSet<Variable> houdiniConstants;
    protected VCGen vcgen;
    protected ProverInterface proverInterface;
    protected Graph<Implementation> callGraph;
    protected HashSet<Implementation> vcgenFailures;
    protected HoudiniState currentHoudiniState;
    protected CrossDependencies crossDependencies;
    internal ReadOnlyDictionary<Implementation, HoudiniSession> houdiniSessions;

    protected string cexTraceFile;

    public HoudiniState CurrentHoudiniState { get { return currentHoudiniState; } }    

    public static TextWriter explainHoudiniDottyFile;

    protected Houdini() { }

    public Houdini(Program program, HoudiniSession.HoudiniStatistics stats, string cexTraceFile = "houdiniCexTrace.txt") {
      this.program = program;
      this.cexTraceFile = cexTraceFile;
      Initialize(program, stats);
    }

    protected void Initialize(Program program, HoudiniSession.HoudiniStatistics stats)
    {
        if (CommandLineOptions.Clo.Trace)
            Console.WriteLine("Collecting existential constants...");
        this.houdiniConstants = CollectExistentialConstants();

        if (CommandLineOptions.Clo.Trace)
            Console.WriteLine("Building call graph...");
        this.callGraph = Program.BuildCallGraph(program);
        if (CommandLineOptions.Clo.Trace)
            Console.WriteLine("Number of implementations = {0}", callGraph.Nodes.Count);

        if (CommandLineOptions.Clo.HoudiniUseCrossDependencies)
        {
            if (CommandLineOptions.Clo.Trace) Console.WriteLine("Computing procedure cross dependencies ...");
            this.crossDependencies = new CrossDependencies(this.houdiniConstants);
            this.crossDependencies.Visit(program);
        }

        Inline();
        /*
        {
            int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
            CommandLineOptions.Clo.PrintUnstructured = 1;
            using (TokenTextWriter stream = new TokenTextWriter("houdini_inline.bpl"))
            {
                program.Emit(stream);
            }
            CommandLineOptions.Clo.PrintUnstructured = oldPrintUnstructured;
        }
        */

        this.vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, new List<Checker>());
        this.proverInterface = ProverInterface.CreateProver(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, CommandLineOptions.Clo.ProverKillTime, taskID: GetTaskID());

        vcgenFailures = new HashSet<Implementation>();
        Dictionary<Implementation, HoudiniSession> houdiniSessions = new Dictionary<Implementation, HoudiniSession>();
        if (CommandLineOptions.Clo.Trace)
            Console.WriteLine("Beginning VC generation for Houdini...");
        foreach (Implementation impl in callGraph.Nodes)
        {
            try
            {
                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Generating VC for {0}", impl.Name);
                HoudiniSession session = new HoudiniSession(this, vcgen, proverInterface, program, impl, stats, taskID: GetTaskID());
                houdiniSessions.Add(impl, session);
            }
            catch (VCGenException)
            {
                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("VC generation failed");
                vcgenFailures.Add(impl);
            }
        }
        this.houdiniSessions = new ReadOnlyDictionary<Implementation, HoudiniSession>(houdiniSessions);

        if (CommandLineOptions.Clo.ExplainHoudini)
        {
            // Print results of ExplainHoudini to a dotty file
            explainHoudiniDottyFile = new StreamWriter("explainHoudini.dot");
            explainHoudiniDottyFile.WriteLine("digraph explainHoudini {");
            foreach (var constant in houdiniConstants)
                explainHoudiniDottyFile.WriteLine("{0} [ label = \"{0}\" color=black ];", constant.Name);
            explainHoudiniDottyFile.WriteLine("TimeOut [label = \"TimeOut\" color=red ];");
        }
    }

    protected void Inline() {
      if (CommandLineOptions.Clo.InlineDepth <= 0)
        return;

      foreach (Implementation impl in callGraph.Nodes) {
        InlineEnsuresVisitor inlineEnsuresVisitor = new InlineEnsuresVisitor();
        inlineEnsuresVisitor.Visit(impl);
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

    protected HashSet<Variable> CollectExistentialConstants() {
      HashSet<Variable> existentialConstants = new HashSet<Variable>();
      foreach (var constant in program.Constants) {
        bool result = false;
        if (constant.CheckBooleanAttribute("existential", ref result)) {
          if (result == true)
            existentialConstants.Add(constant);
        }
      }
      return existentialConstants;
    }

      // Compute dependencies between candidates
    public class CrossDependencies : ReadOnlyVisitor
    {
        public CrossDependencies(HashSet<Variable> constants)
        {
            this.constants = constants;
        }

        public override Program VisitProgram(Program node)
        {
            assumedInImpl = new Dictionary<string, HashSet<Implementation>>();
            return base.VisitProgram(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            curImpl = node;
            return base.VisitImplementation(node);
        }

        public override Cmd VisitAssumeCmd(AssumeCmd node)
        {
            return base.VisitAssumeCmd(node);
        }

        public override Variable VisitVariable(Variable node)
        {
            if (node is Constant)
            {
                var constant = node as Constant;
                if (constants.Contains(constant))
                {
                    if (!assumedInImpl.ContainsKey(constant.Name))
                        assumedInImpl[constant.Name] = new HashSet<Implementation>();
                    assumedInImpl[constant.Name].Add(curImpl);
                }
            }
            return base.VisitVariable(node);
        }

        HashSet<Variable> constants;
        Implementation curImpl;

        // contant -> set of implementations that have an assume command with that constant
        public Dictionary<string, HashSet<Implementation>> assumedInImpl { get; private set; }
    }
    
    protected WorkQueue BuildWorkList(Program program) {
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
      if (CommandLineOptions.Clo.ReverseHoudiniWorklist)
          queue = queue.Reverse();
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

    public static bool MatchCandidate(Expr boogieExpr, IEnumerable<string> candidates, out string candidateConstant) {
      candidateConstant = null;
      NAryExpr e = boogieExpr as NAryExpr;
      if (e != null && e.Fun is BinaryOperator && ((BinaryOperator)e.Fun).Op == BinaryOperator.Opcode.Imp) {
        Expr antecedent = e.Args[0];
        Expr consequent = e.Args[1];

        IdentifierExpr id = antecedent as IdentifierExpr;
        if (id != null && id.Decl is Constant && candidates.Contains(id.Decl.Name)) {
          candidateConstant = id.Decl.Name;
          return true;
        }

        if (MatchCandidate(consequent, candidates, out candidateConstant))
          return true;
      }
      return false;
    }

    public static bool GetCandidateWithoutConstant(Expr boogieExpr, IEnumerable<string> candidates, out string candidateConstant, out Expr exprWithoutConstant) {
      candidateConstant = null;
      exprWithoutConstant = null;
      NAryExpr e = boogieExpr as NAryExpr;
      if (e != null && e.Fun is BinaryOperator && ((BinaryOperator)e.Fun).Op == BinaryOperator.Opcode.Imp) {
        Expr antecedent = e.Args[0];
        Expr consequent = e.Args[1];

        IdentifierExpr id = antecedent as IdentifierExpr;
        if (id != null && id.Decl is Constant && candidates.Contains(id.Decl.Name)) {
          candidateConstant = id.Decl.Name;
          exprWithoutConstant = consequent;
          return true;
        }

        if (GetCandidateWithoutConstant(consequent, candidates, out candidateConstant, out exprWithoutConstant))
        {
            exprWithoutConstant = Expr.Imp(antecedent, exprWithoutConstant);
            return true;
        }
      }
      return false;
    }

    private static Expr AddConditionToCandidateRec(Expr boogieExpr, Expr condition, string candidateConstant, List<Expr> implicationStack)
    {
        NAryExpr e = boogieExpr as NAryExpr;
        if (e != null && e.Fun is BinaryOperator && ((BinaryOperator)e.Fun).Op == BinaryOperator.Opcode.Imp)
        {
            Expr antecedent = e.Args[0];
            Expr consequent = e.Args[1];

            IdentifierExpr id = antecedent as IdentifierExpr;
            if (id != null && id.Decl is Constant && id.Decl.Name.Equals(candidateConstant))
            {
                Expr result = Expr.Imp(antecedent, Expr.Imp(condition, consequent));
                implicationStack.Reverse();
                foreach (var expr in implicationStack)
                {
                    result = Expr.Imp(expr, result);
                }
                return result;
            }

            implicationStack.Add(antecedent);
            return AddConditionToCandidateRec(consequent, condition, candidateConstant,
                implicationStack);
        }
        return boogieExpr;
    }

    public static Expr AddConditionToCandidate(Expr boogieExpr, Expr condition, string candidateConstant)
    {
        return AddConditionToCandidateRec(boogieExpr, condition, candidateConstant, new List<Expr>());
    }

    public bool MatchCandidate(Expr boogieExpr, out Variable candidateConstant) {
      candidateConstant = null;
      string candidateString;
      if(MatchCandidate(boogieExpr, houdiniConstants.Select(item => item.Name), out candidateString)) {
        candidateConstant = houdiniConstants.Where(item => item.Name.Equals(candidateString)).ToList()[0];
        return true;
      }
      return false;
    }

    public bool MatchCandidate(Expr boogieExpr, out string candidateConstant) {
      return MatchCandidate(boogieExpr, houdiniConstants.Select(item => item.Name), out candidateConstant);
    }

    // For Explain houdini: it decorates the condition \phi as (vpos && (\phi || \not vneg))
    // Precondition: MatchCandidate returns true
    public Expr InsertCandidateControl(Expr boogieExpr, Variable vpos, Variable vneg)
    {
        Contract.Assert(CommandLineOptions.Clo.ExplainHoudini);

        NAryExpr e = boogieExpr as NAryExpr;
        if (e != null && e.Fun is BinaryOperator && ((BinaryOperator)e.Fun).Op == BinaryOperator.Opcode.Imp)
        {
            Expr antecedent = e.Args[0];
            Expr consequent = e.Args[1];

            IdentifierExpr id = antecedent as IdentifierExpr;
            if (id != null && id.Decl is Constant && houdiniConstants.Contains((Constant)id.Decl))
            {
                return Expr.Imp(antecedent, Expr.And(Expr.Ident(vpos), Expr.Or(consequent, Expr.Not(Expr.Ident(vneg)))));
            }

            return Expr.Imp(antecedent, InsertCandidateControl(consequent, vpos, vneg));
        }
        Contract.Assert(false);
        return null;
    }

    protected Dictionary<Variable, bool> BuildAssignment(HashSet<Variable> constants) {
      Dictionary<Variable, bool> initial = new Dictionary<Variable, bool>();
      foreach (var constant in constants)
        initial.Add(constant, true);
      return initial;
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

    // Record most current non-candidate errors found
    // Return true if there was at least one non-candidate error
    protected bool UpdateHoudiniOutcome(HoudiniOutcome houdiniOutcome,
                                      Implementation implementation,
                                      ProverInterface.Outcome outcome,
                                      List<Counterexample> errors) {
      string implName = implementation.Name;
      houdiniOutcome.implementationOutcomes.Remove(implName);
      List<Counterexample> nonCandidateErrors = new List<Counterexample>();

      if (outcome == ProverInterface.Outcome.Invalid) {
          foreach (Counterexample error in errors) {
            if (ExtractRefutedAnnotation(error) == null)
              nonCandidateErrors.Add(error);
          }
      }
      houdiniOutcome.implementationOutcomes.Add(implName, new VCGenOutcome(outcome, nonCandidateErrors));
      return nonCandidateErrors.Count > 0;
    }

    protected void FlushWorkList(int stage, IEnumerable<int> completedStages) {
      this.NotifyFlushStart();
      while (currentHoudiniState.WorkQueue.Count > 0) {
        this.NotifyIteration();

        currentHoudiniState.Implementation = currentHoudiniState.WorkQueue.Peek();
        this.NotifyImplementation(currentHoudiniState.Implementation);

        HoudiniSession session;
        houdiniSessions.TryGetValue(currentHoudiniState.Implementation, out session);
        List<Counterexample> errors;
        ProverInterface.Outcome outcome = TryCatchVerify(session, stage, completedStages, out errors);
        UpdateHoudiniOutcome(currentHoudiniState.Outcome, currentHoudiniState.Implementation, outcome, errors);
        this.NotifyOutcome(outcome);

        currentHoudiniState.WorkQueue.Dequeue();
        this.NotifyDequeue();
      }
      this.NotifyFlushFinish();
    }

    protected void UpdateAssignment(RefutedAnnotation refAnnot) {
      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Removing " + refAnnot.Constant);
        using (var cexWriter = new System.IO.StreamWriter(cexTraceFile, true))
            cexWriter.WriteLine("Removing " + refAnnot.Constant);
      }
      currentHoudiniState.Assignment.Remove(refAnnot.Constant);
      currentHoudiniState.Assignment.Add(refAnnot.Constant, false);
      this.NotifyConstant(refAnnot.Constant.Name);
    }

    protected void AddRelatedToWorkList(RefutedAnnotation refutedAnnotation) {
      Contract.Assume(currentHoudiniState.Implementation != null);
      foreach (Implementation implementation in FindImplementationsToEnqueue(refutedAnnotation, refutedAnnotation.RefutationSite)) {
        if (!currentHoudiniState.isBlackListed(implementation.Name)) {
          currentHoudiniState.WorkQueue.Enqueue(implementation);
          this.NotifyEnqueue(implementation);
        }
      }
    }

    // Updates the worklist and current assignment
    // @return true if the current function is dequeued
    protected bool UpdateAssignmentWorkList(ProverInterface.Outcome outcome,
                                          List<Counterexample> errors) {
      Contract.Assume(currentHoudiniState.Implementation != null);
      bool dequeue = true;

      switch (outcome) {
        case ProverInterface.Outcome.Valid:
          //yeah, dequeue
          break;

        case ProverInterface.Outcome.Invalid:
            Contract.Assume(errors != null);

            foreach (Counterexample error in errors) {
              RefutedAnnotation refutedAnnotation = ExtractRefutedAnnotation(error);
              if (refutedAnnotation != null) {
                // some candidate annotation removed
                ShareRefutedAnnotation(refutedAnnotation);
                AddRelatedToWorkList(refutedAnnotation);
                UpdateAssignment(refutedAnnotation);
                dequeue = false;
                #region Extra debugging output
                if (CommandLineOptions.Clo.Trace) {
                  using (var cexWriter = new System.IO.StreamWriter(cexTraceFile, true)) {
                    cexWriter.WriteLine("Counter example for " + refutedAnnotation.Constant);
                    cexWriter.Write(error.ToString());
                    cexWriter.WriteLine();
                    using (var writer = new Microsoft.Boogie.TokenTextWriter(cexWriter, /*pretty=*/ false))
                      foreach (Microsoft.Boogie.Block blk in error.Trace)
                        blk.Emit(writer, 15);
                    //cexWriter.WriteLine(); 
                  }
                }
                #endregion
              }
            }
              
            if (ExchangeRefutedAnnotations()) dequeue = false;

            break;
        default:
            if (CommandLineOptions.Clo.Trace) {
                Console.WriteLine("Timeout/Spaceout while verifying " + currentHoudiniState.Implementation.Name);
            }
            HoudiniSession houdiniSession;
            houdiniSessions.TryGetValue(currentHoudiniState.Implementation, out houdiniSession);
            foreach (Variable v in houdiniSession.houdiniAssertConstants) {
                if (CommandLineOptions.Clo.Trace) {
                    Console.WriteLine("Removing " + v);
                }
                currentHoudiniState.Assignment.Remove(v);
                currentHoudiniState.Assignment.Add(v, false);
                this.NotifyConstant(v.Name);
            }
            currentHoudiniState.addToBlackList(currentHoudiniState.Implementation.Name);
            break;
      }
      
      return dequeue;
    }

    // This method is a hook used by ConcurrentHoudini to
    // exchange refuted annotations with other Houdini engines.
    // If the method returns true, this indicates that at least
    // one new refutation was received from some other engine.
    // In the base class we thus return false.
    protected virtual bool ExchangeRefutedAnnotations() {
      return false;
    }

    // This method is a hook used by ConcurrentHoudini to
    // apply a set of existing refuted annotations at the
    // start of inference.
    protected virtual void ApplyRefutedSharedAnnotations() {
      // Empty in base class; can be overridden.
    }

    // This method is a hook used by ConcurrentHoudini to
    // broadcast to other Houdini engines the fact that an
    // annotation was refuted.
    protected virtual void ShareRefutedAnnotation(RefutedAnnotation refutedAnnotation) {
      // Empty in base class; can be overridden.
    }

    // Hook for ConcurrentHoudini, which requires a task id.
    // Non-concurrent Houdini has -1 as a task id
    protected virtual int GetTaskID() {
      return -1;
    }

    public class WorkQueue {
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
      public WorkQueue Reverse()
      {
          var ret = new WorkQueue();
          foreach (var impl in queue.Reverse())
              ret.Enqueue(impl);
          return ret;
      }
    }

    public class HoudiniState {
      public WorkQueue _workQueue;
      public HashSet<string> blackList;
      public Dictionary<Variable, bool> _assignment;
      public Implementation _implementation;
      public HoudiniOutcome _outcome;

      public HoudiniState(WorkQueue workQueue, Dictionary<Variable, bool> currentAssignment) {
        this._workQueue = workQueue;
        this._assignment = currentAssignment;
        this._implementation = null;
        this._outcome = new HoudiniOutcome();
        this.blackList = new HashSet<string>();
      }

      public WorkQueue WorkQueue {
        get { return this._workQueue; }
      }
      public Dictionary<Variable, bool> Assignment {
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

    public HoudiniOutcome PerformHoudiniInference(int stage = 0, 
                                                  IEnumerable<int> completedStages = null,
                                                  Dictionary<string, bool> initialAssignment = null) {
      this.NotifyStart(program, houdiniConstants.Count);

      currentHoudiniState = new HoudiniState(BuildWorkList(program), BuildAssignment(houdiniConstants));

      if(initialAssignment != null) {
        foreach(var v in CurrentHoudiniState.Assignment.Keys.ToList()) {
          CurrentHoudiniState.Assignment[v] = initialAssignment[v.Name];
        }
      }

      ApplyRefutedSharedAnnotations();

      foreach (Implementation impl in vcgenFailures) {
        currentHoudiniState.addToBlackList(impl.Name);
      }

      while (currentHoudiniState.WorkQueue.Count > 0) {
        this.NotifyIteration();

        currentHoudiniState.Implementation = currentHoudiniState.WorkQueue.Peek();
        this.NotifyImplementation(currentHoudiniState.Implementation);

        HoudiniSession session;
        this.houdiniSessions.TryGetValue(currentHoudiniState.Implementation, out session);
        HoudiniVerifyCurrent(session, stage, completedStages);
      }

      this.NotifyEnd(true);
      Dictionary<string, bool> assignment = new Dictionary<string, bool>();
      foreach (var x in currentHoudiniState.Assignment)
        assignment[x.Key.Name] = x.Value;
      currentHoudiniState.Outcome.assignment = assignment;
      return currentHoudiniState.Outcome;
    }

    public void Close() {
      vcgen.Close();
      proverInterface.Close();
      if (CommandLineOptions.Clo.ExplainHoudini)
      {
          explainHoudiniDottyFile.WriteLine("};");
          explainHoudiniDottyFile.Close();
      }
    }

    private int NumberOfStages()
    {
      int result = 1;
      foreach(var c in program.Constants) {
        result = Math.Max(result, 1 + QKeyValue.FindIntAttribute(c.Attributes, "stage_active", -1));
      }
      return result;
    }

    private List<Implementation> FindImplementationsToEnqueue(RefutedAnnotation refutedAnnotation, Implementation currentImplementation) {
      HoudiniSession session;
      List<Implementation> implementations = new List<Implementation>();
      switch (refutedAnnotation.Kind) {
        case RefutedAnnotationKind.REQUIRES:
              foreach (Implementation callee in callGraph.Successors(currentImplementation))
              {
                  if (vcgenFailures.Contains(callee)) continue;
                  houdiniSessions.TryGetValue(callee, out session);
                  Contract.Assume(callee.Proc != null);
                  if (callee.Proc.Equals(refutedAnnotation.CalleeProc) && session.InUnsatCore(refutedAnnotation.Constant))
                      implementations.Add(callee);
              }
          break;
        case RefutedAnnotationKind.ENSURES:
          foreach (Implementation caller in callGraph.Predecessors(currentImplementation))
          {
              if (vcgenFailures.Contains(caller)) continue;
              houdiniSessions.TryGetValue(caller, out session);
              if (session.InUnsatCore(refutedAnnotation.Constant))
                  implementations.Add(caller);
          }
          break;
        case RefutedAnnotationKind.ASSERT: //the implementation is already in queue
          if (CommandLineOptions.Clo.HoudiniUseCrossDependencies && crossDependencies.assumedInImpl.ContainsKey(refutedAnnotation.Constant.Name))
          {
              foreach (var impl in crossDependencies.assumedInImpl[refutedAnnotation.Constant.Name])
              {
                  if (vcgenFailures.Contains(impl)) continue;
                  houdiniSessions.TryGetValue(impl, out session);
                  if (session.InUnsatCore(refutedAnnotation.Constant))
                      implementations.Add(impl);
              }
          }
          break;
        default:
          throw new Exception("Unknown Refuted annotation kind:" + refutedAnnotation.Kind);
      }
      return implementations;
    }

    public enum RefutedAnnotationKind { REQUIRES, ENSURES, ASSERT };

    public class RefutedAnnotation {
      private Variable _constant;
      private RefutedAnnotationKind _kind;
      private Procedure _callee;
      private Implementation _refutationSite;

      private RefutedAnnotation(Variable constant, RefutedAnnotationKind kind, Procedure callee, Implementation refutationSite) {
        this._constant = constant;
        this._kind = kind;
        this._callee = callee;
        this._refutationSite = refutationSite;
      }
      public RefutedAnnotationKind Kind {
        get { return this._kind; }
      }
      public Variable Constant {
        get { return this._constant; }
      }
      public Procedure CalleeProc {
        get { return this._callee; }
      }
      public Implementation RefutationSite {
        get { return this._refutationSite; }
      }
      public static RefutedAnnotation BuildRefutedRequires(Variable constant, Procedure callee, Implementation refutationSite) {
        return new RefutedAnnotation(constant, RefutedAnnotationKind.REQUIRES, callee, refutationSite);
      }
      public static RefutedAnnotation BuildRefutedEnsures(Variable constant, Implementation refutationSite) {
        return new RefutedAnnotation(constant, RefutedAnnotationKind.ENSURES, null, refutationSite);
      }
      public static RefutedAnnotation BuildRefutedAssert(Variable constant, Implementation refutationSite) {
        return new RefutedAnnotation(constant, RefutedAnnotationKind.ASSERT, null, refutationSite);
      }

      public override int GetHashCode()
      {
        unchecked {
          int hash = 17;
          hash = hash * 23 + this.Constant.GetHashCode();
          hash = hash * 23 + this.Kind.GetHashCode();
          if (this.CalleeProc != null)
            hash = hash * 23 + this.CalleeProc.GetHashCode();
          hash = hash * 23 + this.RefutationSite.GetHashCode();
          return hash;
        }
      }

      public override bool Equals(object obj) {
        bool result = true;
        var other = obj as RefutedAnnotation;

        if (other == null) {
          result = false;
        } else {
          result = result && String.Equals(other.Constant, this.Constant);
          result = result && String.Equals(other.Kind, this.Kind);
          if (other.CalleeProc != null && this.CalleeProc != null)
            result = result && String.Equals(other.CalleeProc, this.CalleeProc);
          result = result && String.Equals(other.RefutationSite, this.RefutationSite);
        }

        return result;
      }
    }

    private void PrintRefutedCall(CallCounterexample err, XmlSink xmlOut) {
      Expr cond = err.FailingRequires.Condition;
      Variable houdiniConst;
      if (MatchCandidate(cond, out houdiniConst)) {
        xmlOut.WriteError("precondition violation", err.FailingCall.tok, err.FailingRequires.tok, err.Trace);
      }
    }

    private void PrintRefutedReturn(ReturnCounterexample err, XmlSink xmlOut) {
      Expr cond = err.FailingEnsures.Condition;
      Variable houdiniConst;
      if (MatchCandidate(cond, out houdiniConst)) {
        xmlOut.WriteError("postcondition violation", err.FailingReturn.tok, err.FailingEnsures.tok, err.Trace);
      }
    }

    private void PrintRefutedAssert(AssertCounterexample err, XmlSink xmlOut) {
      Expr cond = err.FailingAssert.OrigExpr;
      Variable houdiniConst;
      if (MatchCandidate(cond, out houdiniConst)) {
        xmlOut.WriteError("postcondition violation", err.FailingAssert.tok, err.FailingAssert.tok, err.Trace);
      }
    }

    protected void DebugRefutedCandidates(Implementation curFunc, List<Counterexample> errors) {
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
      Variable houdiniConstant;
      CallCounterexample callCounterexample = error as CallCounterexample;
      if (callCounterexample != null) {
        Procedure failingProcedure = callCounterexample.FailingCall.Proc;
        Requires failingRequires = callCounterexample.FailingRequires;
        if (MatchCandidate(failingRequires.Condition, out houdiniConstant)) {
          Contract.Assert(houdiniConstant != null);
          return RefutedAnnotation.BuildRefutedRequires(houdiniConstant, failingProcedure, currentHoudiniState.Implementation);
        }
      }
      ReturnCounterexample returnCounterexample = error as ReturnCounterexample;
      if (returnCounterexample != null) {
        Ensures failingEnsures = returnCounterexample.FailingEnsures;
        if (MatchCandidate(failingEnsures.Condition, out houdiniConstant)) {
          Contract.Assert(houdiniConstant != null);
          return RefutedAnnotation.BuildRefutedEnsures(houdiniConstant, currentHoudiniState.Implementation);
        }
      }
      AssertCounterexample assertCounterexample = error as AssertCounterexample;
      if (assertCounterexample != null) {
        AssertCmd failingAssert = assertCounterexample.FailingAssert;
        if (MatchCandidate(failingAssert.OrigExpr, out houdiniConstant)) {
          Contract.Assert(houdiniConstant != null);
          return RefutedAnnotation.BuildRefutedAssert(houdiniConstant, currentHoudiniState.Implementation);
        }
      }

      return null;
    }

    private ProverInterface.Outcome TryCatchVerify(HoudiniSession session, int stage, IEnumerable<int> completedStages, out List<Counterexample> errors) {
      ProverInterface.Outcome outcome;
      try {
        outcome = session.Verify(proverInterface, GetAssignmentWithStages(stage, completedStages), out errors, taskID: GetTaskID());
      }
      catch (UnexpectedProverOutputException upo) {
        Contract.Assume(upo != null);
        errors = null;
        outcome = ProverInterface.Outcome.Undetermined;
      }
      return outcome;
    }

    protected Dictionary<Variable, bool> GetAssignmentWithStages(int currentStage, IEnumerable<int> completedStages)
    {
      Dictionary<Variable, bool> result = new Dictionary<Variable, bool>(currentHoudiniState.Assignment);
      foreach (var c in program.Constants)
      {
        int stageActive = QKeyValue.FindIntAttribute(c.Attributes, "stage_active", -1);
        if (stageActive != -1)
        {
          result[c] = (stageActive == currentStage);
        }
        int stageComplete = QKeyValue.FindIntAttribute(c.Attributes, "stage_complete", -1);
        if (stageComplete != -1)
        {
          result[c] = (completedStages.Contains(stageComplete));
        }
      }
      return result;
    }

    private void HoudiniVerifyCurrent(HoudiniSession session, int stage, IEnumerable<int> completedStages) {
      while (true) {
        this.NotifyAssignment(currentHoudiniState.Assignment);

        //check the VC with the current assignment
        List<Counterexample> errors;
        ProverInterface.Outcome outcome = TryCatchVerify(session, stage, completedStages, out errors);
        this.NotifyOutcome(outcome);

        DebugRefutedCandidates(currentHoudiniState.Implementation, errors);

        #region Explain Houdini
        if (CommandLineOptions.Clo.ExplainHoudini && outcome == ProverInterface.Outcome.Invalid)
        {
            Contract.Assume(errors != null);
            // make a copy of this variable
            errors = new List<Counterexample>(errors);
            var refutedAnnotations = new List<RefutedAnnotation>();
            foreach (Counterexample error in errors)
            {
                RefutedAnnotation refutedAnnotation = ExtractRefutedAnnotation(error);
                if (refutedAnnotation == null || refutedAnnotation.Kind == RefutedAnnotationKind.ASSERT) continue;
                refutedAnnotations.Add(refutedAnnotation);
            }
            foreach (var refutedAnnotation in refutedAnnotations)
            {
                session.Explain(proverInterface, currentHoudiniState.Assignment, refutedAnnotation.Constant);
            }
        }
        #endregion

        if (UpdateHoudiniOutcome(currentHoudiniState.Outcome, currentHoudiniState.Implementation, outcome, errors)) { // abort
          currentHoudiniState.WorkQueue.Dequeue();
          this.NotifyDequeue();
          FlushWorkList(stage, completedStages);
          return;
        }
        else if (UpdateAssignmentWorkList(outcome, errors)) {
          if (CommandLineOptions.Clo.UseUnsatCoreForContractInfer && outcome == ProverInterface.Outcome.Valid)
            session.UpdateUnsatCore(proverInterface, currentHoudiniState.Assignment);
          currentHoudiniState.WorkQueue.Dequeue();
          this.NotifyDequeue();
          return;
        }
      } 
    }

    /// <summary>
    /// Transforms given program based on Houdini outcome.  If a constant is assigned "true",
    /// any preconditions or postconditions guarded by the constant are made free, and any assertions 
    /// guarded by the constant are replaced with assumptions.
    /// 
    /// If a constant is assigned "false", any preconditions or postconditions
    /// guarded by the constant are replaced with "true", and assertions guarded by the constant
    /// are removed.
    /// 
    /// In addition, all Houdini constants are removed from the program.
    /// </summary>
    public static void ApplyAssignment(Program prog, HoudiniOutcome outcome) {

      var Candidates = prog.TopLevelDeclarations.OfType<Constant>().Where
            (Item => QKeyValue.FindBoolAttribute(Item.Attributes, "existential")).Select(Item => Item.Name);

      // Treat all assertions
      // TODO: do we need to also consider assumptions?
      foreach (Block block in prog.Implementations.Select(item => item.Blocks).SelectMany(item => item)) {
        List<Cmd> newCmds = new List<Cmd>();
        foreach (Cmd cmd in block.Cmds) {
          string c;
          AssertCmd assertCmd = cmd as AssertCmd;
          if (assertCmd != null && MatchCandidate(assertCmd.Expr, Candidates, out c)) {
            var cVar = outcome.assignment.Keys.Where(item => item.Equals(c)).ToList()[0];
            if (outcome.assignment[cVar]) {
              Dictionary<Variable, Expr> cToTrue = new Dictionary<Variable, Expr>();
              Variable cVarProg = prog.Variables.Where(item => item.Name.Equals(c)).ToList()[0];
              cToTrue[cVarProg] = Expr.True;
              newCmds.Add(new AssumeCmd(assertCmd.tok,
                Substituter.Apply(Substituter.SubstitutionFromHashtable(cToTrue), assertCmd.Expr),
                assertCmd.Attributes));
            }
          }
          else {
            newCmds.Add(cmd);
          }
        }
        block.Cmds = newCmds;
      }

      foreach (var proc in prog.Procedures) {
        List<Requires> newRequires = new List<Requires>();
        foreach (Requires r in proc.Requires) {
          string c;
          if (MatchCandidate(r.Condition, Candidates, out c)) {
            var cVar = outcome.assignment.Keys.Where(item => item.Equals(c)).ToList()[0];
            if (outcome.assignment[cVar]) {
              Variable cVarProg = prog.Variables.Where(item => item.Name.Equals(c)).ToList()[0];
              Dictionary<Variable, Expr> subst = new Dictionary<Variable, Expr>();
              subst[cVarProg] = Expr.True;
              newRequires.Add(new Requires(Token.NoToken, true,
                Substituter.Apply(Substituter.SubstitutionFromHashtable(subst), r.Condition),
                r.Comment, r.Attributes));
            }
          }
          else {
            newRequires.Add(r);
          }
        }
        proc.Requires = newRequires;

        List<Ensures> newEnsures = new List<Ensures>();
        foreach (Ensures e in proc.Ensures) {
          string c;
          if (MatchCandidate(e.Condition, Candidates, out c)) {
            var cVar = outcome.assignment.Keys.Where(item => item.Equals(c)).ToList()[0];
            if (outcome.assignment[cVar]) {
              Variable cVarProg = prog.Variables.Where(item => item.Name.Equals(c)).ToList()[0];
              Dictionary<Variable, Expr> subst = new Dictionary<Variable, Expr>();
              subst[cVarProg] = Expr.True;
              newEnsures.Add(new Ensures(Token.NoToken, true,
                Substituter.Apply(Substituter.SubstitutionFromHashtable(subst), e.Condition),
                e.Comment, e.Attributes));
            }
          }
          else {
            newEnsures.Add(e);
          }
        }
        proc.Ensures = newEnsures;
      }

      // Remove the existential constants
      prog.RemoveTopLevelDeclarations(item => (item is Constant) && 
               (Candidates.Any(item2 => item2.Equals((item as Constant).Name))));
    }

  }

  public class VCGenOutcome {
    public VCGen.Outcome outcome;
    public List<Counterexample> errors;
    public VCGenOutcome(ProverInterface.Outcome outcome, List<Counterexample> errors) {
      this.outcome = ConditionGeneration.ProverInterfaceOutcomeToConditionGenerationOutcome(outcome);
      this.errors = errors;
    }
  }

  public class HoudiniOutcome {
    // final assignment
    public Dictionary<string, bool> assignment = new Dictionary<string, bool>();
    // boogie errors
    public Dictionary<string, VCGenOutcome> implementationOutcomes = new Dictionary<string, VCGenOutcome>();

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
