//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Linq;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Text.RegularExpressions;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Basetypes;
using System.Threading.Tasks;

namespace Microsoft.Boogie {

  enum CheckerStatus
  {
    Idle,
    Ready,
    Busy,
    Closed
  }

  /// <summary>
  /// Interface to the theorem prover specialized to Boogie.
  ///
  /// This class creates the appropriate background axioms.  There
  /// should be one instance per BoogiePL program.
  /// </summary>
  public sealed class Checker {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(gen != null);
      Contract.Invariant(thmProver != null);
    }

    private readonly VCExpressionGenerator gen;

    private ProverInterface thmProver;
    private int timeout;
    private int rlimit;

    // state for the async interface
    private volatile ProverInterface.Outcome outcome;
    private volatile bool hasOutput;
    private volatile UnexpectedProverOutputException outputExn;
    private DateTime proverStart;
    private TimeSpan proverRunTime;
    private volatile ProverInterface.ErrorHandler handler;
    private volatile CheckerStatus status;
    public volatile Program Program;

    public void GetReady()
    {
      Contract.Requires(IsIdle);

      status = CheckerStatus.Ready;
    }

    public void GoBackToIdle()
    {
      Contract.Requires(IsBusy);

      status = CheckerStatus.Idle;
    }

    public Task ProverTask { get; set; }

    public bool WillingToHandle(int timeout, int rlimit, Program prog) {
      return status == CheckerStatus.Idle && timeout == this.timeout && rlimit == this.rlimit && (prog == null || Program == prog);
    }

    public VCExpressionGenerator VCExprGen {
      get {
        Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);
        return this.gen;
      }
    }
    public ProverInterface TheoremProver {
      get {
        Contract.Ensures(Contract.Result<ProverInterface>() != null);
        return this.thmProver;
      }
    }

    /////////////////////////////////////////////////////////////////////////////////
    // We share context information for the same program between different Checkers

    private struct ContextCacheKey {
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(program != null);
      }

      public readonly Program program;

      public ContextCacheKey(Program prog) {
        Contract.Requires(prog != null);
        this.program = prog;
      }

      [Pure]
      [Reads(ReadsAttribute.Reads.Nothing)]
      public override bool Equals(object that) {
        if (that is ContextCacheKey) {
          ContextCacheKey thatKey = (ContextCacheKey)that;
          return this.program.Equals(thatKey.program);
        }
        return false;
      }

      [Pure]
      public override int GetHashCode() {
        return this.program.GetHashCode();
      }
    }

    /////////////////////////////////////////////////////////////////////////////////

    /// <summary>
    /// Constructor.  Initialize a checker with the program and log file.
    /// Optionally, use prover context provided by parameter "ctx". 
    /// </summary>
    public Checker(VC.ConditionGeneration vcgen, Program prog, string/*?*/ logFilePath, bool appendLogFile, int timeout, int rlimit = 0, ProverContext ctx = null) {
      Contract.Requires(vcgen != null);
      Contract.Requires(prog != null);
      this.timeout = timeout;
      this.rlimit = rlimit;
      this.Program = prog;

      ProverOptions options = cce.NonNull(CommandLineOptions.Clo.TheProverFactory).BlankProverOptions();

      if (logFilePath != null) {
        options.LogFilename = logFilePath;
        if (appendLogFile)
          options.AppendLogFile = appendLogFile;
      }

      if (timeout > 0) {
        options.TimeLimit = timeout * 1000;
      }

      if (rlimit > 0) {
        options.ResourceLimit = rlimit;
      } else {
        options.ResourceLimit = 0;
      }

      options.Parse(CommandLineOptions.Clo.ProverOptions);

      ContextCacheKey key = new ContextCacheKey(prog);
      ProverInterface prover;

      if (vcgen.CheckerCommonState == null) {
        vcgen.CheckerCommonState = new Dictionary<ContextCacheKey, ProverContext>();
      }
      IDictionary<ContextCacheKey, ProverContext>/*!>!*/ cachedContexts = (IDictionary<ContextCacheKey, ProverContext/*!*/>)vcgen.CheckerCommonState;

      if (ctx == null && cachedContexts.TryGetValue(key, out ctx))
      {
        ctx = (ProverContext)cce.NonNull(ctx).Clone();
        prover = (ProverInterface)
          CommandLineOptions.Clo.TheProverFactory.SpawnProver(options, ctx);
      } else {
        if (ctx == null) ctx = (ProverContext)CommandLineOptions.Clo.TheProverFactory.NewProverContext(options);

        Setup(prog, ctx);

        // we first generate the prover and then store a clone of the
        // context in the cache, so that the prover can setup stuff in
        // the context to be cached
        prover = (ProverInterface)
          CommandLineOptions.Clo.TheProverFactory.SpawnProver(options, ctx);
        cachedContexts.Add(key, cce.NonNull((ProverContext)ctx.Clone()));
      }

      this.thmProver = prover;
      this.gen = prover.VCExprGen;
    }

    public void Retarget(Program prog, ProverContext ctx, int timeout = 0, int rlimit = 0)
    {
      lock (this)
      {
        hasOutput = default(bool);
        outcome = default(ProverInterface.Outcome);
        outputExn = default(UnexpectedProverOutputException);
        handler = default(ProverInterface.ErrorHandler);
        TheoremProver.FullReset(gen);
        ctx.Reset();
        Setup(prog, ctx);
        this.timeout = timeout;
        SetTimeout();
        this.rlimit = rlimit;
        SetRlimit();
      }
    }

    public void RetargetWithoutReset(Program prog, ProverContext ctx)
    {
        ctx.Clear();
        Setup(prog, ctx);
    }


    public void SetTimeout()
    {
      if (0 < timeout)
      {
        TheoremProver.SetTimeOut(timeout * 1000);
      }
      else
      {
        TheoremProver.SetTimeOut(0);
      }
    }

    public void SetRlimit()
    {
      if (0 < rlimit) {
        TheoremProver.SetRlimit(rlimit);
      }
      else 
      {
        TheoremProver.SetRlimit(0);
      }
    }

    /// <summary>
    /// Set up the context.
    /// </summary>
    private void Setup(Program prog, ProverContext ctx)
    {
      Program = prog;
      // TODO(wuestholz): Is this lock necessary?
      lock (Program.TopLevelDeclarations)
      {
        foreach (Declaration decl in Program.TopLevelDeclarations)
        {
          Contract.Assert(decl != null);
          var typeDecl = decl as TypeCtorDecl;
          var constDecl = decl as Constant;
          var funDecl = decl as Function;
          var axiomDecl = decl as Axiom;
          var glVarDecl = decl as GlobalVariable;
          if (typeDecl != null)
          {
            ctx.DeclareType(typeDecl, null);
          }
          else if (constDecl != null)
          {
            ctx.DeclareConstant(constDecl, constDecl.Unique, null);
          }
          else if (funDecl != null)
          {
            ctx.DeclareFunction(funDecl, null);
          }
          else if (axiomDecl != null)
          {
            ctx.AddAxiom(axiomDecl, null);
          }
          else if (glVarDecl != null)
          {
            ctx.DeclareGlobalVariable(glVarDecl, null);
          }
        }
      }
    }

    /// <summary>
    /// Clean-up.
    /// </summary>
    public void Close() {      
      thmProver.Close();
      status = CheckerStatus.Closed;
    }

    /// <summary>
    /// Push a Verification Condition as an Axiom 
    /// (Required for Doomed Program Point detection)
    /// </summary>
    public void PushVCExpr(VCExpr vc) {
      Contract.Requires(vc != null);
      //thmProver.Context.AddAxiom(vc);
      thmProver.PushVCExpression(vc);
    }

    public bool IsBusy {
      get {
        return status == CheckerStatus.Busy;
      }
    }

    public bool IsReady
    {
      get
      {
        return status == CheckerStatus.Ready;
      }
    }

    public bool IsClosed {
      get {
        return status == CheckerStatus.Closed;
      }
    }

    public bool IsIdle
    {
      get
      {
        return status == CheckerStatus.Idle;
      }
    }

    public bool HasOutput {
      get {
        return hasOutput;
      }
    }

    public TimeSpan ProverRunTime {
      get {
        return proverRunTime;
      }
    }

    private void WaitForOutput(object dummy) {
      lock (this)
      {
        try {
          outcome = thmProver.CheckOutcome(cce.NonNull(handler));
        } catch (UnexpectedProverOutputException e) {
          outputExn = e;
        } catch (Exception e) {
          outputExn = new UnexpectedProverOutputException(e.Message);
        }

        switch (outcome)
        {
          case ProverInterface.Outcome.Valid:
            thmProver.LogComment("Valid");
            break;
          case ProverInterface.Outcome.Invalid:
            thmProver.LogComment("Invalid");
            break;
          case ProverInterface.Outcome.TimeOut:
            thmProver.LogComment("Timed out");
            break;
          case ProverInterface.Outcome.OutOfResource:
            thmProver.LogComment("Out of resource");
            break;
          case ProverInterface.Outcome.OutOfMemory:
            thmProver.LogComment("Out of memory");
            break;
          case ProverInterface.Outcome.Undetermined:
            thmProver.LogComment("Undetermined");
            break;
        }

        hasOutput = true;
        proverRunTime = DateTime.UtcNow - proverStart;
      }
    }

    public void BeginCheck(string descriptiveName, VCExpr vc, ProverInterface.ErrorHandler handler) {
      Contract.Requires(descriptiveName != null);
      Contract.Requires(vc != null);
      Contract.Requires(handler != null);
      Contract.Requires(IsReady);

      status = CheckerStatus.Busy;
      hasOutput = false;
      outputExn = null;
      this.handler = handler;
      
      thmProver.Reset(gen);
      SetTimeout();
      proverStart = DateTime.UtcNow;
      thmProver.BeginCheck(descriptiveName, vc, handler);
      //  gen.ClearSharedFormulas();    PR: don't know yet what to do with this guy

      ProverTask = Task.Factory.StartNew(() => { WaitForOutput(null); }, TaskCreationOptions.LongRunning);
    }

    public ProverInterface.Outcome ReadOutcome() {
      Contract.Requires(IsBusy);
      Contract.Requires(HasOutput);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      hasOutput = false;

      if (outputExn != null) {
        throw outputExn;
      }

      return outcome;
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public abstract class ProverInterface {

    public static ProverInterface CreateProver(Program prog, string/*?*/ logFilePath, bool appendLogFile, int timeout, int taskID = -1) {
      Contract.Requires(prog != null);

      ProverOptions options = cce.NonNull(CommandLineOptions.Clo.TheProverFactory).BlankProverOptions();

      if (logFilePath != null) {
        options.LogFilename = logFilePath;
        if (appendLogFile)
          options.AppendLogFile = appendLogFile;
      }

      if (timeout > 0) {
        options.TimeLimit = timeout * 1000;
      }

      if (taskID >= 0) {
        options.Parse(CommandLineOptions.Clo.Cho[taskID].ProverOptions);
      } else {
        options.Parse(CommandLineOptions.Clo.ProverOptions);
      }

      ProverContext ctx = (ProverContext)CommandLineOptions.Clo.TheProverFactory.NewProverContext(options);

      // set up the context
      foreach (Declaration decl in prog.TopLevelDeclarations) {
        Contract.Assert(decl != null);
        TypeCtorDecl t = decl as TypeCtorDecl;
        if (t != null) {
          ctx.DeclareType(t, null);
        }
      }
      foreach (Declaration decl in prog.TopLevelDeclarations) {
        Contract.Assert(decl != null);
        Constant c = decl as Constant;
        if (c != null) {
          ctx.DeclareConstant(c, c.Unique, null);
        }
        else {
          Function f = decl as Function;
          if (f != null) {
            ctx.DeclareFunction(f, null);
          }
        }
      }
      foreach (var ax in prog.Axioms) {
        ctx.AddAxiom(ax, null);
      }
      foreach (Declaration decl in prog.TopLevelDeclarations) {
        Contract.Assert(decl != null);
        GlobalVariable v = decl as GlobalVariable;
        if (v != null) {
          ctx.DeclareGlobalVariable(v, null);
        }
      }

      return (ProverInterface)CommandLineOptions.Clo.TheProverFactory.SpawnProver(options, ctx);
    }

    public enum Outcome {
      Valid,
      Invalid,
      TimeOut,
      OutOfMemory,
      OutOfResource,
      Undetermined,
      Bounded
    }

    public readonly ISet<VCExprVar> NamedAssumes = new HashSet<VCExprVar>();
    public ISet<string> UsedNamedAssumes { get; protected set; }

    public class ErrorHandler {
      // Used in CheckOutcomeCore
      public virtual int StartingProcId()
      {
          return 0;
      }

      public virtual void OnModel(IList<string> labels, Model model, Outcome proverOutcome) {
        Contract.Requires(cce.NonNullElements(labels));
      }

      public virtual void OnResourceExceeded(string message, IEnumerable<Tuple<AssertCmd, TransferCmd>> assertCmds = null) {
        Contract.Requires(message != null);
      }

      public virtual void OnProverWarning(string message)
      {
        Contract.Requires(message != null);
        switch (CommandLineOptions.Clo.PrintProverWarnings) {
          case CommandLineOptions.ProverWarnings.None:
            break;
          case CommandLineOptions.ProverWarnings.Stdout:
            Console.WriteLine("Prover warning: " + message);
            break;
          case CommandLineOptions.ProverWarnings.Stderr:
            Console.Error.WriteLine("Prover warning: " + message);
            break;
          default:
            Contract.Assume(false);
            throw new cce.UnreachableException();  // unexpected case
        }
      }

      public virtual void OnProverError(string message)
      {
            // no-op by default. 
            //Errors are always printed to console by the prover
      }

      public virtual Absy Label2Absy(string label) {
        Contract.Requires(label != null);
        Contract.Ensures(Contract.Result<Absy>() != null);

        throw new System.NotImplementedException();
      }
    }
    public abstract void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler);
    
    public virtual Outcome CheckRPFP(string descriptiveName, RPFP vc, ErrorHandler handler,
                                     out RPFP.Node cex,
                                     Dictionary<int, Dictionary<string, string>> varSubst, Dictionary<string,int> extra_bound = null)
    {
        throw new System.NotImplementedException();
    }
    [NoDefaultContract]
    public abstract Outcome CheckOutcome(ErrorHandler handler, int taskID = -1);
    public virtual string[] CalculatePath(int controlFlowConstant) {
      throw new System.NotImplementedException();
    }
    public virtual void LogComment(string comment) {
      Contract.Requires(comment != null);
    }
    public virtual void Close() {
    }

    public abstract void Reset(VCExpressionGenerator gen);

    public abstract void FullReset(VCExpressionGenerator gen);

    /// <summary>
    /// MSchaef: Allows to Push a VCExpression as Axiom on the prover stack (beta)
    /// for now it is only implemented by ProcessTheoremProver and still requires some
    /// testing
    /// </summary>    
    public virtual void PushVCExpression(VCExpr vc) {
      Contract.Requires(vc != null);
      throw new NotImplementedException();
    }
    public virtual string VCExpressionToString(VCExpr vc) {
      Contract.Requires(vc != null);
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();
    }
    public virtual void Pop() {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      throw new NotImplementedException();
    }
    public virtual int NumAxiomsPushed() {
      throw new NotImplementedException();
    }
    public virtual int FlushAxiomsToTheoremProver() {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      throw new NotImplementedException();
    }

    // (assert vc)
    public virtual void Assert(VCExpr vc, bool polarity, bool isSoft = false, int weight = 1, string name = null)
    {
        throw new NotImplementedException();
    }

    public virtual List<string> UnsatCore()
    {
        throw new NotImplementedException();
    }


    // (assert implicit-axioms)
    public virtual void AssertAxioms()
    {
        throw new NotImplementedException();
    }

    // (check-sat)
    public virtual void Check()
    {
        throw new NotImplementedException();
    }

    // (check-sat + get-unsat-core + checkOutcome)
    public virtual Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore, ErrorHandler handler)
    {
        throw new NotImplementedException();
    }

    public virtual Outcome CheckAssumptions(List<VCExpr> hardAssumptions, List<VCExpr> softAssumptions, out List<int> unsatisfiedSoftAssumptions, ErrorHandler handler) {
      throw new NotImplementedException();
    }

    public virtual Outcome CheckOutcomeCore(ErrorHandler handler, int taskID = -1)
    {
        throw new NotImplementedException();
    }

    // (push 1)
    public virtual void Push()
    {
        throw new NotImplementedException();
    }

    // Set theorem prover timeout for the next "check-sat"
    public virtual void SetTimeOut(int ms)
    { }

    public virtual void SetRlimit(int limit)
    { }

    public abstract ProverContext Context {
      get;
    }

    public abstract VCExpressionGenerator VCExprGen {
      get;
    }

    public virtual void DefineMacro(Macro fun, VCExpr vc) {
      throw new NotImplementedException();
    }

    public class VCExprEvaluationException : Exception
    {

    }

    public virtual object Evaluate(VCExpr expr)
    {
        throw new NotImplementedException();
    }

    //////////////////////
    // For interpolation queries
    //////////////////////

    // Assert vc tagged with a name
    public virtual void AssertNamed(VCExpr vc, bool polarity, string name)
    {
        throw new NotImplementedException();
    }

    // Returns Interpolant(A,B)
    public virtual VCExpr ComputeInterpolant(VCExpr A, VCExpr B)
    {
        throw new NotImplementedException();
    }

    // Returns for each l, Interpolant(root + (leaves - l), l)
    // Preconditions:
    //    leaves cannot have subformulas with same variable names
    //    Both root and leaves should have been previously named via AssertNamed
    public virtual List<VCExpr> GetTreeInterpolant(List<string> root, List<string> leaves)
    {
        throw new NotImplementedException();
    }

  }

  public class ProverInterfaceContracts : ProverInterface {
    public override ProverContext Context {
      get {
        Contract.Ensures(Contract.Result<ProverContext>() != null);

        throw new NotImplementedException();
      }
    }
    public override VCExpressionGenerator VCExprGen {
      get {
        Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);

        throw new NotImplementedException();
      }
    }
    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler) {/*Contract.Requires(descriptiveName != null);*/
      //Contract.Requires(vc != null);
      //Contract.Requires(handler != null);
      throw new NotImplementedException();
    }
    [NoDefaultContract]
    public override Outcome CheckOutcome(ErrorHandler handler, int taskID = -1) {
      //Contract.Requires(handler != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      throw new NotImplementedException();
    }

    public override void Reset(VCExpressionGenerator gen)
    {
      throw new NotImplementedException();
    }

    public override void FullReset(VCExpressionGenerator gen)
    {
      throw new NotImplementedException();
    }
  }

  public class ProverException : Exception {
    public ProverException(string s)
      : base(s) {
    }
  }
  public class UnexpectedProverOutputException : ProverException {
    public UnexpectedProverOutputException(string s)
      : base(s) {
    }
  }
  public class ProverDiedException : UnexpectedProverOutputException {
    public ProverDiedException()
      : base("Prover died with no further output, perhaps it ran out of memory or was killed.") {
    }
  }
}
