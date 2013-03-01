//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
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

namespace Microsoft.Boogie {
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
      Contract.Invariant(ProverDone != null);
    }

    private readonly VCExpressionGenerator gen;

    private ProverInterface thmProver;
    private int timeout;

    // state for the async interface
    private volatile ProverInterface.Outcome outcome;
    private volatile bool busy;
    private volatile bool hasOutput;
    private volatile UnexpectedProverOutputException outputExn;
    private DateTime proverStart;
    private TimeSpan proverRunTime;
    private volatile ProverInterface.ErrorHandler handler;
    private volatile bool closed;

    public readonly AutoResetEvent ProverDone = new AutoResetEvent(false);

    public bool WillingToHandle(Implementation impl, int timeout) {
      return !closed && timeout == this.timeout;
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
    public Checker(VC.ConditionGeneration vcgen, Program prog, string/*?*/ logFilePath, bool appendLogFile, int timeout, ProverContext ctx = null) {
      Contract.Requires(vcgen != null);
      Contract.Requires(prog != null);
      this.timeout = timeout;

      ProverOptions options = cce.NonNull(CommandLineOptions.Clo.TheProverFactory).BlankProverOptions();

      if (logFilePath != null) {
        options.LogFilename = logFilePath;
        if (appendLogFile)
          options.AppendLogFile = appendLogFile;
      }

      if (timeout > 0) {
        options.TimeLimit = timeout * 1000;
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
          } else {
            Function f = decl as Function;
            if (f != null) {
              ctx.DeclareFunction(f, null);
            }
          }
        }
        foreach (Declaration decl in prog.TopLevelDeclarations) {
          Contract.Assert(decl != null);
          Axiom ax = decl as Axiom;
          if (ax != null) {
            ctx.AddAxiom(ax, null);
          }
        }
        foreach (Declaration decl in prog.TopLevelDeclarations) {
          Contract.Assert(decl != null);
          GlobalVariable v = decl as GlobalVariable;
          if (v != null) {
            ctx.DeclareGlobalVariable(v, null);
          }
        }

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


    /// <summary>
    /// Clean-up.
    /// </summary>
    public void Close() {
      this.closed = true;
      thmProver.Close();
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
        return busy;
      }
    }

    public bool Closed {
      get {
        return closed;
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
      try {
        outcome = thmProver.CheckOutcome(cce.NonNull(handler));
      } catch (UnexpectedProverOutputException e) {
        outputExn = e;
      }

      switch (outcome) {
        case ProverInterface.Outcome.Valid:
          thmProver.LogComment("Valid");
          break;
        case ProverInterface.Outcome.Invalid:
          thmProver.LogComment("Invalid");
          break;
        case ProverInterface.Outcome.TimeOut:
          thmProver.LogComment("Timed out");
          break;
        case ProverInterface.Outcome.OutOfMemory:
          thmProver.LogComment("Out of memory");
          break;
        case ProverInterface.Outcome.Undetermined:
          thmProver.LogComment("Undetermined");
          break;
      }

      Contract.Assert(busy);
      hasOutput = true;
      proverRunTime = DateTime.UtcNow - proverStart;

      ProverDone.Set();
    }

    public void BeginCheck(string descriptiveName, VCExpr vc, ProverInterface.ErrorHandler handler) {
      Contract.Requires(descriptiveName != null);
      Contract.Requires(vc != null);
      Contract.Requires(handler != null);

      Contract.Requires(!IsBusy);
      Contract.Assert(!busy);
      busy = true;
      hasOutput = false;
      outputExn = null;
      this.handler = handler;

      proverStart = DateTime.UtcNow;
      thmProver.BeginCheck(descriptiveName, vc, handler);
      //  gen.ClearSharedFormulas();    PR: don't know yet what to do with this guy

      ThreadPool.QueueUserWorkItem(WaitForOutput);
    }

    public ProverInterface.Outcome ReadOutcome() {

      Contract.Requires(IsBusy);
      Contract.Requires(HasOutput);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      hasOutput = false;
      busy = false;

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
    public static ProverInterface CreateProver(Program prog, string/*?*/ logFilePath, bool appendLogFile, int timeout) {
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

      options.Parse(CommandLineOptions.Clo.ProverOptions);

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
      foreach (Declaration decl in prog.TopLevelDeclarations) {
        Contract.Assert(decl != null);
        Axiom ax = decl as Axiom;
        if (ax != null) {
          ctx.AddAxiom(ax, null);
        }
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
      Undetermined
    }
    public class ErrorHandler {
      // Used in CheckOutcomeCore
      public virtual int StartingProcId()
      {
          return 0;
      }

      public virtual void OnModel(IList<string> labels, Model model) {
        Contract.Requires(cce.NonNullElements(labels));
      }

      public virtual void OnResourceExceeded(string message) {
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

      public virtual Absy Label2Absy(string label) {
        Contract.Requires(label != null);
        Contract.Ensures(Contract.Result<Absy>() != null);

        throw new System.NotImplementedException();
      }
    }
    public abstract void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler);
    [NoDefaultContract]
    public abstract Outcome CheckOutcome(ErrorHandler handler);
    public virtual string[] CalculatePath(int controlFlowConstant) {
      throw new System.NotImplementedException();
    }
    public virtual void LogComment(string comment) {
      Contract.Requires(comment != null);
    }
    public virtual void Close() {
    }

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
    public virtual void Assert(VCExpr vc, bool polarity)
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

    public virtual Outcome CheckOutcomeCore(ErrorHandler handler)
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
    public override Outcome CheckOutcome(ErrorHandler handler) {
      //Contract.Requires(handler != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
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
