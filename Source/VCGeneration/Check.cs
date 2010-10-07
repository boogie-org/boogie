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
    private CommandLineOptions.BvHandling bitvectors;
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

    private static CommandLineOptions.BvHandling BvHandlingForImpl(Implementation impl) {
      if (impl == null)
        return CommandLineOptions.Clo.Bitvectors;
      bool force_int = false;
      bool force_native = false;
      cce.NonNull(impl.Proc).CheckBooleanAttribute("forceBvInt", ref force_int);
      impl.Proc.CheckBooleanAttribute("forceBvZ3Native", ref force_native);
      impl.CheckBooleanAttribute("forceBvInt", ref force_int);
      impl.CheckBooleanAttribute("forceBvZ3Native", ref force_native);
      if (force_native)
        return CommandLineOptions.BvHandling.Z3Native;
      if (force_int)
        return CommandLineOptions.BvHandling.ToInt;
      return CommandLineOptions.Clo.Bitvectors;
    }

    public bool WillingToHandle(Implementation impl, int timeout) {
      return !closed && timeout == this.timeout && bitvectors == BvHandlingForImpl(impl);
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
      public readonly CommandLineOptions.BvHandling bitvectors;

      public ContextCacheKey(Program prog,
                             CommandLineOptions.BvHandling bitvectors) {
        Contract.Requires(prog != null);
        this.program = prog;
        this.bitvectors = bitvectors;
      }

      [Pure]
      [Reads(ReadsAttribute.Reads.Nothing)]
      public override bool Equals(object that) {
        if (that is ContextCacheKey) {
          ContextCacheKey thatKey = (ContextCacheKey)that;
          return this.program.Equals(thatKey.program) &&
                 this.bitvectors.Equals(thatKey.bitvectors);
        }
        return false;
      }

      [Pure]
      public override int GetHashCode() {
        return this.program.GetHashCode() + this.bitvectors.GetHashCode();
      }
    }

    /////////////////////////////////////////////////////////////////////////////////

    /// <summary>
    /// Constructor.  Initialize a checker with the program and log file.
    /// </summary>
    public Checker(VC.ConditionGeneration vcgen, Program prog, string/*?*/ logFilePath, bool appendLogFile, Implementation impl, int timeout) {
      Contract.Requires(vcgen != null);
      Contract.Requires(prog != null);
      this.bitvectors = BvHandlingForImpl(impl);
      this.timeout = timeout;

      ProverOptions options = cce.NonNull(CommandLineOptions.Clo.TheProverFactory).BlankProverOptions();

      if (logFilePath != null) {
        options.LogFilename = logFilePath;
        if (appendLogFile)
          options.AppendLogFile = appendLogFile;
      }

      options.Parse(CommandLineOptions.Clo.ProverOptions);

      if (timeout > 0) {
        options.TimeLimit = timeout * 1000;
      }
      options.BitVectors = this.bitvectors;

      ContextCacheKey key = new ContextCacheKey(prog, this.bitvectors);
      ProverContext ctx;
      ProverInterface prover;

      if (vcgen.CheckerCommonState == null) {
        vcgen.CheckerCommonState = new Dictionary<ContextCacheKey, ProverContext>();
      }
      IDictionary<ContextCacheKey, ProverContext>/*!>!*/ cachedContexts = (IDictionary<ContextCacheKey, ProverContext/*!*/>)vcgen.CheckerCommonState;

      if (cachedContexts.TryGetValue(key, out ctx)) {
        ctx = (ProverContext)cce.NonNull(ctx).Clone();
        prover = (ProverInterface)
          CommandLineOptions.Clo.TheProverFactory.SpawnProver(options, ctx);
      } else {
        ctx = (ProverContext)CommandLineOptions.Clo.TheProverFactory.NewProverContext(options);

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
          bool expand = false;
          Axiom ax = decl as Axiom;
          decl.CheckBooleanAttribute("inline", ref expand);
          if (!expand && ax != null) {
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

      // base();
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
      proverRunTime = DateTime.Now - proverStart;

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

      proverStart = DateTime.Now;
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

  public class ErrorModel {
    public Dictionary<string/*!*/, int>/*!*/ identifierToPartition;
    public List<List<string/*!>>!*/>> partitionToIdentifiers;
    public List<Object>/*!*/ partitionToValue;
    public Dictionary<object, int>/*!*/ valueToPartition;
    public Dictionary<string/*!*/, List<List<int>>/*!*/>/*!*/ definedFunctions;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(identifierToPartition));
      Contract.Invariant(partitionToIdentifiers != null);
      Contract.Invariant(Contract.ForAll(partitionToIdentifiers, i => cce.NonNullElements(i)));
      Contract.Invariant(partitionToValue != null);
      Contract.Invariant(valueToPartition != null);
      Contract.Invariant(cce.NonNullElements(definedFunctions));
    }


    public ErrorModel(Dictionary<string, int> identifierToPartition, List<List<string>> partitionToIdentifiers, List<Object> partitionToValue, Dictionary<object, int> valueToPartition, Dictionary<string, List<List<int>>> definedFunctions) {
      Contract.Requires(cce.NonNullElements(identifierToPartition));
      Contract.Requires(partitionToIdentifiers != null);
      Contract.Requires(Contract.ForAll(partitionToIdentifiers, i => cce.NonNullElements(i)));
      Contract.Requires(partitionToValue != null);
      Contract.Requires(valueToPartition != null);
      Contract.Requires(cce.NonNullElements(definedFunctions));
      this.identifierToPartition = identifierToPartition;
      this.partitionToIdentifiers = partitionToIdentifiers;
      this.partitionToValue = partitionToValue;
      this.valueToPartition = valueToPartition;
      this.definedFunctions = definedFunctions;
    }

    public virtual void Print(TextWriter writer) {
      Contract.Requires(writer != null);
    }

    public int LookupPartitionValue(int partition) {
      BigNum bignum = (BigNum)cce.NonNull(partitionToValue[partition]);
      return bignum.ToInt;
    }

    public int LookupControlFlowFunctionAt(int cfc, int id) {
      List<List<int>> tuples = this.definedFunctions["ControlFlow"];
      Contract.Assert(tuples != null);
      foreach (List<int> tuple in tuples) {
        if (tuple == null)
          continue;
        if (tuple.Count != 3)
          continue;
        if (LookupPartitionValue(tuple[0]) == cfc && LookupPartitionValue(tuple[1]) == id)
          return LookupPartitionValue(tuple[2]);
      }
      Contract.Assert(false);
      throw new cce.UnreachableException();
    }

    private string LookupSkolemConstant(string name) {
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<string>() != null);

      foreach (string functionName in identifierToPartition.Keys) {
        Contract.Assert(functionName != null);

        int index = functionName.LastIndexOf("!");
        if (index == -1)
          continue;
        string newFunctionName = cce.NonNull(functionName.Remove(index));
        if (newFunctionName.Equals(name))
          return functionName;
      }
      return "";
    }
    private string LookupSkolemFunction(string name) {
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<string>() != null);

      foreach (string functionName in definedFunctions.Keys) {
        Contract.Assert(functionName != null);
        int index = functionName.LastIndexOf("!");
        if (index == -1)
          continue;
        string newFunctionName = cce.NonNull(functionName.Remove(index));
        if (newFunctionName.Equals(name))
          return functionName;
      }
      return "";
    }
    public int LookupSkolemFunctionAt(string functionName, List<int> values) {
      Contract.Requires(functionName != null);
      Contract.Requires(values != null);

      string actualFunctionName = LookupSkolemFunction(functionName);
      Contract.Assert(actualFunctionName != null);
      if (actualFunctionName.Equals("")) {
        // The skolem function is actually a skolem constant
        actualFunctionName = LookupSkolemConstant(functionName);
        Contract.Assert(!actualFunctionName.Equals(""));
        return identifierToPartition[actualFunctionName];
      }
      List<List<int>> tuples = this.definedFunctions[actualFunctionName];
      Contract.Assert(tuples.Count > 0);
      // the last tuple is a dummy tuple
      for (int n = 0; n < tuples.Count - 1; n++) {
        List<int> tuple = cce.NonNull(tuples[n]);
        Contract.Assert(tuple.Count - 1 <= values.Count);
        for (int i = 0, j = 0; i < values.Count; i++) {
          if (values[i] == tuple[j]) {
            // succeeded in matching tuple[j]
            j++;
            if (j == tuple.Count - 1)
              return tuple[tuple.Count - 1];
          }
        }
      }
      Contract.Assert(false);
      throw new cce.UnreachableException();
    }

    public List<object>/*!>!*/ PartitionsToValues(List<int> args) {
      Contract.Requires(args != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<object>>()));

      List<object> vals = new List<object>();
      foreach (int i in args) {
        object o = cce.NonNull(partitionToValue[i]);
        if (o is bool) {
          vals.Add(o);
        } else if (o is BigNum) {
          vals.Add(o);
        } else if (o is List<List<int>>) {
          List<List<int>> array = (List<List<int>>)o;
          List<List<object>> arrayVal = new List<List<object>>();
          foreach (List<int> tuple in array) {
            Contract.Assert(tuple != null);

            List<object> tupleVal = new List<object>();
            foreach (int j in tuple) {
              tupleVal.Add(cce.NonNull(partitionToValue[i]));
            }
            arrayVal.Add(tupleVal);
          }
          vals.Add(arrayVal);
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }
      return vals;
    }
  }

  public abstract class ProverInterface {
    public enum Outcome {
      Valid,
      Invalid,
      TimeOut,
      OutOfMemory,
      Undetermined
    }
    public class ErrorHandler {
      public virtual void OnModel(IList<string>/*!>!*/ labels, ErrorModel errModel) {
        Contract.Requires(cce.NonNullElements(labels));
      }

      public virtual void OnResourceExceeded(string message) {
        Contract.Requires(message != null);
      }

      public virtual void OnProverWarning(string message)
        //modifies Console.Out.*, Console.Error.*;
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
    }
    public virtual string VCExpressionToString(VCExpr vc) {
      Contract.Requires(vc != null);
      Contract.Ensures(Contract.Result<string>() != null);
      return "";
    }
    public virtual void Pop() {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
    }
    public virtual int NumAxiomsPushed() {
      return 0;
    }
    public virtual int FlushAxiomsToTheoremProver() {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      return 0;
    }


    public abstract ProverContext Context {
      get;
    }
    public abstract VCExpressionGenerator VCExprGen {
      get;
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
