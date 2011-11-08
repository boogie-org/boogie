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
    /// </summary>
    public Checker(VC.ConditionGeneration vcgen, Program prog, string/*?*/ logFilePath, bool appendLogFile, Implementation impl, int timeout) {
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

  // This class will go away soon. Use Model class instead.
  public class ErrorModel {
    public Dictionary<string/*!*/, int>/*!*/ identifierToPartition;
    public List<List<string/*!>>!*/>> partitionToIdentifiers;
    public List<Object>/*!*/ partitionToValue;
    public Dictionary<object, int>/*!*/ valueToPartition;
    public Dictionary<string/*!*/, List<List<int>>/*!*/>/*!*/ definedFunctions;
    public Model comesFrom;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(identifierToPartition != null);
      Contract.Invariant(partitionToIdentifiers != null);
      Contract.Invariant(Contract.ForAll(partitionToIdentifiers, i => cce.NonNullElements(i)));
      Contract.Invariant(partitionToValue != null);
      Contract.Invariant(valueToPartition != null);
      Contract.Invariant(cce.NonNullDictionaryAndValues(definedFunctions));
    }


    public ErrorModel(Dictionary<string, int> identifierToPartition, List<List<string>> partitionToIdentifiers, List<Object> partitionToValue, Dictionary<object, int> valueToPartition, Dictionary<string, List<List<int>>> definedFunctions) {
      Contract.Requires(identifierToPartition != null);
      Contract.Requires(partitionToIdentifiers != null);
      Contract.Requires(Contract.ForAll(partitionToIdentifiers, i => cce.NonNullElements(i)));
      Contract.Requires(partitionToValue != null);
      Contract.Requires(valueToPartition != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(definedFunctions));
      this.identifierToPartition = identifierToPartition;
      this.partitionToIdentifiers = partitionToIdentifiers;
      this.partitionToValue = partitionToValue;
      this.valueToPartition = valueToPartition;
      this.definedFunctions = definedFunctions;
    }

    public ErrorModel(Model m)
    {      
      // this.comesFrom = m;

      this.identifierToPartition = new Dictionary<string, int>();
      this.partitionToValue = new List<object>();
      this.partitionToIdentifiers = new List<List<string>>();
      this.valueToPartition = new Dictionary<object, int>();
      this.definedFunctions = new Dictionary<string, List<List<int>>>();

      var elseElt = m.MkElement("*#unspecified");

      foreach (var e in m.Elements) {
        Contract.Assert(e.Id == this.partitionToValue.Count);
        object val;
        switch (e.Kind) {
          case Model.ElementKind.Uninterpreted:
            val = null;            
            break;
          case Model.ElementKind.Integer:
            val = BigNum.FromString(((Model.Integer)e).Numeral);            
            break;
          case Model.ElementKind.BitVector:
            val = new BvConst(BigNum.FromString(((Model.BitVector)e).Numeral), ((Model.BitVector)e).Size);
            break;
          case Model.ElementKind.Boolean:
            val = ((Model.Boolean)e).Value;
            break;     
          case Model.ElementKind.Array:
            val = null;
            break;
          case Model.ElementKind.DataValue:
            val = null;
            break;
          default:
            Contract.Assert(false);
            val = null;
            break;
        }
        this.partitionToValue.Add(val);
        if (val != null)
          this.valueToPartition[val] = e.Id;

        var names = new List<string>();
        this.partitionToIdentifiers.Add(names);
        foreach (var app in e.Names) {
          if (app.Func.Arity == 0) {
            names.Add(app.Func.Name);
            this.identifierToPartition[app.Func.Name] = e.Id;
          }
        }
      }

      foreach (var f in m.Functions) {
        if (f.Arity > 0) {
          var tuples = new List<List<int>>();
          this.definedFunctions[f.Name] = tuples;
          foreach (var app in f.Apps) {
            var tpl = new List<int>(f.Arity + 1);
            foreach (var a in app.Args) tpl.Add(a.Id);
            tpl.Add(app.Result.Id);
            tuples.Add(tpl);
          }
          var elseTpl = new List<int>();
          if (f.Else != null)
            elseTpl.Add(f.Else.Id);
          else
            elseTpl.Add(elseElt.Id);
          tuples.Add(elseTpl);
        }
      }

      foreach (var e in m.Elements) {
        var arr = e as Model.Array;
        if (arr != null) {
          var tuples = this.definedFunctions[arr.Value.Name];
          this.partitionToValue[arr.Id] = tuples;
          this.valueToPartition[tuples] = arr.Id;
        }
      }
    }

    public Model ToModel()
    {
      if (comesFrom != null)
        return comesFrom;

      Model m = new Model();
      // create an Element for every partition
      Model.Element[] elts = new Model.Element[partitionToValue.Count];
      var asArrayIdx = 0;
      for (int i = 0; i < partitionToValue.Count; ++i) {
        var v = partitionToValue[i];
        if (v == null)
          elts[i] = m.MkElement(string.Format("*{0}", i));
        else {
          var ll = v as List<List<int>>;
          if (ll != null) {
            var arrName = "boogie-array#" + asArrayIdx++;
            this.definedFunctions[arrName] = ll;
            elts[i] = m.MkElement("as-array[" + arrName + "]");
          }
          else
            elts[i] = m.MkElement(v.ToString());
        }

        foreach (var id in partitionToIdentifiers[i]) {
          var f = m.MkFunc(id, 0);
          f.SetConstant(elts[i]);
        }
      }
      // compute and apply redirections
      foreach (var pr in Redirections(definedFunctions)) {
        elts[pr.Key] = elts[pr.Value];
      }

      // create functions
      var selectFunctions = new Dictionary<int, Model.Func>();
      var storeFunctions = new Dictionary<int, Model.Func>();
      foreach (var t in definedFunctions) {
        var tuples = t.Value;
        if (tuples.Count == 0) continue;

        // get the Func ("it doesn't matter if you get the funk, just as long as the funk gets you", from Ulco Bed's "Get The Funk" on Candy Dulfer's 1990 album Saxuality)
        var name = t.Key;
        var arity = tuples[0].Count - 1;

        // this may happen if the function only has the else clause; the 1 is just the best guess in such case
        if (arity == 0)
          arity = 1; 

        Model.Func f;
        if (Regex.IsMatch(name, "^MapType[0-9]*Select$")) {
          name = string.Format("[{0}]", arity);
          if (!selectFunctions.TryGetValue(arity, out f)) {
            f = m.MkFunc(name, arity);
            selectFunctions.Add(arity, f);
          }
        } else if (Regex.IsMatch(name, "^MapType[0-9]*Store$")) {
          name = string.Format("[{0}:=]", arity);
          if (!storeFunctions.TryGetValue(arity, out f)) {
            f = m.MkFunc(name, arity);
            storeFunctions.Add(arity, f);
          }
        } else {
          f = m.MkFunc(name, arity);
        }

        var args = new Model.Element[arity];
        foreach (var l in tuples) {
          if (l.Count == 1) {
            if (f.Else == null)
              f.Else = elts[l[0]];
          } else {
            for (int i = 0; i < f.Arity; ++i)
              args[i] = elts[l[i]];
            f.AddApp(elts[l[f.Arity]], args);
          }
        }
      }

      return m;
    }

    IEnumerable<KeyValuePair<int,int>> Redirections(Dictionary<string, List<List<int>>> functions) {
      List<List<int>> fn;
      if (functions.TryGetValue("U_2_bool", out fn)) {
        foreach (var tpl in fn) {
          if (tpl.Count == 2)  // the last tuple (the default value) has length 1
            yield return new KeyValuePair<int,int>(tpl[0], tpl[1]);
        }
      }
      if (functions.TryGetValue("U_2_int", out fn)) {
        foreach (var tpl in fn) {
          if (tpl.Count == 2)  // the last tuple (the default value) has length 1
            yield return new KeyValuePair<int,int>(tpl[0], tpl[1]);
        }
      }
    }

    public virtual void Print(TextWriter writer)
    {
      Contract.Requires(writer != null);

      writer.WriteLine("Z3 error model: ");

      writer.WriteLine("partitions:");
      Contract.Assert(partitionToIdentifiers.Count == partitionToValue.Count);
      for (int i = 0; i < partitionToIdentifiers.Count; i++) {
        writer.Write("*" + i);
        List<string> pti = partitionToIdentifiers[i];
        if (pti != null && pti.Count != 0) {
          writer.Write(" {");
          for (int k = 0; k < pti.Count - 1; k++) {
            writer.Write(pti[k] + " ");
          }
          //extra work to make sure no " " is at the end of the list of identifiers
          if (pti.Count != 0) {
            writer.Write(pti[pti.Count - 1]);
          }
          writer.Write("}");
        }
        // temp object needed for non-null checking
        object tempPTVI = partitionToValue[i];
        if (tempPTVI != null) {
          if (tempPTVI.ToString() == "True") {
            writer.Write(" -> " + "true" + "");
          } else if (tempPTVI.ToString() == "False") {
            writer.Write(" -> " + "false" + "");
          } else if (tempPTVI is BigNum) {
            writer.Write(" -> " + tempPTVI + ":int");
          } else if (tempPTVI is List<List<int>>) {
            List<List<int>> array = tempPTVI as List<List<int>>;
            Contract.Assume(array != null);
            writer.Write(" -> {");
            foreach (List<int> l in array) {
              if (l.Count == 2) {
                writer.Write("*" + l[0] + " -> " + "*" + l[1] + "; ");
              } else {
                Contract.Assert((l.Count == 1));
                writer.Write("else -> *" + l[0] + "}");
              }
            }
          } else {
            writer.Write(" -> " + tempPTVI + "");
          }
        } else {
          writer.Write(" ");
        }
        writer.WriteLine();
      }

      writer.WriteLine("function interpretations:");
      foreach (KeyValuePair<string, List<List<int>>> kvp in definedFunctions) {
        Contract.Assert(kvp.Key != null);
        writer.WriteLine(kvp.Key + " -> {");
        List<List<int>> kvpValue = kvp.Value;
        if (kvpValue != null) {
          foreach (List<int> l in kvpValue) {
            writer.Write("  ");
            if (l != null) {
              for (int i = 0; i < l.Count - 1; i++) {
                writer.Write("*" + l[i] + " ");
              }
              if (l.Count == 1) {
                writer.WriteLine("else -> #unspecified");
              } else {
                writer.WriteLine("-> " + "*" + l[l.Count - 1]);
              }
            }
          }
        }
        writer.WriteLine("}");
      }
      writer.WriteLine("END_OF_MODEL");
      writer.WriteLine(".");

      if (CommandLineOptions.Clo.PrintErrorModel >= 2) {
        writer.WriteLine("identifierToPartition:");
        foreach (KeyValuePair<string, int> kvp in identifierToPartition) {
          Contract.Assert(kvp.Key != null);
          writer.WriteLine(kvp.Key + " : " + "*" + kvp.Value);
        }

        writer.WriteLine("valueToPartition:");
        foreach (KeyValuePair<object, int> kvp in valueToPartition) {
          writer.WriteLine(kvp.Key + " : " + "*" + kvp.Value);
        }
        writer.WriteLine("End of model.");
      }
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
        object o = partitionToValue[i];
        if (o == null) {
          // uninterpreted value
          vals.Add(string.Format("UI({0})", i.ToString()));
        } else if (o is bool) {
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
              tupleVal.Add(cce.NonNull(partitionToValue[j]));
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

  // Exposes an api in line with z3's api
  public abstract class ApiProverInterface : ProverInterface
  {
      public abstract void Assert(VCExpr vc, bool polarity);
      public abstract void AssertAxioms();
      public abstract void Check();
      public abstract void CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore);
      public abstract void Push();
      public virtual void SetTimeOut(int ms) { }
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
