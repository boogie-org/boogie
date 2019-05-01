//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Linq;
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
using Set = Microsoft.Boogie.GSet<object>;

namespace Microsoft.Boogie {

  public class CalleeCounterexampleInfo {
    public Counterexample counterexample;
    public List<object>/*!>!*/ args;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(args));
    }

    public CalleeCounterexampleInfo(Counterexample cex, List<object/*!>!*/> x)
    {
      Contract.Requires(cce.NonNullElements(x));
      counterexample = cex;
      args = x;
    }
  }

  public class TraceLocation : IEquatable<TraceLocation>
  {
      public int numBlock;
      public int numInstr;

      public TraceLocation(int numBlock, int numInstr)
      {
          this.numBlock = numBlock;
          this.numInstr = numInstr;
      }

      public override bool Equals(object obj)
      {
          TraceLocation that = obj as TraceLocation;
          if (that == null) return false;
          return (numBlock == that.numBlock && numInstr == that.numInstr);
      }

      public bool Equals(TraceLocation that)
      {
          return (numBlock == that.numBlock && numInstr == that.numInstr);
      }

      public override int GetHashCode()
      {
          return numBlock.GetHashCode() ^ 131 * numInstr.GetHashCode();
      }
  }

  public abstract class Counterexample {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Trace != null);
      Contract.Invariant(Context != null);
      Contract.Invariant(cce.NonNullElements(relatedInformation));
      Contract.Invariant(cce.NonNullDictionaryAndValues(calleeCounterexamples));
    }

    [Peer]
    public List<Block> Trace;
    public Model Model;
    public VC.ModelViewInfo MvInfo;
    public ProverContext Context;
    [Peer]
    public List<string>/*!>!*/ relatedInformation;
    public string OriginalRequestId;
    public string RequestId;
    public abstract byte[] Checksum { get; }
    public byte[] SugaredCmdChecksum;
    public bool IsAuxiliaryCexForDiagnosingTimeouts;

    public Dictionary<TraceLocation, CalleeCounterexampleInfo> calleeCounterexamples;

    internal Counterexample(List<Block> trace, Model model, VC.ModelViewInfo mvInfo, ProverContext context) {
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      this.Trace = trace;
      this.Model = model;
      this.MvInfo = mvInfo;
      this.Context = context;
      this.relatedInformation = new List<string>();
      this.calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();
    }

    // Create a shallow copy of the counterexample
    public abstract Counterexample Clone();

    public void AddCalleeCounterexample(TraceLocation loc, CalleeCounterexampleInfo cex)
    {
      Contract.Requires(cex != null);
      calleeCounterexamples[loc] = cex;
    }

    public void AddCalleeCounterexample(int numBlock, int numInstr, CalleeCounterexampleInfo cex)
    {
        Contract.Requires(cex != null);
        calleeCounterexamples[new TraceLocation(numBlock, numInstr)] = cex;
    }

    public void AddCalleeCounterexample(Dictionary<TraceLocation, CalleeCounterexampleInfo> cs)
    {
      Contract.Requires(cce.NonNullDictionaryAndValues(cs));
      foreach (TraceLocation loc in cs.Keys)
      {
          AddCalleeCounterexample(loc, cs[loc]);
      }
    }

    // Looks up the Cmd at a given index into the trace
    public Cmd getTraceCmd(TraceLocation loc)
    {
        Debug.Assert(loc.numBlock < Trace.Count);
        Block b = Trace[loc.numBlock];
        Debug.Assert(loc.numInstr < b.Cmds.Count);
        return b.Cmds[loc.numInstr];
    }

    // Looks up the name of the called procedure.
    // Asserts that the name exists
    public string getCalledProcName(Cmd cmd)
    {
        // There are two options:
        // 1. cmd is a CallCmd
        // 2. cmd is an AssumeCmd (passified version of a CallCmd)
        if(cmd is CallCmd) {
            return (cmd as CallCmd).Proc.Name;
        }
        AssumeCmd assumeCmd = cmd as AssumeCmd;
        Debug.Assert(assumeCmd != null);

        NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
        Debug.Assert(naryExpr != null);

        return naryExpr.Fun.FunctionName;
    }

    public void Print(int indent, TextWriter tw, Action<Block> blockAction = null) {
      int numBlock = -1;
      string ind = new string(' ', indent);
      foreach (Block b in Trace) {
        Contract.Assert(b != null);
        numBlock++;
        if (b.tok == null) {
          tw.WriteLine("{0}<intermediate block>", ind);
        } else {
          // for ErrorTrace == 1 restrict the output;
          // do not print tokens with -17:-4 as their location because they have been
          // introduced in the translation and do not give any useful feedback to the user
          if (!(CommandLineOptions.Clo.ErrorTrace == 1 && b.tok.line == -17 && b.tok.col == -4)) {
            if (blockAction != null)
            {
                blockAction(b);
            }

            tw.WriteLine("{4}{0}({1},{2}): {3}", b.tok.filename, b.tok.line, b.tok.col, b.Label, ind);

            for (int numInstr = 0; numInstr < b.Cmds.Count; numInstr++)
            {
                var loc = new TraceLocation(numBlock, numInstr);
                if (calleeCounterexamples.ContainsKey(loc))
                {
                    var cmd = getTraceCmd(loc);
                    var calleeName = getCalledProcName(cmd);
                    if (calleeName.StartsWith(VC.StratifiedVCGen.recordProcName) && CommandLineOptions.Clo.StratifiedInlining > 0)
                    {
                        Contract.Assert(calleeCounterexamples[loc].args.Count == 1);
                        var arg = calleeCounterexamples[loc].args[0];
                        tw.WriteLine("{0}value = {1}", ind, arg.ToString());
                    }
                    else
                    {
                        tw.WriteLine("{1}Inlined call to procedure {0} begins", calleeName, ind);
                        calleeCounterexamples[loc].counterexample.Print(indent + 4, tw);
                        tw.WriteLine("{1}Inlined call to procedure {0} ends", calleeName, ind);
                    }
                }
            }
          }
        }
      }
    }

    public static bool firstModelFile = true;

    public void PrintModel(TextWriter tw)
    {
      var filename = CommandLineOptions.Clo.ModelViewFile;
      if (Model == null || filename == null || CommandLineOptions.Clo.StratifiedInlining > 0) return;

      if (!Model.ModelHasStatesAlready) {
        PopulateModelWithStates();
        Model.ModelHasStatesAlready = true;
      }

      if (filename == "-") {
        Model.Write(tw);
        tw.Flush();
      } else {
        using (var wr = new StreamWriter(filename, !firstModelFile)) {
          firstModelFile = false;
          Model.Write(wr);
        }
      }
    }

    void ApplyRedirections(Model m) {
      var mapping = new Dictionary<Model.Element, Model.Element>();
      foreach (var name in new string[] { "U_2_bool", "U_2_int" }) {
        Model.Func f = m.TryGetFunc(name);
        if (f != null && f.Arity == 1) {
          foreach (var ft in f.Apps) mapping[ft.Args[0]] = ft.Result;
        }
      }
      m.Substitute(mapping);
    }

    public void PopulateModelWithStates()
    {
      Contract.Requires(Model != null);

      Model m = Model;
      ApplyRedirections(m); 

      var mvstates = m.TryGetFunc("$mv_state");
      if (MvInfo == null || mvstates == null || (mvstates.Arity == 1 && mvstates.Apps.Count() == 0))
        return;

      Contract.Assert(mvstates.Arity == 2);

      foreach (Variable v in MvInfo.AllVariables) {
        m.InitialState.AddBinding(v.Name, GetModelValue(m, v));
      }

      var states = new List<int>();
      foreach (var t in mvstates.Apps)
        states.Add(t.Args[1].AsInt());

      states.Sort();

      for (int i = 0; i < states.Count; ++i) {
        var s = states[i];
        if (0 <= s && s < MvInfo.CapturePoints.Count) {
          VC.ModelViewInfo.Mapping map = MvInfo.CapturePoints[s];
          var prevInc = i > 0 ? MvInfo.CapturePoints[states[i - 1]].IncarnationMap : new Dictionary<Variable, Expr>();
          var cs = m.MkState(map.Description);

          foreach (Variable v in MvInfo.AllVariables) {
            Expr e = map.IncarnationMap.ContainsKey(v) ? map.IncarnationMap[v] : null;
            if (e == null) continue;

            Expr prevIncV = prevInc.ContainsKey(v) ? prevInc[v] : null;
            if (prevIncV == e) continue; // skip unchanged variables

            Model.Element elt;

            if (e is IdentifierExpr) {
              IdentifierExpr ide = (IdentifierExpr)e;
              elt = GetModelValue(m, ide.Decl);
            } else if (e is LiteralExpr) {
              LiteralExpr lit = (LiteralExpr)e;
              elt = m.MkElement(lit.Val.ToString());
            } else {
              elt = m.MkFunc(e.ToString(), 0).GetConstant();
            }

            cs.AddBinding(v.Name, elt);
          }

        } else {
          Contract.Assume(false);
        }
      }
    }

    private Model.Element GetModelValue(Model m, Variable v) {
      Model.Element elt;
      // first, get the unique name
      string uniqueName;
      VCExprVar vvar = Context.BoogieExprTranslator.TryLookupVariable(v);
      if (vvar == null) {
        uniqueName = v.Name;
      } else {
        uniqueName = Context.Lookup(vvar);
      }

      var f = m.TryGetFunc(uniqueName);
      if (f == null) {
        f = m.MkFunc(uniqueName, 0);
      }
      elt = f.GetConstant();
      return elt;
    }

    public abstract int GetLocation();
  }

  public class CounterexampleComparer : IComparer<Counterexample>, IEqualityComparer<Counterexample> {

    private int Compare(List<Block> bs1, List<Block> bs2)
    {
      if (bs1.Count < bs2.Count)
      {
        return -1;
      }
      else if (bs2.Count < bs1.Count)
      {
        return 1;
      }

      for (int i = 0; i < bs1.Count; i++)
      {
        var b1 = bs1[i];
        var b2 = bs2[i];
        if (b1.tok.pos < b2.tok.pos)
        {
          return -1;
        }
        else if (b2.tok.pos < b1.tok.pos)
        {
          return 1;
        }
      }

      return 0;
    }

    public int Compare(Counterexample c1, Counterexample c2)
    {
      //Contract.Requires(c1 != null);
      //Contract.Requires(c2 != null);
      if (c1.GetLocation() == c2.GetLocation())
      {
        var c = Compare(c1.Trace, c2.Trace);
        if (c != 0)
        {
          return c;
        }
        // TODO(wuestholz): Generalize this to compare all IPotentialErrorNodes of the counterexample.
        var a1 = c1 as AssertCounterexample;
        var a2 = c2 as AssertCounterexample;
        if (a1 != null && a2 != null)
        {
          var s1 = a1.FailingAssert.ErrorData as string;
          var s2 = a2.FailingAssert.ErrorData as string;
          if (s1 != null && s2 != null)
          {
            return s1.CompareTo(s2);
          }
        }

        return 0;
      }
      if (c1.GetLocation() > c2.GetLocation())
      {
        return 1;
      }
      return -1;
    }

    public bool Equals(Counterexample x, Counterexample y)
    {
      return Compare(x, y) == 0;
    }

    public int GetHashCode(Counterexample obj)
    {
      return 0;
    }
  }

  public class AssertCounterexample : Counterexample {
    [Peer]
    public AssertCmd FailingAssert;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FailingAssert != null);
    }


    public AssertCounterexample(List<Block> trace, AssertCmd failingAssert, Model model, VC.ModelViewInfo mvInfo, ProverContext context)
      : base(trace, model, mvInfo, context) {
      Contract.Requires(trace != null);
      Contract.Requires(failingAssert != null);
      Contract.Requires(context != null);
      this.FailingAssert = failingAssert;
    }

    public override int GetLocation() {
      return FailingAssert.tok.line * 1000 + FailingAssert.tok.col;
    }

    public override byte[] Checksum
    {
      get { return FailingAssert.Checksum; }
    }

    public override Counterexample Clone()
    {
        var ret = new AssertCounterexample(Trace, FailingAssert, Model, MvInfo, Context);
        ret.calleeCounterexamples = calleeCounterexamples;
        return ret;
    }
  }

  public class CallCounterexample : Counterexample {
    public CallCmd FailingCall;
    public Requires FailingRequires;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FailingCall != null);
      Contract.Invariant(FailingRequires != null);
    }


    public CallCounterexample(List<Block> trace, CallCmd failingCall, Requires failingRequires, Model model, VC.ModelViewInfo mvInfo, ProverContext context, byte[] checksum = null)
      : base(trace, model, mvInfo, context) {
      Contract.Requires(!failingRequires.Free);
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      Contract.Requires(failingCall != null);
      Contract.Requires(failingRequires != null);
      this.FailingCall = failingCall;
      this.FailingRequires = failingRequires;
      this.checksum = checksum;
      this.SugaredCmdChecksum = failingCall.Checksum;
    }

    public override int GetLocation() {
      return FailingCall.tok.line * 1000 + FailingCall.tok.col;
    }

    byte[] checksum;
    public override byte[] Checksum
    {
      get { return checksum; }
    }

    public override Counterexample Clone()
    {
        var ret = new CallCounterexample(Trace, FailingCall, FailingRequires, Model, MvInfo, Context, Checksum);
        ret.calleeCounterexamples = calleeCounterexamples;
        return ret;
    }
  }

  public class ReturnCounterexample : Counterexample {
    public TransferCmd FailingReturn;
    public Ensures FailingEnsures;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FailingEnsures != null);
      Contract.Invariant(FailingReturn != null);
    }


    public ReturnCounterexample(List<Block> trace, TransferCmd failingReturn, Ensures failingEnsures, Model model, VC.ModelViewInfo mvInfo, ProverContext context, byte[] checksum)
      : base(trace, model, mvInfo, context) {
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      Contract.Requires(failingReturn != null);
      Contract.Requires(failingEnsures != null);
      Contract.Requires(!failingEnsures.Free);
      this.FailingReturn = failingReturn;
      this.FailingEnsures = failingEnsures;
      this.checksum = checksum;
    }

    public override int GetLocation() {
      return FailingReturn.tok.line * 1000 + FailingReturn.tok.col;
    }

    byte[] checksum;

    /// <summary>
    /// Returns the checksum of the corresponding assertion.
    /// </summary>
    public override byte[] Checksum
    {
      get
      {
        return checksum;
      }
    }

    public override Counterexample Clone()
    {
        var ret = new ReturnCounterexample(Trace, FailingReturn, FailingEnsures, Model, MvInfo, Context, checksum);
        ret.calleeCounterexamples = calleeCounterexamples;
        return ret;
    }
  }

  public class VerifierCallback {
    // reason == null means this is genuine counterexample returned by the prover
    // other reason means it's time out/memory out/crash
    public virtual void OnCounterexample(Counterexample ce, string/*?*/ reason) {
      Contract.Requires(ce != null);
    }

    // called in case resource is exceeded and we don't have counterexample
    public virtual void OnTimeout(string reason) {
      Contract.Requires(reason != null);
    }

    public virtual void OnOutOfMemory(string reason) {
      Contract.Requires(reason != null);
    }

    public virtual void OnOutOfResource(string reason)
    {
      Contract.Requires(reason != null);
    }

    public virtual void OnProgress(string phase, int step, int totalSteps, double progressEstimate) {
    }

    public virtual void OnUnreachableCode(Implementation impl) {
      Contract.Requires(impl != null);
    }

    public virtual void OnWarning(string msg) {
      Contract.Requires(msg != null);
      switch (CommandLineOptions.Clo.PrintProverWarnings) {
        case CommandLineOptions.ProverWarnings.None:
          break;
        case CommandLineOptions.ProverWarnings.Stdout:
          Console.WriteLine("Prover warning: " + msg);
          break;
        case CommandLineOptions.ProverWarnings.Stderr:
          Console.Error.WriteLine("Prover warning: " + msg);
          break;
        default:
          Contract.Assume(false);
          throw new cce.UnreachableException();  // unexpected case
      }
    }
  }
}

////////////////////////////////////////////

namespace VC {
  using Bpl = Microsoft.Boogie;

  public class VCGenException : Exception {
    public VCGenException(string s)
      : base(s) {
    }
  }
  [ContractClassFor(typeof(ConditionGeneration))]
  public abstract class ConditionGenerationContracts : ConditionGeneration {
    public override Outcome VerifyImplementation(Implementation impl, VerifierCallback callback) {
      Contract.Requires(impl != null);
      Contract.Requires(callback != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      throw new NotImplementedException();
    }
    public ConditionGenerationContracts(Program p, List<Checker> checkers)
      : base(p, checkers) {
    }
  }

  [ContractClass(typeof(ConditionGenerationContracts))]
  public abstract class ConditionGeneration : IDisposable {
    protected internal object CheckerCommonState;

    public enum Outcome {
      Correct,
      Errors,
      TimedOut,
      OutOfResource,
      OutOfMemory,
      Inconclusive,
      ReachedBound
    }

    public static Outcome ProverInterfaceOutcomeToConditionGenerationOutcome(ProverInterface.Outcome outcome) {
      switch (outcome) {
        case ProverInterface.Outcome.Invalid:
          return Outcome.Errors;
        case ProverInterface.Outcome.OutOfMemory:
          return Outcome.OutOfMemory;
        case ProverInterface.Outcome.TimeOut:
          return Outcome.TimedOut;
        case ProverInterface.Outcome.OutOfResource:
          return Outcome.OutOfResource;
        case ProverInterface.Outcome.Undetermined:
          return Outcome.Inconclusive;
        case ProverInterface.Outcome.Valid:
          return Outcome.Correct;
      }
      return Outcome.Inconclusive;  // unreachable but the stupid compiler does not understand
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(checkers));
      Contract.Invariant(cce.NonNullDictionaryAndValues(incarnationOriginMap));
      Contract.Invariant(program != null);
    }

    public int CumulativeAssertionCount;  // for statistics

    protected readonly List<Checker>/*!>!*/ checkers;

    private bool _disposed;

    protected Implementation currentImplementation;

    protected List<Variable> CurrentLocalVariables = null;

    // shared across each implementation; created anew for each implementation
    protected Dictionary<Variable, int> variable2SequenceNumber;
    public Dictionary<Incarnation, Absy>/*!>!*/ incarnationOriginMap = new Dictionary<Incarnation, Absy>();

    public Program program;
    protected string/*?*/ logFilePath;
    protected bool appendLogFile;

    public static List<Model> errorModelList;

    public ConditionGeneration(Program p, List<Checker> checkers) {
      Contract.Requires(p != null && checkers != null && cce.NonNullElements(checkers));
      program = p;
      this.checkers = checkers;
      Cores = 1;
    }

    /// <summary>
    /// Takes an implementation and constructs a verification condition and sends
    /// it to the theorem prover.
    /// Returns null if "impl" is correct.  Otherwise, returns a list of counterexamples,
    /// each counterexample consisting of an array of labels.
    /// </summary>
    /// <param name="impl"></param>
    public Outcome VerifyImplementation(Implementation impl, out List<Counterexample>/*?*/ errors, string requestId = null) {
      Contract.Requires(impl != null);

      Contract.Ensures(Contract.ValueAtReturn(out errors) == null || Contract.ForAll(Contract.ValueAtReturn(out errors), i => i != null));
      Contract.Ensures(Contract.Result<Outcome>() != Outcome.Errors || errors != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      Helpers.ExtraTraceInformation("Starting implementation verification");

      CounterexampleCollector collector = new CounterexampleCollector();
      collector.RequestId = requestId;
      Outcome outcome = VerifyImplementation(impl, collector);
      if (outcome == Outcome.Errors || outcome == Outcome.TimedOut || outcome == Outcome.OutOfMemory || outcome == Outcome.OutOfResource) {
        errors = collector.examples;
      } else {
        errors = null;
      }

      Helpers.ExtraTraceInformation("Finished implementation verification");
      return outcome;
    }

    /// <summary>
    /// Takes an implementation and constructs a verification condition and sends
    /// it to the theorem prover.
    /// Returns null if "impl" is correct.  Otherwise, returns a list of counterexamples,
    /// each counterexample consisting of an array of labels.
    /// </summary>
    /// <param name="impl"></param>
    public Outcome VerifyImplementation(Implementation impl, out List<Counterexample> errors, out List<Model> errorsModel)
    {
        Contract.Ensures(Contract.Result<Outcome>() != Outcome.Errors || Contract.ValueAtReturn(out errors) != null);
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        List<Counterexample> errorsOut;

        Outcome outcome;
        errorModelList = new List<Model>();
        outcome = VerifyImplementation(impl, out errorsOut);
        errors = errorsOut;
        errorsModel = errorModelList;

        return outcome;
    }

    public abstract Outcome VerifyImplementation(Implementation impl, VerifierCallback callback);

    /////////////////////////////////// Common Methods and Classes //////////////////////////////////////////

    #region Methods for injecting pre- and postconditions
    private static void
      ThreadInCodeExpr(Implementation impl,
                       Block targetBlock,
                       CodeExpr codeExpr,
                       bool replaceWithAssert,
                       TokenTextWriter debugWriter) {
      Contract.Requires(impl != null);
      Contract.Requires(codeExpr != null);
      Contract.Requires(targetBlock != null);
      // Go through codeExpr and for all blocks that have a "return e"
      // as their transfer command:
      //   Replace all "return e" with "assert/assume e"
      //   Change the transfer command to "goto targetBlock"
      // Then add all of the blocks in codeExpr to the implementation (at the end)
      foreach (Block b in codeExpr.Blocks) {
        Contract.Assert(b != null);
        ReturnExprCmd rec = b.TransferCmd as ReturnExprCmd;
        if (rec != null) { // otherwise it is a goto command
          if (replaceWithAssert) {
            Ensures ens = new Ensures(rec.tok, false, rec.Expr, null);
            Contract.Assert(ens != null);
            Cmd c = new AssertEnsuresCmd(ens);
            Contract.Assert(c != null);
            b.Cmds.Add(c);
          } else {
            b.Cmds.Add(new AssumeCmd(rec.tok, rec.Expr));
          }
          b.TransferCmd = new GotoCmd(Token.NoToken,
            new List<String> { targetBlock.Label },
            new List<Block> { targetBlock });
          targetBlock.Predecessors.Add(b);
        }
        impl.Blocks.Add(b);
      }
      if (debugWriter != null) {
        codeExpr.Emit(debugWriter, 1, false);
      }
      return;
    }

    private static void AddAsPrefix(Block b, List<Cmd> cs) {
      Contract.Requires(b != null);
      Contract.Requires(cs != null);
      List<Cmd> newCommands = new List<Cmd>();
      newCommands.AddRange(cs);
      newCommands.AddRange(b.Cmds);
      b.Cmds = newCommands;
    }


    /// <summary>
    /// Modifies an implementation by prepending it with startCmds and then, as assume
    /// statements, all preconditions.  Insert new blocks as needed, and adjust impl.Blocks[0]
    /// accordingly to make it the new implementation entry block.
    /// </summary>
    /// <param name="impl"></param>
    /// <param name="startCmds"></param>
    protected static void InjectPreconditions(Implementation impl, [Captured] List<Cmd> startCmds) {
      Contract.Requires(impl != null);
      Contract.Requires(startCmds != null);
      Contract.Requires(impl.Proc != null);

      TokenTextWriter debugWriter = null;
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
        debugWriter = new TokenTextWriter("<console>", Console.Out, /*setTokens=*/ false, /*pretty=*/ false);
        debugWriter.WriteLine("Effective precondition:");
      }

      Substitution formalProcImplSubst = Substituter.SubstitutionFromHashtable(impl.GetImplFormalMap());
      string blockLabel = "PreconditionGeneratedEntry";

      Block origStartBlock = impl.Blocks[0];
      Block insertionPoint = new Block(
        new Token(-17, -4), blockLabel, startCmds,
        new GotoCmd(Token.NoToken, new List<String> { origStartBlock.Label }, new List<Block> { origStartBlock }));

      impl.Blocks[0] = insertionPoint;  // make insertionPoint the start block
      impl.Blocks.Add(origStartBlock);  // and put the previous start block at the end of the list

      // (free and checked) requires clauses
      foreach (Requires req in impl.Proc.Requires)
      // invariant:  insertionPoint.TransferCmd is "goto origStartBlock;", but origStartBlock.Predecessors has not yet been updated
      {
        Contract.Assert(req != null);
        Expr e = Substituter.Apply(formalProcImplSubst, req.Condition);
        Cmd c = new AssumeCmd(req.tok, e);
        c.IrrelevantForChecksumComputation = true;
        insertionPoint.Cmds.Add(c);
        if (debugWriter != null) {
          c.Emit(debugWriter, 1);
        }
      }
      origStartBlock.Predecessors.Add(insertionPoint);

      if (impl.ExplicitAssumptionAboutCachedPrecondition != null)
      {
        insertionPoint.Cmds.Add(impl.ExplicitAssumptionAboutCachedPrecondition);
      }

      if (debugWriter != null) {
        debugWriter.WriteLine();
      }
    }
    /// <summary>
    /// Modifies an implementation by inserting all postconditions
    /// as assert statements at the end of the implementation
    /// Returns the possibly-new unified exit block of the implementation
    /// </summary>
    /// <param name="impl"></param>
    /// <param name="unifiedExitblock">The unified exit block that has
    /// already been constructed for the implementation (and so
    /// is already an element of impl.Blocks)
    /// </param>
    protected static void InjectPostConditions(Implementation impl, Block unifiedExitBlock, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins) {
      Contract.Requires(impl != null);
      Contract.Requires(unifiedExitBlock != null);
      Contract.Requires(gotoCmdOrigins != null);
      Contract.Requires(impl.Proc != null);
      Contract.Requires(unifiedExitBlock.TransferCmd is ReturnCmd);

      TokenTextWriter debugWriter = null;
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
        debugWriter = new TokenTextWriter("<console>", Console.Out, /*setTokens=*/ false, /*pretty=*/ false);
        debugWriter.WriteLine("Effective postcondition:");
      }

      Substitution formalProcImplSubst = Substituter.SubstitutionFromHashtable(impl.GetImplFormalMap());

      // (free and checked) ensures clauses
      foreach (Ensures ens in impl.Proc.Ensures) {
        Contract.Assert(ens != null);
        if (!ens.Free) { // skip free ensures clauses
            Expr e = Substituter.Apply(formalProcImplSubst, ens.Condition);
            Ensures ensCopy = (Ensures)cce.NonNull(ens.Clone());
            ensCopy.Condition = e;
            AssertEnsuresCmd c = new AssertEnsuresCmd(ensCopy);
            c.ErrorDataEnhanced = ensCopy.ErrorDataEnhanced;
            unifiedExitBlock.Cmds.Add(c);
            if (debugWriter != null) {
              c.Emit(debugWriter, 1);
            }
        }
      }

      if (debugWriter != null) {
        debugWriter.WriteLine();
      }
    }


    /// <summary>
    /// Get the pre-condition of an implementation, including the where clauses from the in-parameters.
    /// </summary>
    /// <param name="impl"></param>
    protected static List<Cmd> GetPre(Implementation impl) {
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);


      TokenTextWriter debugWriter = null;
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
        debugWriter = new TokenTextWriter("<console>", Console.Out, /*setTokens=*/ false, /*pretty=*/ false);
        debugWriter.WriteLine("Effective precondition:");
      }

      Substitution formalProcImplSubst = Substituter.SubstitutionFromHashtable(impl.GetImplFormalMap());
      List<Cmd> pre = new List<Cmd>();

      // (free and checked) requires clauses
      foreach (Requires req in impl.Proc.Requires) {
        Contract.Assert(req != null);
        Expr e = Substituter.Apply(formalProcImplSubst, req.Condition);
        Contract.Assert(e != null);
        Cmd c = new AssumeCmd(req.tok, e);
        Contract.Assert(c != null);
        pre.Add(c);

        if (debugWriter != null) {
          c.Emit(debugWriter, 1);
        }
      }

      if (debugWriter != null) {
        debugWriter.WriteLine();
      }

      return pre;
    }

    /// <summary>
    /// Get the post-condition of an implementation.
    /// </summary>
    /// <param name="impl"></param>
    protected static List<Cmd> GetPost(Implementation impl) {


      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
        Console.WriteLine("Effective postcondition:");
      }

      // Construct an Expr for the post-condition
      Substitution formalProcImplSubst = Substituter.SubstitutionFromHashtable(impl.GetImplFormalMap());
      List<Cmd> post = new List<Cmd>();
      foreach (Ensures ens in impl.Proc.Ensures) {
        Contract.Assert(ens != null);
        if (!ens.Free) {
          Expr e = Substituter.Apply(formalProcImplSubst, ens.Condition);
          Contract.Assert(e != null);
          Ensures ensCopy = cce.NonNull((Ensures)ens.Clone());
          ensCopy.Condition = e;
          Cmd c = new AssertEnsuresCmd(ensCopy);
          ((AssertEnsuresCmd)c).ErrorDataEnhanced = ensCopy.ErrorDataEnhanced;
          post.Add(c);

          if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
            c.Emit(new TokenTextWriter("<console>", Console.Out, /*setTokens=*/ false, /*pretty=*/ false), 1);
          }
        }
      }

      if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
        Console.WriteLine();
      }

      return post;
    }

    /// <summary>
    /// Get the where clauses from the in- and out-parameters as
    /// a sequence of assume commands.
    /// As a side effect, this method adds these where clauses to the out parameters.
    /// </summary>
    /// <param name="impl"></param>
    protected static List<Cmd> GetParamWhereClauses(Implementation impl) {
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      TokenTextWriter debugWriter = null;
      if (CommandLineOptions.Clo.PrintWithUniqueASTIds) {
        debugWriter = new TokenTextWriter("<console>", Console.Out, /*setTokens=*/ false, /*pretty=*/ false);
        debugWriter.WriteLine("Effective precondition from where-clauses:");
      }

      Substitution formalProcImplSubst = Substituter.SubstitutionFromHashtable(impl.GetImplFormalMap());
      List<Cmd> whereClauses = new List<Cmd>();

      // where clauses of in-parameters
      foreach (Formal f in impl.Proc.InParams) {
        Contract.Assert(f != null);
        if (f.TypedIdent.WhereExpr != null) {
          Expr e = Substituter.Apply(formalProcImplSubst, f.TypedIdent.WhereExpr);
          Cmd c = new AssumeCmd(f.tok, e);
          whereClauses.Add(c);

          if (debugWriter != null) {
            c.Emit(debugWriter, 1);
          }
        }
      }

      // where clauses of out-parameters
      Contract.Assert(impl.OutParams.Count == impl.Proc.OutParams.Count);
      for (int i = 0; i < impl.OutParams.Count; i++) {
        Variable f = cce.NonNull(impl.Proc.OutParams[i]);
        if (f.TypedIdent.WhereExpr != null) {
          Expr e = Substituter.Apply(formalProcImplSubst, f.TypedIdent.WhereExpr);
          Cmd c = new AssumeCmd(f.tok, e);
          whereClauses.Add(c);

          Variable fi = cce.NonNull(impl.OutParams[i]);
          Contract.Assume(fi.TypedIdent.WhereExpr == null);
          fi.TypedIdent.WhereExpr = e;

          if (debugWriter != null) {
            c.Emit(debugWriter, 1);
          }
        }
      }

      if (debugWriter != null) {
        debugWriter.WriteLine();
      }

      return whereClauses;
    }

    protected static void RestoreParamWhereClauses(Implementation impl) {
      Contract.Requires(impl != null);
      // We no longer need the where clauses on the out parameters, so we remove them to restore the situation from before VC generation
      foreach (Formal f in impl.OutParams) {
        Contract.Assert(f != null);
        f.TypedIdent.WhereExpr = null;
      }
    }
    #endregion


    protected Checker FindCheckerFor(int timeout, int rlimit = 0, bool isBlocking = true, int waitTimeinMs = 50, int maxRetries = 3)
    {
      Contract.Requires(0 <= waitTimeinMs && 0 <= maxRetries);
      Contract.Ensures(!isBlocking || Contract.Result<Checker>() != null);

      lock (checkers)
      {
      retry:
        // Look for existing checker.
        for (int i = 0; i < checkers.Count; i++)
        {
          var c = checkers[i];
          if (Monitor.TryEnter(c))
          {
            try
            {
              if (c.WillingToHandle(timeout, rlimit, program))
              {
                c.GetReady();
                return c;
              }
              else if (c.IsIdle || c.IsClosed)
              {
                if (c.IsIdle)
                {
                  c.Retarget(program, c.TheoremProver.Context, timeout, rlimit);
                  c.GetReady();
                  return c;
                }
                else
                {
                  checkers.RemoveAt(i);
                  i--;
                  continue;
                }
              }
            }
            finally
            {
              Monitor.Exit(c);
            }
          }
        }

        if (Cores <= checkers.Count)
        {
          if (isBlocking || 0 < maxRetries)
          {
            if (0 < waitTimeinMs)
            {
              Monitor.Wait(checkers, waitTimeinMs);
            }
            maxRetries--;
            goto retry;
          }
          else
          {
            return null;
          }
        }

        // Create a new checker.
        string log = logFilePath;
        if (log != null && !log.Contains("@PROC@") && checkers.Count > 0)
        {
          log = log + "." + checkers.Count;
        }
        Checker ch = new Checker(this, program, log, appendLogFile, timeout, rlimit);
        ch.GetReady();
        checkers.Add(ch);
        return ch;
      }      
    }


    virtual public void Close() {
    }


    public class CounterexampleCollector : VerifierCallback {
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullElements(examples));
      }

      public string RequestId;

      public readonly List<Counterexample>/*!>!*/ examples = new List<Counterexample>();
      public override void OnCounterexample(Counterexample ce, string/*?*/ reason) {
        //Contract.Requires(ce != null);
        if (RequestId != null)
        {
          ce.RequestId = RequestId;
        }
        if (ce.OriginalRequestId == null && 1 < CommandLineOptions.Clo.VerifySnapshots)
        {
          ce.OriginalRequestId = RequestId;
        }
        examples.Add(ce);
      }

      public override void OnUnreachableCode(Implementation impl) {
        //Contract.Requires(impl != null);
        System.Console.WriteLine("found unreachable code:");
        EmitImpl(impl, false);
        // TODO report error about next to last in seq
      }
    }

    protected static void EmitImpl(Implementation impl, bool printDesugarings) {
      Contract.Requires(impl != null);
      int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
      CommandLineOptions.Clo.PrintUnstructured = 2;  // print only the unstructured program
      bool oldPrintDesugaringSetting = CommandLineOptions.Clo.PrintDesugarings;
      CommandLineOptions.Clo.PrintDesugarings = printDesugarings;
      impl.Emit(new TokenTextWriter("<console>", Console.Out, /*setTokens=*/ false, /*pretty=*/ false), 0);
      CommandLineOptions.Clo.PrintDesugarings = oldPrintDesugaringSetting;
      CommandLineOptions.Clo.PrintUnstructured = oldPrintUnstructured;
    }


    protected Block GenerateUnifiedExit(Implementation impl, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins) {
      Contract.Requires(impl != null);
      Contract.Requires(gotoCmdOrigins != null);
      Contract.Ensures(Contract.Result<Block>() != null);

      Contract.Ensures(Contract.Result<Block>().TransferCmd is ReturnCmd);
      Block/*?*/ exitBlock = null;
      #region Create a unified exit block, if there's more than one
      {
        int returnBlocks = 0;
        foreach (Block b in impl.Blocks) {
          if (b.TransferCmd is ReturnCmd) {
            exitBlock = b;
            returnBlocks++;
          }
        }
        if (returnBlocks > 1) {
          string unifiedExitLabel = "GeneratedUnifiedExit";
          Block unifiedExit;
          unifiedExit = new Block(new Token(-17, -4), unifiedExitLabel, new List<Cmd>(), new ReturnCmd(impl.StructuredStmts != null ? impl.StructuredStmts.EndCurly : Token.NoToken));         
          Contract.Assert(unifiedExit != null);
          foreach (Block b in impl.Blocks) {
            if (b.TransferCmd is ReturnCmd) {
              List<String> labels = new List<String>();
              labels.Add(unifiedExitLabel);
              List<Block> bs = new List<Block>();
              bs.Add(unifiedExit);
              GotoCmd go = new GotoCmd(Token.NoToken, labels, bs);
              gotoCmdOrigins[go] = (ReturnCmd)b.TransferCmd;
              b.TransferCmd = go;
              unifiedExit.Predecessors.Add(b);
            }
          }

          exitBlock = unifiedExit;
          impl.Blocks.Add(unifiedExit);
        }
        Contract.Assert(exitBlock != null);
      }
      return exitBlock;
      #endregion
    }

    protected static void ResetPredecessors(List<Block> blocks) {
      Contract.Requires(blocks != null);
      foreach (Block b in blocks) {
        Contract.Assert(b != null);
        b.Predecessors = new List<Block>();
      }
      foreach (Block b in blocks) {
        Contract.Assert(b != null);
        foreach (Block ch in Exits(b)) {
          Contract.Assert(ch != null);
          ch.Predecessors.Add(b);
        }
      }
    }

    protected static IEnumerable Exits(Block b) {
      Contract.Requires(b != null);
      GotoCmd g = b.TransferCmd as GotoCmd;
      if (g != null) {
        return cce.NonNull(g.labelTargets);
      }
      return new List<Block>();
    }

    protected Variable CreateIncarnation(Variable x, Absy a) {
      Contract.Requires(this.variable2SequenceNumber != null);
      Contract.Requires(this.CurrentLocalVariables != null);
      Contract.Requires(a is Block || a is AssignCmd || a is HavocCmd);

      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<Variable>() != null);

      int currentIncarnationNumber =
        variable2SequenceNumber.ContainsKey(x)
        ?
        variable2SequenceNumber[x]
        :
        -1;
      Variable v = new Incarnation(x, currentIncarnationNumber + 1);
      variable2SequenceNumber[x] = currentIncarnationNumber + 1;
      CurrentLocalVariables.Add(v);
      incarnationOriginMap.Add((Incarnation)v, a);
      return v;
    }

    /// <summary>
    /// Compute the incarnation map at the beginning of block "b" from the incarnation blocks of the
    /// predecessors of "b".
    ///
    /// The predecessor map b.map for block "b" is defined as follows:
    ///   b.map.Domain == Union{Block p in b.predecessors; p.map.Domain}
    ///   Forall{Variable v in b.map.Domain;
    ///              b.map[v] == (v in Intersection{Block p in b.predecessors; p.map}.Domain
    ///                           ?  b.predecessors[0].map[v]
    ///                           :  new Variable())}
    /// Every variable that b.map maps to a fresh variable requires a fixup in all predecessor blocks.
    /// </summary>
    /// <param name="b"></param>
    /// <param name="block2Incarnation">Gives incarnation maps for b's predecessors.</param>
    /// <returns></returns>
    protected Dictionary<Variable, Expr> ComputeIncarnationMap(Block b, Dictionary<Block, Dictionary<Variable, Expr>> block2Incarnation) {
      Contract.Requires(b != null);
      Contract.Requires(block2Incarnation != null);
      Contract.Ensures(Contract.Result<Dictionary<Variable, Expr>>() != null);

      if (b.Predecessors.Count == 0) {
        return new Dictionary<Variable, Expr>();
      }

      Dictionary<Variable, Expr> incarnationMap = null;
      Set /*Variable*/ fixUps = new Set /*Variable*/ ();
      foreach (Block pred in b.Predecessors) {
        Contract.Assert(pred != null);
        Contract.Assert(block2Incarnation.ContainsKey(pred));  // otherwise, Passive Transformation found a block whose predecessors have not been processed yet
        Dictionary<Variable, Expr> predMap = (Dictionary<Variable, Expr>)block2Incarnation[pred];
        Contract.Assert(predMap != null);
        if (incarnationMap == null) {
          incarnationMap = new Dictionary<Variable, Expr>(predMap);
          continue;
        }

        ArrayList /*Variable*/ conflicts = new ArrayList /*Variable*/ ();
        foreach (Variable v in incarnationMap.Keys) {
          Contract.Assert(v != null);
          if (!predMap.ContainsKey(v)) {
            // conflict!!
            conflicts.Add(v);
            fixUps.Add(v);
          }
        }
        // Now that we're done with enumeration, we'll do all the removes
        foreach (Variable v in conflicts) {
          Contract.Assert(v != null);
          incarnationMap.Remove(v);
        }
        foreach (Variable v in predMap.Keys) {
          Contract.Assert(v != null);
          if (!incarnationMap.ContainsKey(v)) {
            // v was not in the domain of the predecessors seen so far, so it needs to be fixed up
            fixUps.Add(v);
          } else {
            // v in incarnationMap ==> all pred blocks (up to now) all agree on its incarnation
            if (predMap[v] != incarnationMap[v]) {
              // conflict!!
              incarnationMap.Remove(v);
              fixUps.Add(v);
            }
          }
        }
      }

      #region Second, for all variables in the fixups list, introduce a new incarnation and push it back into the preds.
      foreach (Variable v in fixUps) {
        Contract.Assert(v != null);
        if (!b.IsLive(v))
          continue;
        Variable v_prime = CreateIncarnation(v, b);
        IdentifierExpr ie = new IdentifierExpr(v_prime.tok, v_prime);
        Contract.Assert(incarnationMap != null);
        incarnationMap[v] = ie;
        foreach (Block pred in b.Predecessors) {
          Contract.Assert(pred != null);
          #region Create an assume command equating v_prime with its last incarnation in pred
          #region Create an identifier expression for the last incarnation in pred
          Dictionary<Variable, Expr> predMap = (Dictionary<Variable, Expr>)cce.NonNull(block2Incarnation[pred]);

          Expr pred_incarnation_exp;
          Expr o = predMap.ContainsKey(v) ? predMap[v] : null;
          if (o == null) {
            Variable predIncarnation = v;
            IdentifierExpr ie2 = new IdentifierExpr(predIncarnation.tok, predIncarnation);
            pred_incarnation_exp = ie2;
          } else {
            pred_incarnation_exp = o;
          }
          #endregion
          #region Create an identifier expression for the new incarnation
          IdentifierExpr v_prime_exp = new IdentifierExpr(v_prime.tok, v_prime);
          #endregion
          #region Create the assume command itself
          AssumeCmd ac = new AssumeCmd(v.tok, TypedExprEq(v_prime_exp, pred_incarnation_exp, v_prime.Name.Contains("a##cached##")));
          pred.Cmds.Add(ac);
          #endregion
          #endregion
        }
      }
      #endregion

      Contract.Assert(incarnationMap != null);
      return incarnationMap;
    }

    Dictionary<Variable, Expr> preHavocIncarnationMap = null;     // null = the previous command was not an HashCmd. Otherwise, a *copy* of the map before the havoc statement

    protected void TurnIntoPassiveBlock(Block b, Dictionary<Variable, Expr> incarnationMap, ModelViewInfo mvInfo, Substitution oldFrameSubst, MutableVariableCollector variableCollector, byte[] currentChecksum = null) {
      Contract.Requires(b != null);
      Contract.Requires(incarnationMap != null);
      Contract.Requires(mvInfo != null);
      Contract.Requires(oldFrameSubst != null);
      #region Walk forward over the commands in this block and convert them to passive commands

      List<Cmd> passiveCmds = new List<Cmd>();
      foreach (Cmd c in b.Cmds) {
        Contract.Assert(c != null); // walk forward over the commands because the map gets modified in a forward direction
        ChecksumHelper.ComputeChecksums(c, currentImplementation, variableCollector.UsedVariables, currentChecksum);
        variableCollector.Visit(c);
        currentChecksum = c.Checksum;
        TurnIntoPassiveCmd(c, incarnationMap, oldFrameSubst, passiveCmds, mvInfo, b);
      }
      b.Checksum = currentChecksum;
      b.Cmds = passiveCmds;

      if (b.TransferCmd is ReturnExprCmd) {
        ReturnExprCmd rec = (ReturnExprCmd)b.TransferCmd.Clone();
        Substitution incarnationSubst = Substituter.SubstitutionFromHashtable(incarnationMap);
        rec.Expr = Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, rec.Expr);
        b.TransferCmd = rec;
      }
      #endregion
    }

    protected Dictionary<Variable, Expr> Convert2PassiveCmd(Implementation impl, ModelViewInfo mvInfo) {
      Contract.Requires(impl != null);
      Contract.Requires(mvInfo != null);

      currentImplementation = impl;

      var start = DateTime.UtcNow;

      Dictionary<Variable, Expr> r = ConvertBlocks2PassiveCmd(impl.Blocks, impl.Proc.Modifies, mvInfo);
      
      var end = DateTime.UtcNow;

      if (CommandLineOptions.Clo.TraceCachingForDebugging)
      {
        Console.Out.WriteLine("Turned implementation into passive commands within {0:F0} ms.\n", end.Subtract(start).TotalMilliseconds);
      }

      if (CommandLineOptions.Clo.TraceCachingForDebugging)
      {
        using (var tokTxtWr = new TokenTextWriter("<console>", Console.Out, false, false))
        {
          var pd = CommandLineOptions.Clo.PrintDesugarings;
          var pu = CommandLineOptions.Clo.PrintUnstructured;
          CommandLineOptions.Clo.PrintDesugarings = true;
          CommandLineOptions.Clo.PrintUnstructured = 1;
          impl.Emit(tokTxtWr, 0);
          CommandLineOptions.Clo.PrintDesugarings = pd;
          CommandLineOptions.Clo.PrintUnstructured = pu;
        }
      }

      currentImplementation = null;

      RestoreParamWhereClauses(impl);

      #region Debug Tracing
      if (CommandLineOptions.Clo.TraceVerify) {
        Console.WriteLine("after conversion to passive commands");
        EmitImpl(impl, true);
      }
      #endregion

      return r;
    }

    protected Dictionary<Variable, Expr> ConvertBlocks2PassiveCmd(List<Block> blocks, List<IdentifierExpr> modifies, ModelViewInfo mvInfo) {
      Contract.Requires(blocks != null);
      Contract.Requires(modifies != null);
      Contract.Requires(mvInfo != null);
      #region Convert to Passive Commands

      #region Topological sort -- need to process in a linearization of the partial order
      Graph<Block> dag = new Graph<Block>();
      dag.AddSource(cce.NonNull(blocks[0])); // there is always at least one node in the graph
      foreach (Block b in blocks) {
        GotoCmd gtc = b.TransferCmd as GotoCmd;
        if (gtc != null) {
          Contract.Assume(gtc.labelTargets != null);
          foreach (Block dest in gtc.labelTargets) {
            Contract.Assert(dest != null);
            dag.AddEdge(b, dest);
          }
        }
      }

      IEnumerable sortedNodes;
      if (CommandLineOptions.Clo.ModifyTopologicalSorting) {
        sortedNodes = dag.TopologicalSort(true);
      } else {
        sortedNodes = dag.TopologicalSort();
      }

      Contract.Assert(sortedNodes != null);
      #endregion

      Substitution oldFrameSubst = ComputeOldExpressionSubstitution(modifies);

      // Now we can process the nodes in an order so that we're guaranteed to have
      // processed all of a node's predecessors before we process the node.
      Dictionary<Block, Dictionary<Variable, Expr>> block2Incarnation = new Dictionary<Block, Dictionary<Variable, Expr>>();
      Block exitBlock = null;
      Dictionary<Variable, Expr> exitIncarnationMap = null;
      var variableCollectors = new Dictionary<Block, MutableVariableCollector>();
      foreach (Block b in sortedNodes) {
        Contract.Assert(b != null);
        Contract.Assert(!block2Incarnation.ContainsKey(b));
        Dictionary<Variable, Expr> incarnationMap = ComputeIncarnationMap(b, block2Incarnation);

        // b.liveVarsBefore has served its purpose in the just-finished call to ComputeIncarnationMap; null it out.
        b.liveVarsBefore = null;

        // Decrement the succCount field in each predecessor. Once the field reaches zero in any block, 
        // all its successors have been passified.  Consequently, its entry in block2Incarnation can be removed.
        byte[] currentChecksum = null;
        var mvc = new MutableVariableCollector();
        variableCollectors[b] = mvc;
        foreach (Block p in b.Predecessors) {
          p.succCount--;
          if (p.Checksum != null)
          {
            // Compute the checksum based on the checksums of the predecessor. The order should not matter.
            currentChecksum = ChecksumHelper.CombineChecksums(p.Checksum, currentChecksum, true);
          }
          mvc.AddUsedVariables(variableCollectors[p].UsedVariables);
          if (p.succCount == 0)
            block2Incarnation.Remove(p);
        }

        #region Each block's map needs to be available to successor blocks
        GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
        if (gotoCmd == null) {
          b.succCount = 0;
        }
        else {
          // incarnationMap needs to be added only if there is some successor of b
          b.succCount = gotoCmd.labelNames.Count;
          block2Incarnation.Add(b, incarnationMap);
        }
        #endregion Each block's map needs to be available to successor blocks

        TurnIntoPassiveBlock(b, incarnationMap, mvInfo, oldFrameSubst, mvc, currentChecksum);
        exitBlock = b;
        exitIncarnationMap = incarnationMap;
      }

      variableCollectors.Clear();

      // Verify that exitBlock is indeed the unique exit block
      Contract.Assert(exitBlock != null);
      Contract.Assert(exitBlock.TransferCmd is ReturnCmd);
      #endregion Convert to Passive Commands

      return exitIncarnationMap;
    }

    /// <summary>
    /// Compute the substitution for old expressions.
    /// </summary>
    protected static Substitution ComputeOldExpressionSubstitution(List<IdentifierExpr> modifies)
    {
      Dictionary<Variable, Expr> oldFrameMap = new Dictionary<Variable, Expr>();
      foreach (IdentifierExpr ie in modifies)
      {
        Contract.Assert(ie != null);
        if (!oldFrameMap.ContainsKey(cce.NonNull(ie.Decl)))
          oldFrameMap.Add(ie.Decl, ie);
      }
      return Substituter.SubstitutionFromHashtable(oldFrameMap);
    }

    public enum CachingAction : byte
    {
      DoNothingToAssert,
      MarkAsPartiallyVerified,
      MarkAsFullyVerified,
      RecycleError,
      AssumeNegationOfAssumptionVariable,
      DropAssume
    }

    public long[] CachingActionCounts;

    void TraceCachingAction(Cmd cmd, CachingAction action)
    {
      if (CommandLineOptions.Clo.TraceCachingForTesting)
      {
        using (var tokTxtWr = new TokenTextWriter("<console>", Console.Out, false, false))
        {
          var loc = cmd.tok != null && cmd.tok != Token.NoToken ? string.Format("{0}({1},{2})", cmd.tok.filename, cmd.tok.line, cmd.tok.col) : "<unknown location>";
          Console.Write("Processing command (at {0}) ", loc);
          cmd.Emit(tokTxtWr, 0);
          Console.Out.WriteLine("  >>> {0}", action);
        }
      }
      
      if (CommandLineOptions.Clo.TraceCachingForBenchmarking && CachingActionCounts != null)
      {
        Interlocked.Increment(ref CachingActionCounts[(int)action]);
      }
    }

    /// <summary>
    /// Turn a command into a passive command, and it remembers the previous step, to see if it is a havoc or not. In the case, it remembers the incarnation map BEFORE the havoc
    /// Meanwhile, record any information needed to later reconstruct a model view.
    /// </summary>
    protected void TurnIntoPassiveCmd(Cmd c, Dictionary<Variable, Expr> incarnationMap, Substitution oldFrameSubst, List<Cmd> passiveCmds, ModelViewInfo mvInfo, Block containingBlock) {
      Contract.Requires(c != null);
      Contract.Requires(incarnationMap != null);
      Contract.Requires(oldFrameSubst != null);
      Contract.Requires(passiveCmds != null);
      Contract.Requires(mvInfo != null);
      Contract.Requires(containingBlock != null);

      Substitution incarnationSubst = Substituter.SubstitutionFromHashtable(incarnationMap);
      #region assert/assume P |--> assert/assume P[x := in(x)], out := in
      if (c is PredicateCmd) {
        Contract.Assert(c is AssertCmd || c is AssumeCmd);  // otherwise, unexpected PredicateCmd type

        PredicateCmd pc = (PredicateCmd)c.Clone();
        Contract.Assert(pc != null);

        QKeyValue current = pc.Attributes;
        while (current != null)
        {
          if (current.Key == "minimize" || current.Key == "maximize") {
            Contract.Assume(current.Params.Count == 1);
            var param = current.Params[0] as Expr;
            Contract.Assume(param != null && (param.Type.IsInt || param.Type.IsReal || param.Type.IsBv));
            current.ClearParams();
            current.AddParam(Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, param));
          }
          if (current.Key == "verified_under") {
            Contract.Assume(current.Params.Count == 1);
            var param = current.Params[0] as Expr;
            Contract.Assume(param != null && param.Type.IsBool);
            current.ClearParams();
            current.AddParam(Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, param));
          }
          current = current.Next;
        }

        Expr copy = Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, pc.Expr);
        if (CommandLineOptions.Clo.ModelViewFile != null && pc is AssumeCmd) {
          string description = QKeyValue.FindStringAttribute(pc.Attributes, "captureState");
          if (description != null) {
            Expr mv = new NAryExpr(pc.tok, new FunctionCall(ModelViewInfo.MVState_FunctionDef), new List<Expr> { Bpl.Expr.Ident(ModelViewInfo.MVState_ConstantDef), Bpl.Expr.Literal(mvInfo.CapturePoints.Count) });
            copy = Bpl.Expr.And(mv, copy);
            mvInfo.CapturePoints.Add(new ModelViewInfo.Mapping(description, new Dictionary<Variable, Expr>(incarnationMap)));
          }
        }
        Contract.Assert(copy != null);
        var dropCmd = false;
        var relevantAssumpVars = currentImplementation != null ? currentImplementation.RelevantInjectedAssumptionVariables(incarnationMap) : new List<LocalVariable>();
        var relevantDoomedAssumpVars = currentImplementation != null ? currentImplementation.RelevantDoomedInjectedAssumptionVariables(incarnationMap) : new List<LocalVariable>();
        var checksum = pc.Checksum;
        if (pc is AssertCmd) {
          var ac = (AssertCmd)pc;
          ac.OrigExpr = ac.Expr;
          Contract.Assert(ac.IncarnationMap == null);
          ac.IncarnationMap = (Dictionary<Variable, Expr>)cce.NonNull(new Dictionary<Variable, Expr>(incarnationMap));

          var subsumption = Wlp.Subsumption(ac);
          if (relevantDoomedAssumpVars.Any())
          {
            TraceCachingAction(pc, CachingAction.DoNothingToAssert);
          }
          else if (currentImplementation != null
                   && currentImplementation.HasCachedSnapshot
                   && checksum != null
                   && currentImplementation.IsAssertionChecksumInCachedSnapshot(checksum)
                   && !currentImplementation.IsErrorChecksumInCachedSnapshot(checksum))
          {
            if (!currentImplementation.AnyErrorsInCachedSnapshot
                && currentImplementation.InjectedAssumptionVariables.Count == 1
                && relevantAssumpVars.Count == 1)
            {
              TraceCachingAction(pc, CachingAction.MarkAsPartiallyVerified);
            }
            else
            {
              bool isTrue;
              var assmVars = currentImplementation.ConjunctionOfInjectedAssumptionVariables(incarnationMap, out isTrue);
              TraceCachingAction(pc, !isTrue ? CachingAction.MarkAsPartiallyVerified : CachingAction.MarkAsFullyVerified);
              var litExpr = ac.Expr as LiteralExpr;
              if (litExpr == null || !litExpr.IsTrue)
              {
                ac.MarkAsVerifiedUnder(assmVars);
              }
              else
              {
                dropCmd = true;
              }
            }
          }
          else if (currentImplementation != null
                   && currentImplementation.HasCachedSnapshot
                   && relevantAssumpVars.Count == 0
                   && checksum != null
                   && currentImplementation.IsAssertionChecksumInCachedSnapshot(checksum)
                   && currentImplementation.IsErrorChecksumInCachedSnapshot(checksum))
          {
            TraceCachingAction(pc, CachingAction.RecycleError);
            ac.MarkAsVerifiedUnder(Expr.True);
            currentImplementation.AddRecycledFailingAssertion(ac);
            pc.Attributes = new QKeyValue(Token.NoToken, "recycled_failing_assertion", new List<object>(), pc.Attributes);
          }
          else
          {
            TraceCachingAction(pc, CachingAction.DoNothingToAssert);
          }
        }
        else if (pc is AssumeCmd
                 && QKeyValue.FindBoolAttribute(pc.Attributes, "precondition_previous_snapshot")
                 && pc.SugaredCmdChecksum != null)
        {
          if (!relevantDoomedAssumpVars.Any()
              && currentImplementation.HasCachedSnapshot
              && currentImplementation.IsAssertionChecksumInCachedSnapshot(pc.SugaredCmdChecksum)
              && !currentImplementation.IsErrorChecksumInCachedSnapshot(pc.SugaredCmdChecksum))
          {
            bool isTrue;
            var assmVars = currentImplementation.ConjunctionOfInjectedAssumptionVariables(incarnationMap, out isTrue);
            if (!isTrue)
            {
              copy = LiteralExpr.Imp(assmVars, copy);
              TraceCachingAction(pc, CachingAction.MarkAsPartiallyVerified);
            }
            else
            {
              TraceCachingAction(pc, CachingAction.MarkAsFullyVerified);
            }
          }
          else
          {
            TraceCachingAction(pc, CachingAction.DropAssume);
            dropCmd = true;
          }
        }
        else if (pc is AssumeCmd && QKeyValue.FindBoolAttribute(pc.Attributes, "assumption_variable_initialization"))
        {
          var identExpr = pc.Expr as IdentifierExpr;
          if (identExpr != null && identExpr.Decl != null && !incarnationMap.ContainsKey(identExpr.Decl))
          {
            incarnationMap[identExpr.Decl] = LiteralExpr.True;
            dropCmd = true;
          }
        }
        pc.Expr = copy;
        if (!dropCmd)
        {
          passiveCmds.Add(pc);
        }
      }
      #endregion
      #region x1 := E1, x2 := E2, ... |--> assume x1' = E1[in] & x2' = E2[in], out := in( x |-> x' ) [except as noted below]
 else if (c is AssignCmd) {
        AssignCmd assign = ((AssignCmd)c).AsSimpleAssignCmd; // first remove map assignments
        Contract.Assert(assign != null);
        #region Substitute all variables in E with the current map
        List<Expr> copies = new List<Expr>();
        foreach (Expr e in assign.Rhss) {
          Contract.Assert(e != null);
          copies.Add(Substituter.ApplyReplacingOldExprs(incarnationSubst,
                                                        oldFrameSubst,
                                                        e));
        }
        #endregion

        List<Expr/*!>!*/> assumptions = new List<Expr>();
        // it might be too slow to create a new dictionary each time ...
        IDictionary<Variable, Expr> newIncarnationMappings =
          new Dictionary<Variable, Expr>();

        for (int i = 0; i < assign.Lhss.Count; ++i) {
          IdentifierExpr lhsIdExpr =
            cce.NonNull((SimpleAssignLhs)assign.Lhss[i]).AssignedVariable;
          Variable lhs = cce.NonNull(lhsIdExpr.Decl);
          Contract.Assert(lhs != null);
          Expr rhs = assign.Rhss[i];
          Contract.Assert(rhs != null);

          // don't create incarnations for assignments of literals or single variables.
          if (rhs is LiteralExpr) {
            incarnationMap[lhs] = rhs;
          } else if (rhs is IdentifierExpr) {
            IdentifierExpr ie = (IdentifierExpr)rhs;
            if (incarnationMap.ContainsKey(cce.NonNull(ie.Decl)))
              newIncarnationMappings[lhs] = cce.NonNull((Expr)incarnationMap[ie.Decl]);
            else
              newIncarnationMappings[lhs] = ie;
          } else {
            IdentifierExpr x_prime_exp = null;
            #region Make a new incarnation, x', for variable x, but only if x is *not* already an incarnation
            if (lhs is Incarnation) {
              // incarnations are already written only once, no need to make an incarnation of an incarnation
              x_prime_exp = lhsIdExpr;
            } else {
              Variable v = CreateIncarnation(lhs, c);
              x_prime_exp = new IdentifierExpr(lhsIdExpr.tok, v);
              newIncarnationMappings[lhs] = x_prime_exp;
            }
            #endregion

            var nAryExpr = copies[i] as NAryExpr;
            if (nAryExpr != null)
            {
              var binOp = nAryExpr.Fun as BinaryOperator;
              if (binOp != null
                  && binOp.Op == BinaryOperator.Opcode.And)
              {
                var arg0 = nAryExpr.Args[0] as LiteralExpr;
                var arg1 = nAryExpr.Args[1] as LiteralExpr;
                if ((arg0 != null && arg0.IsTrue) || (arg1 != null && arg1.IsFalse))
                {
                  // Replace the expressions "true && arg1" or "arg0 && false" by "arg1".
                  copies[i] = nAryExpr.Args[1];
                }
              }
            }
          
            #region Create an assume command with the new variable
            assumptions.Add(TypedExprEq(x_prime_exp, copies[i], x_prime_exp.Decl != null && x_prime_exp.Decl.Name.Contains("a##cached##")));
            #endregion
          }
        }

        foreach (KeyValuePair<Variable, Expr> pair in newIncarnationMappings) {
          Contract.Assert(pair.Key != null && pair.Value != null);
          incarnationMap[pair.Key] = pair.Value;
        }

        if (assumptions.Count > 0) {
          Expr assumption = assumptions[0];

          for (int i = 1; i < assumptions.Count; ++i) {
            Contract.Assert(assumption != null);
            assumption = Expr.And(assumption, assumptions[i]);
          }
          passiveCmds.Add(new AssumeCmd(c.tok, assumption));
        }

        if (currentImplementation != null
            && currentImplementation.HasCachedSnapshot
            && !currentImplementation.AnyErrorsInCachedSnapshot
            && currentImplementation.DoomedInjectedAssumptionVariables.Count == 0
            && currentImplementation.InjectedAssumptionVariables.Count == 1
            && assign.Lhss.Count == 1)
        {
          var identExpr = assign.Lhss[0].AsExpr as IdentifierExpr;
          Expr incarnation;
          if (identExpr != null && identExpr.Decl != null && QKeyValue.FindBoolAttribute(identExpr.Decl.Attributes, "assumption") && incarnationMap.TryGetValue(identExpr.Decl, out incarnation))
          {
            TraceCachingAction(assign, CachingAction.AssumeNegationOfAssumptionVariable);
            passiveCmds.Add(new AssumeCmd(c.tok, Expr.Not(incarnation)));
          }
        }
      }
      #endregion
      #region havoc w |--> assume whereClauses, out := in( w |-> w' )
 else if (c is HavocCmd) {
        if (this.preHavocIncarnationMap == null)      // Save a copy of the incarnation map (at the top of a sequence of havoc statements)
          this.preHavocIncarnationMap = new Dictionary<Variable, Expr>(incarnationMap);

        HavocCmd hc = (HavocCmd)c;
        Contract.Assert(c != null);
        // If an assumption variable for postconditions is included here, it must have been assigned within a loop.
        // We do not need to havoc it if we have performed a modular proof of the loop (i.e., using only the loop
        // invariant) in the previous snapshot and, consequently, the corresponding assumption did not affect the
        // anything after the loop. We can achieve this by simply not updating/adding it in the incarnation map.
        List<IdentifierExpr> havocVars = hc.Vars.Where(v => !(QKeyValue.FindBoolAttribute(v.Decl.Attributes, "assumption") && v.Decl.Name.StartsWith("a##cached##"))).ToList();
        // First, compute the new incarnations
        foreach (IdentifierExpr ie in havocVars) {
          Contract.Assert(ie != null);
          if (!(ie.Decl is Incarnation)) {
            Variable x = cce.NonNull(ie.Decl);
            Variable x_prime = CreateIncarnation(x, c);
            incarnationMap[x] = new IdentifierExpr(x_prime.tok, x_prime);
          }
        }
        // Then, perform the assume of the where clauses, using the updated incarnations
        Substitution updatedIncarnationSubst = Substituter.SubstitutionFromHashtable(incarnationMap);
        foreach (IdentifierExpr ie in havocVars) {
          Contract.Assert(ie != null);
          if (!(ie.Decl is Incarnation)) {
            Variable x = cce.NonNull(ie.Decl);
            Bpl.Expr w = x.TypedIdent.WhereExpr;
            if (w != null) {
              Expr copy = Substituter.ApplyReplacingOldExprs(updatedIncarnationSubst, oldFrameSubst, w);
              passiveCmds.Add(new AssumeCmd(c.tok, copy));
            }
          }
        }

        // Add the following assume-statement for each assumption variable 'v', where 'v_post' is the new incarnation and 'v_pre' is the old one:
        // assume v_post ==> v_pre;
        foreach (IdentifierExpr ie in havocVars)
        {
          if (QKeyValue.FindBoolAttribute(ie.Decl.Attributes, "assumption"))
          {
            var preInc = (Expr)(preHavocIncarnationMap[ie.Decl].Clone());
            var postInc = (Expr)(incarnationMap[ie.Decl].Clone());
            passiveCmds.Add(new AssumeCmd(c.tok, Expr.Imp(postInc, preInc)));
          }
        }
      }
      #endregion
 else if (c is CommentCmd) {
        // comments are just for debugging and don't affect verification
      } else if (c is SugaredCmd) {
        SugaredCmd sug = (SugaredCmd)c;
        Contract.Assert(sug != null);
        Cmd cmd = sug.Desugaring;
        Contract.Assert(cmd != null);
        TurnIntoPassiveCmd(cmd, incarnationMap, oldFrameSubst, passiveCmds, mvInfo, containingBlock);
      } else if (c is StateCmd) {
        this.preHavocIncarnationMap = null;       // we do not need to remeber the previous incarnations
        StateCmd st = (StateCmd)c;
        Contract.Assert(st != null);
        // account for any where clauses among the local variables
        foreach (Variable v in st.Locals) {
          Contract.Assert(v != null);
          Expr w = v.TypedIdent.WhereExpr;
          if (w != null) {
            passiveCmds.Add(new AssumeCmd(v.tok, w));
          }
        }
        // do the sub-commands
        foreach (Cmd s in st.Cmds) {
          Contract.Assert(s != null);
          TurnIntoPassiveCmd(s, incarnationMap, oldFrameSubst, passiveCmds, mvInfo, containingBlock);
        }
        // remove the local variables from the incarnation map
        foreach (Variable v in st.Locals) {
          Contract.Assert(v != null);
          incarnationMap.Remove(v);
        }
      }
      #region There shouldn't be any other types of commands at this point
 else {
        Debug.Fail("Internal Error: Passive transformation handed a command that is not one of assert,assume,havoc,assign.");
      }
      #endregion


      #region We remember if we have put an havoc statement into a passive form

      if (!(c is HavocCmd))
        this.preHavocIncarnationMap = null;
      // else: it has already been set by the case for the HavocCmd
      #endregion
    }

    NAryExpr TypedExprEq(Expr e0, Expr e1, bool doNotResolveOverloading = false) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      NAryExpr e = Expr.Eq(e0, e1);
      var fun = e.Fun as IOverloadedAppliable;
      if (fun != null)
      {
        fun.DoNotResolveOverloading = doNotResolveOverloading;
      }
      e.Type = Bpl.Type.Bool;
      e.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      return e;
    }

    /// <summary>
    /// Creates a new block to add to impl.Blocks, where impl is the implementation that contains
    /// succ.  Caller must do the add to impl.Blocks.
    /// </summary>
    protected Block CreateBlockBetween(int predIndex, Block succ) {
      Contract.Requires(0 <= predIndex && predIndex < succ.Predecessors.Count);


      Contract.Requires(succ != null);
      Contract.Ensures(Contract.Result<Block>() != null);

      Block pred = cce.NonNull(succ.Predecessors[predIndex]);

      string newBlockLabel = pred.Label + "_@2_" + succ.Label;

      // successor of newBlock list
      List<String> ls = new List<String>();
      ls.Add(succ.Label);
      List<Block> bs = new List<Block>();
      bs.Add(succ);

      Block newBlock = new Block(
          new Token(-17, -4),
          newBlockLabel,
          new List<Cmd>(),
          new GotoCmd(Token.NoToken, ls, bs)
          );

      // predecessors of newBlock
      List<Block> ps = new List<Block>();
      ps.Add(pred);
      newBlock.Predecessors = ps;

      // fix successors of pred
      #region Change the edge "pred->succ" to "pred->newBlock"
      GotoCmd gtc = (GotoCmd)cce.NonNull(pred.TransferCmd);
      Contract.Assume(gtc.labelTargets != null);
      Contract.Assume(gtc.labelNames != null);
      for (int i = 0, n = gtc.labelTargets.Count; i < n; i++) {
        if (gtc.labelTargets[i] == succ) {
          gtc.labelTargets[i] = newBlock;
          gtc.labelNames[i] = newBlockLabel;
          break;
        }
      }
      #endregion Change the edge "pred->succ" to "pred->newBlock"

      // fix predecessors of succ
      succ.Predecessors[predIndex] = newBlock;

      return newBlock;
    }

    protected void AddBlocksBetween(List<Block> blocks) {
      Contract.Requires(blocks != null);
      #region Introduce empty blocks between join points and their multi-successor predecessors
      List<Block> tweens = new List<Block>();
      foreach (Block b in blocks) {
        int nPreds = b.Predecessors.Count;
        if (nPreds > 1) {
          // b is a join point (i.e., it has more than one predecessor)
          for (int i = 0; i < nPreds; i++) {
            GotoCmd gotocmd = (GotoCmd)(cce.NonNull(b.Predecessors[i]).TransferCmd);
            if (gotocmd.labelNames != null && gotocmd.labelNames.Count > 1) {
              tweens.Add(CreateBlockBetween(i, b));
            }
          }
        }
      }
      blocks.AddRange(tweens);  // must wait until iteration is done before changing the list
      #endregion
    }


    public void Dispose()
    {
      Dispose(true);
      GC.SuppressFinalize(this);
    }

    protected virtual void Dispose(bool disposing)
    {
      if (!_disposed)
      {
        if (disposing)
        {
          Close();
        }
        _disposed = true;
      }
    }

    public int Cores { get; set; }
  }

  public class ModelViewInfo
  {
    public readonly List<Variable> AllVariables = new List<Variable>();
    public readonly List<Mapping> CapturePoints = new List<Mapping>();
    public static readonly Function MVState_FunctionDef = new Function(Token.NoToken, "$mv_state",
      new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, TypedIdent.NoName, Bpl.Type.Int), true),
                           new Formal(Token.NoToken, new TypedIdent(Token.NoToken, TypedIdent.NoName, Bpl.Type.Int), true) },
      new Formal(Token.NoToken, new TypedIdent(Token.NoToken, TypedIdent.NoName, Bpl.Type.Bool), false));
    public static readonly Constant MVState_ConstantDef = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "$mv_state_const", Bpl.Type.Int));

    public ModelViewInfo(Program program, Implementation impl) {
      Contract.Requires(program != null);
      Contract.Requires(impl != null);

      // global variables
      lock (program.TopLevelDeclarations)
      {
        foreach (var v in program.Variables)
        {
          if (!(v is Constant))
          {
            AllVariables.Add(v);
          }
        }
      }
      // implementation parameters
      foreach (Variable p in impl.InParams) {
        AllVariables.Add(p);
      }
      foreach (Variable p in impl.OutParams) {
        AllVariables.Add(p);
      }
      // implementation locals
      foreach (Variable v in impl.LocVars) {
        AllVariables.Add(v);
      }
    }

    public ModelViewInfo(CodeExpr codeExpr) {
      Contract.Requires(codeExpr != null);
      // TODO: also need all variables of enclosing scopes (the global variables of the program, the parameters
      // and perhaps locals of the implementation (if any), any enclosing code expressions).

      foreach (Variable v in codeExpr.LocVars) {
        AllVariables.Add(v);
      }
    }

    public class Mapping
    {
      public readonly string Description;
      public readonly Dictionary<Variable, Expr> IncarnationMap;
      public Mapping(string description, Dictionary<Variable, Expr> incarnationMap) {
        Description = description;
        IncarnationMap = incarnationMap;
      }
    }
  }
}
