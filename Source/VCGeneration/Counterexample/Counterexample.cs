using System;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;
using VC;
using VCGeneration;

namespace Microsoft.Boogie
{
  public abstract class Counterexample
  {

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Trace != null);
      Contract.Invariant(Context != null);
      Contract.Invariant(cce.NonNullDictionaryAndValues(CalleeCounterexamples));
    }

    public ProofRun ProofRun { get; }
    protected readonly VCGenOptions Options;
    [Peer] public List<Block> Trace;
    public readonly List<object> AugmentedTrace;
    public AssertCmd FailingAssert { get; }
    public Model Model { get; }
    public readonly ModelViewInfo MvInfo;
    public readonly ProverContext Context;
    public abstract byte[] Checksum { get; }
    public byte[] SugaredCmdChecksum;
    public bool IsAuxiliaryCexForDiagnosingTimeouts;

    public Dictionary<TraceLocation, CalleeCounterexampleInfo> CalleeCounterexamples;

    internal Counterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, Model model,
      VC.ModelViewInfo mvInfo, ProverContext context, ProofRun proofRun, AssertCmd failingAssert)
    {
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      this.Options = options;
      this.Trace = trace;
      this.Model = model;
      this.MvInfo = mvInfo;
      this.Context = context;
      this.ProofRun = proofRun;
      this.FailingAssert = failingAssert;
      this.CalleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();
      // the call to instance method GetModelValue in the following code requires the fields Model and Context to be initialized
      if (augmentedTrace != null)
      {
        this.AugmentedTrace = augmentedTrace
          .Select(elem => elem is IdentifierExpr identifierExpr ? GetModelValue(identifierExpr.Decl) : elem).ToList();
      }
    }

    // Create a shallow copy of the counterexample
    public abstract Counterexample Clone();

    public void AddCalleeCounterexample(TraceLocation loc, CalleeCounterexampleInfo cex)
    {
      Contract.Requires(cex != null);
      CalleeCounterexamples[loc] = cex;
    }

    public void AddCalleeCounterexample(int numBlock, int numInstr, CalleeCounterexampleInfo cex)
    {
      Contract.Requires(cex != null);
      CalleeCounterexamples[new TraceLocation(numBlock, numInstr)] = cex;
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
    public Cmd GetTraceCmd(TraceLocation loc)
    {
      Debug.Assert(loc.numBlock < Trace.Count);
      Block b = Trace[loc.numBlock];
      Debug.Assert(loc.numInstr < b.Cmds.Count);
      return b.Cmds[loc.numInstr];
    }

    // Looks up the name of the called procedure.
    // Asserts that the name exists
    public string GetCalledProcName(Cmd cmd)
    {
      // There are two options:
      // 1. cmd is a CallCmd
      // 2. cmd is an AssumeCmd (passified version of a CallCmd)
      if (cmd is CallCmd)
      {
        return (cmd as CallCmd).Proc.Name;
      }

      AssumeCmd assumeCmd = cmd as AssumeCmd;
      Debug.Assert(assumeCmd != null);

      NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
      Debug.Assert(naryExpr != null);

      return naryExpr.Fun.FunctionName;
    }

    public void Print(int indent, TextWriter tw, Action<Block> blockAction = null)
    {
      int numBlock = -1;
      string ind = new string(' ', indent);
      foreach (Block block in Trace)
      {
        Contract.Assert(block != null);
        numBlock++;
        if (block.tok == null)
        {
          tw.WriteLine("{0}<intermediate block>", ind);
        }
        else {
          // for ErrorTrace == 1 restrict the output;
          // do not print tokens with -17:-4 as their location because they have been
          // introduced in the translation and do not give any useful feedback to the user
          if (Options.ErrorTrace == 1 && block.tok == Token.NoToken) {
            continue;
          }

          blockAction?.Invoke(block);

          tw.WriteLine("{4}{0}({1},{2}): {3}", block.tok.filename, block.tok.line, block.tok.col, block.Label, ind);

          for (int numInstr = 0; numInstr < block.Cmds.Count; numInstr++)
          {
            var loc = new TraceLocation(numBlock, numInstr);
            if (!CalleeCounterexamples.ContainsKey(loc)) {
              continue;
            }

            var cmd = GetTraceCmd(loc);
            var calleeName = GetCalledProcName(cmd);
            if (calleeName.StartsWith(VC.StratifiedVerificationConditionGeneratorBase.recordProcName) &&
                Options.StratifiedInlining > 0)
            {
              Contract.Assert(CalleeCounterexamples[loc].Args.Count == 1);
              var arg = CalleeCounterexamples[loc].Args[0];
              tw.WriteLine("{0}value = {1}", ind, arg.ToString());
            }
            else
            {
              tw.WriteLine("{1}Inlined call to procedure {0} begins", calleeName, ind);
              CalleeCounterexamples[loc].Counterexample.Print(indent + 4, tw);
              tw.WriteLine("{1}Inlined call to procedure {0} ends", calleeName, ind);
            }
          }
        }
      }
    }

    public void PrintModel(TextWriter tw, Counterexample counterexample)
    {
      Contract.Requires(counterexample != null);

      var filenameTemplate = Options.ModelViewFile;
      if (Model == null || filenameTemplate == null || Options.StratifiedInlining > 0)
      {
        return;
      }
      
      if (!Model.ModelHasStatesAlready) {
        throw new InvalidOperationException("Model should have states before being printed");
      }

      if (filenameTemplate == "-")
      {
        Model.Write(tw);
        tw.Flush();
      }
      else {
        var (filename, reused) = Helpers.GetLogFilename(ProofRun.Description, filenameTemplate, true);
        using var wr = new StreamWriter(filename, reused);
        Model.Write(wr);
      }
    }

    public void InitializeModelStates()
    {
      if (Model is { ModelHasStatesAlready: false }) {
        PopulateModelWithStates(Trace, ModelFailingCommand);
        Model.ModelHasStatesAlready = true;
      }
    }

    void ApplyRedirections()
    {
      var mapping = new Dictionary<Model.Element, Model.Element>();
      foreach (var name in new string[] {"U_2_bool", "U_2_int"})
      {
        Model.Func f = Model.TryGetFunc(name);
        if (f != null && f.Arity == 1)
        {
          foreach (var ft in f.Apps)
          {
            mapping[ft.Args[0]] = ft.Result;
          }
        }
      }

      Model.Substitute(mapping);
    }

    protected abstract Cmd ModelFailingCommand { get; }

    public void PopulateModelWithStates(List<Block> trace, Cmd/*?*/ failingCmd)
    {
      Contract.Requires(Model != null);
      Contract.Requires(trace != null);

      Model m = Model;
      ApplyRedirections();

      if (MvInfo == null) {
        return;
      }

      foreach (Variable v in MvInfo.AllVariables)
      {
        m.InitialState.AddBinding(v.Name, GetModelValue(v));
      }

      var prevInc = new Dictionary<Variable, Expr>();
      for (int i = 0; i < trace.Count; ++i)
      {
        if (!MvInfo.BlockToCapturePointIndex.TryGetValue(trace[i], out var points)) {
          continue;
        }
        int cmdIndexlimit;
        if (i < trace.Count - 1 || failingCmd == null) {
          cmdIndexlimit = trace[i].Cmds.Count;
        } else {
          // this is the last block, so we only want to consider :captureState markers before
          // the error
          for (cmdIndexlimit = 0; cmdIndexlimit < trace[i].Cmds.Count; cmdIndexlimit++) {
            var cmd = trace[i].Cmds[cmdIndexlimit];
            if (cmd is AssertRequiresCmd arc && arc.Call == failingCmd) {
              break;
            } else if (cmd == failingCmd) {
              break;
            }
          }
        }
        var index = 0;
        foreach (var (captureStateAssumeCmd, map) in points) {
          if (i == trace.Count - 1 && failingCmd != null) {
            // Don't go past the error in this block
            // Continue looking through the commands in block trace[i] to see which one we'll
            // find next, the capture-state command or the error command.
            for (; index < trace[i].Cmds.Count; index++) {
              var cmd = trace[i].Cmds[index];
              if (cmd == captureStateAssumeCmd) {
                // yes, include MvInfo.CapturePoints[capturePointIndex]
                break;
              } else if ((cmd is AssertRequiresCmd arc && arc.Call == failingCmd) || cmd == failingCmd) {
                // don't include any further captured points
                return;
              }
            }
          }
          
          var cs = m.MkState(map.Description);

          foreach (Variable v in MvInfo.AllVariables)
          {
            if (!map.IncarnationMap.TryGetValue(v, out var e)) {
              continue; // not in the current state
            }
            Contract.Assert(e != null);

            if (prevInc.TryGetValue(v, out var prevIncV) && e == prevIncV) {
              continue; // skip unchanged variables
            }

            Model.Element elt;
            if (e is IdentifierExpr ide)
            {
              elt = GetModelValue(ide.Decl);
            }
            else if (e is LiteralExpr lit)
            {
              elt = m.MkElement(lit.Val.ToString());
            }
            else
            {
              elt = m.MkFunc(e.ToString(), 0).GetConstant();
            }

            cs.AddBinding(v.Name, elt);
          }

          prevInc = map.IncarnationMap;
        }
      }
    }

    public Model.Element GetModelValue(Variable v)
    {
      Model.Element elt;
      // first, get the unique name
      string uniqueName;
      VCExprVar vvar = Context.BoogieExprTranslator.TryLookupVariable(v);
      if (vvar == null)
      {
        uniqueName = v.Name;
      }
      else
      {
        uniqueName = Context.Lookup(vvar);
      }

      var f = Model.TryGetFunc(uniqueName);
      if (f == null)
      {
        f = Model.MkFunc(uniqueName, 0);
      }

      elt = f.GetConstant();
      return elt;
    }

    public abstract int GetLocation();

    public ErrorInformation CreateErrorInformation(VcOutcome vcOutcome, bool forceBplErrors)
    {
      ErrorInformation errorInfo;
      var cause = vcOutcome switch {
        VcOutcome.TimedOut => "Timed out on",
        VcOutcome.OutOfMemory => "Out of memory on",
        VcOutcome.SolverException => "Solver exception on",
        VcOutcome.OutOfResource => "Out of resource on",
        _ => "Error"
      };

      if (this is CallCounterexample callError)
      {
        if (callError.FailingRequires.ErrorMessage == null || forceBplErrors)
        {
          string msg = callError.FailingCall.Description.FailureDescription;
          errorInfo = ErrorInformation.Create(callError.FailingCall.tok, msg, cause);
          errorInfo.Kind = ErrorKind.Precondition;
          errorInfo.AddAuxInfo(callError.FailingRequires.tok,
            callError.FailingRequires.Description.FailureDescription,
            "Related location");
        }
        else
        {
          errorInfo = ErrorInformation.Create(null, callError.FailingRequires.ErrorMessage, null);
        }
      }
      else if (this is ReturnCounterexample returnError)
      {
        if (returnError.FailingEnsures.ErrorMessage == null || forceBplErrors)
        {
          errorInfo = ErrorInformation.Create(returnError.FailingReturn.tok, returnError.FailingReturn.Description.FailureDescription, cause);
          errorInfo.Kind = ErrorKind.Postcondition;
          errorInfo.AddAuxInfo(returnError.FailingEnsures.tok,
            returnError.FailingEnsures.Description.FailureDescription,
            "Related location");
        }
        else
        {
          errorInfo = ErrorInformation.Create(null, returnError.FailingEnsures.ErrorMessage, null);
        }
      }
      else // error is AssertCounterexample
      {
        var assertError = (AssertCounterexample)this;
        var failingAssert = assertError.FailingAssert;
        if (failingAssert is LoopInitAssertCmd or LoopInvMaintainedAssertCmd)
        {
          errorInfo = ErrorInformation.Create(failingAssert.tok, failingAssert.Description.FailureDescription, cause);
          errorInfo.Kind = failingAssert is LoopInitAssertCmd ?
            ErrorKind.InvariantEntry : ErrorKind.InvariantMaintainance;
          string relatedMessage = null;
          if (failingAssert is LoopInitAssertCmd initCmd)
          {
            var desc = initCmd.originalAssert.Description;
            if (desc is not AssertionDescription)
            {
              relatedMessage = desc.FailureDescription;
            }
          }
          else if (failingAssert is LoopInvMaintainedAssertCmd maintCmd)
          {
            var desc = maintCmd.originalAssert.Description;
            if (desc is not AssertionDescription)
            {
              relatedMessage = desc.FailureDescription;
            }
          }

          if (relatedMessage != null) {
            errorInfo.AddAuxInfo(failingAssert.tok, relatedMessage, "Related message");
          }
        }
        else
        {
          if (failingAssert.ErrorMessage == null || forceBplErrors)
          {
            string msg = failingAssert.Description.FailureDescription;
            errorInfo = ErrorInformation.Create(failingAssert.tok, msg, cause);
            errorInfo.Kind = ErrorKind.Assertion;
          }
          else
          {
            errorInfo = ErrorInformation.Create(null, failingAssert.ErrorMessage, null);
          }
        }
      }

      return errorInfo;
    }
  }
}
