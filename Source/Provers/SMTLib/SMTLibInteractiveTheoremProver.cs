using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Numerics;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.TypeErasure;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibInteractiveTheoremProver : SMTLibProcessTheoremProver
  {
    private bool ProcessNeedsRestart;

    [NotDelayed]
    public SMTLibInteractiveTheoremProver(SMTLibOptions libOptions, ProverOptions options, VCExpressionGenerator gen,
      SMTLibProverContext ctx) : base(libOptions, options, gen, ctx)
    {
      SetupProcess();
      if (libOptions.ImmediatelyAcceptCommands) {
        PrepareCommon();
      }
    }

    public override Task GoBackToIdle()
    {
      return Process.PingPong();
    }

    private void PossiblyRestart()
    {
      if (Process != null && ProcessNeedsRestart) {
        ProcessNeedsRestart = false;
        SetupProcess();
        Process.Send(common.ToString());
      }
    }

    private void FlushAndCacheCommons()
    {
      FlushAxioms();
      CachedCommon ??= common.ToString();
    }

    public override int FlushAxiomsToTheoremProver()
    {
      // we feed the axioms when BeginCheck is called.
      return 0;
    }

    private bool hasReset;
    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
    {
      if (options.SeparateLogFiles)
      {
        CloseLogFile(); // shouldn't really happen
      }

      if (options.LogFilename != null && currentLogFile == null)
      {
        currentLogFile = OpenOutputFile(descriptiveName);
        currentLogFile.Write(common.ToString());
      }

      PrepareCommon();
      FlushAndCacheCommons();

      if (hasReset)
      {
        AxBuilder = (TypeAxiomBuilder) CachedAxBuilder?.Clone();
        Namer = ResetNamer(CachedNamer);
        DeclCollector.SetNamer(Namer);
        DeclCollector.Push();
      }

      OptimizationRequests.Clear();

      string vcString = "(assert (not\n" + VCExpr2String(vc, 1) + "\n))";

      FlushAxioms();

      PossiblyRestart();

      SendThisVC("(push 1)");
      SendVCAndOptions(descriptiveName, vcString);

      SendOptimizationRequests();

      FlushLogFile();

      if (Process != null)
      {
        Process.PingPong().Wait(); // flush any errors
        Process.NewProblem(descriptiveName);
      }

      if (hasReset)
      {
        DeclCollector.Pop();
        common = new StringBuilder(CachedCommon);
        hasReset = false;
      }

      SendCheckSat();
      FlushLogFile();
    }

    public override void Reset(VCExpressionGenerator generator)
    {
      if (options.Solver == SolverKind.Z3 || options.Solver == SolverKind.NoOpWithZ3Options)
      {
        this.gen = generator;
        SendThisVC("(reset)");
        RecoverIfProverCrashedAfterReset();

        if (0 < common.Length)
        {
          var c = common.ToString();
          Process.Send(c);
          if (currentLogFile != null)
          {
            currentLogFile.WriteLine(c);
          }
        }

        hasReset = true;
      }
    }

    private void RecoverIfProverCrashedAfterReset()
    {
      if (Process.GetExceptionIfProverDied().Result is not null)
      {
        // We recover the process but don't issue the `(reset)` command that fails.
        SetupProcess();
      }
    }

    public override void FullReset(VCExpressionGenerator generator)
    {
      if (options.Solver == SolverKind.Z3 || options.Solver == SolverKind.NoOpWithZ3Options)
      {
        this.gen = generator;
        SendThisVC("(reset)");
        SendThisVC("(set-option :" + Z3.RlimitOption + " 0)");
        hasReset = true;
        common.Clear();
        SetupAxiomBuilder(gen);
        Axioms.Clear();
        TypeDecls.Clear();
        AxiomsAreSetup = false;
        ctx.Reset();
        ctx.KnownDatatypes.Clear();
        ctx.parent = this;
        DeclCollector.Reset();
        NamedAssumes.Clear();
        UsedNamedAssumes = null;
        SendThisVC("; did a full reset");
      }
    }

    [NoDefaultContract]
    public override async Task<Outcome> CheckOutcome(ErrorHandler handler, int errorLimit, CancellationToken cancellationToken)
    {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var result = await CheckOutcomeCore(handler, cancellationToken, errorLimit);
      SendThisVC("(pop 1)");
      FlushLogFile();

      return result;
    }

    [NoDefaultContract]
    public override async Task<Outcome> CheckOutcomeCore(ErrorHandler handler, CancellationToken cancellationToken,
      int errorLimit)
    {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var result = Outcome.Undetermined;

      if (Process == null || proverErrors.Count > 0)
      {
        return result;
      }

      try
      {
        currentErrorHandler = handler;
        FlushProverWarnings();

        var errorsDiscovered = 0;

        var globalResult = Outcome.Undetermined;

        while (true)
        {
          string[] labels = null;
          var popLater = false;

          try
          {
            errorsDiscovered++;

            result = await GetResponse(cancellationToken);

            var reporter = handler;
            // TODO(wuestholz): Is the reporter ever null?
            if (usingUnsatCore && result == Outcome.Valid && reporter != null && 0 < NamedAssumes.Count)
            {
              if (usingUnsatCore)
              {
                UsedNamedAssumes = new HashSet<string>();
                SendThisVC("(get-unsat-core)");
                var resp = await Process.GetProverResponse().WaitAsync(cancellationToken);
                if (resp.Name != "")
                {
                  UsedNamedAssumes.Add(resp.Name);
                  if (libOptions.PrintNecessaryAssumes)
                  {
                    reporter.AddNecessaryAssume(resp.Name.Substring("aux$$assume$$".Length));
                  }
                }

                foreach (var arg in resp.Arguments)
                {
                  UsedNamedAssumes.Add(arg.Name);
                  if (libOptions.PrintNecessaryAssumes)
                  {
                    reporter.AddNecessaryAssume(arg.Name.Substring("aux$$assume$$".Length));
                  }
                }
              }
              else
              {
                UsedNamedAssumes = null;
              }
            }

            if (libOptions.RunDiagnosticsOnTimeout && result == Outcome.TimeOut) {
              (result, popLater) = await RunTimeoutDiagnostics(handler, result, cancellationToken);
            }

            if (globalResult == Outcome.Undetermined)
            {
              globalResult = result;
            }

            if (result == Outcome.Invalid)
            {
              Model model = await GetErrorModel(cancellationToken);
              if (libOptions.SIBoolControlVC)
              {
                labels = Array.Empty<string>();
              }
              else
              {
                labels = await CalculatePath(handler.StartingProcId(), cancellationToken);
                if (labels.Length == 0)
                {
                  // Without a path to an error, we don't know what to report
                  globalResult = Outcome.Undetermined;
                  break;
                }
              }

              handler.OnModel(labels, model, result);
            }

            Debug.Assert(errorsDiscovered > 0);
            // if errorLimit is 0, loop will break only if there are no more 
            // counterexamples to be discovered.
            if (labels == null || !labels.Any() || errorsDiscovered == errorLimit)
            {
              break;
            }
          }
          finally
          {
            if (popLater)
            {
              SendThisVC("(pop 1)");
            }
          }

          var source = labels[^2];
          var target = labels[^1];
          // block the assert which was falsified by this counterexample
          SendThisVC($"(assert (not (= (ControlFlow 0 {source}) (- {target}))))");
          SendCheckSat();
        }

        FlushLogFile();

        if (libOptions.RestartProverPerVC && Process != null)
        {
          ProcessNeedsRestart = true;
        }

        return globalResult;
      }
      finally
      {
        currentErrorHandler = null;
      }
    }

    private T WrapInPushPop<T>(ref bool popLater, Func<T> action)
    {
      if (popLater)
      {
        SendThisVC("(pop 1)");
      }
      SendThisVC("(push 1)");
      var result = action();
      popLater = true;
      return result;
    }

    private async Task<(Outcome, bool)> RunTimeoutDiagnostics(ErrorHandler handler, Outcome result, CancellationToken cancellationToken)
    {
      var popLater = false;
      if (libOptions.TraceDiagnosticsOnTimeout) {
        Console.Out.WriteLine("Starting timeout diagnostics with initial time limit {0}.", options.TimeLimit);
      }

      SendThisVC("; begin timeout diagnostics");

      var start = DateTime.UtcNow;
      var unverified = new SortedSet<int>(ctx.TimeoutDiagnosticIDToAssertion.Keys);
      var timedOut = new SortedSet<int>();
      var frac = 2;
      var queries = 0;
      var timeLimitPerAssertion = 0 < options.TimeLimit
        ? (options.TimeLimit / 100) * libOptions.TimeLimitPerAssertionInPercent
        : 1000;
      while (true) {
        var rem = unverified.Count;
        if (rem == 0) {
          if (0 < timedOut.Count) {
            
            result = await WrapInPushPop(ref popLater, () => CheckSplit(timedOut, options.TimeLimit, timeLimitPerAssertion, ref queries, cancellationToken));
            if (result == Outcome.Valid) {
              timedOut.Clear();
            } else if (result == Outcome.TimeOut) {
              // Give up and report which assertions were not verified.
              var cmds = timedOut.Select(id => ctx.TimeoutDiagnosticIDToAssertion[id]);

              if (cmds.Any()) {
                handler.OnResourceExceeded("timeout after running diagnostics", cmds);
              }
            }
          } else {
            result = Outcome.Valid;
          }

          break;
        }

        // TODO(wuestholz): Try out different ways for splitting up the work (e.g., randomly).
        var cnt = Math.Max(1, rem / frac);
        // It seems like assertions later in the control flow have smaller indexes.
        var split = new SortedSet<int>(unverified.Where((val, idx) => (rem - idx - 1) < cnt));
        Contract.Assert(0 < split.Count);
        
        var splitRes = await WrapInPushPop(ref popLater, () => CheckSplit(split, timeLimitPerAssertion, timeLimitPerAssertion,
          ref queries, cancellationToken));
        if (splitRes == Outcome.Valid) {
          unverified.ExceptWith(split);
          frac = 1;
        } else if (splitRes == Outcome.Invalid) {
          result = splitRes;
          break;
        } else if (splitRes == Outcome.TimeOut) {
          if (2 <= frac && (4 <= (rem / frac))) {
            frac *= 4;
          } else if (2 <= (rem / frac)) {
            frac *= 2;
          } else {
            timedOut.UnionWith(split);
            unverified.ExceptWith(split);
            frac = 1;
          }
        } else {
          break;
        }
      }

      unverified.UnionWith(timedOut);

      var end = DateTime.UtcNow;

      SendThisVC("; end timeout diagnostics");

      if (libOptions.TraceDiagnosticsOnTimeout) {
        Console.Out.WriteLine("Terminated timeout diagnostics after {0:F0} ms and {1} prover queries.",
          end.Subtract(start).TotalMilliseconds, queries);
        Console.Out.WriteLine("Outcome: {0}", result);
        Console.Out.WriteLine("Unverified assertions: {0} (of {1})", unverified.Count,
          ctx.TimeoutDiagnosticIDToAssertion.Keys.Count);

        var filename = "unknown";
        var assertion = ctx.TimeoutDiagnosticIDToAssertion.Values.Select(t => t.Item1)
          .FirstOrDefault(a => a.tok != null && a.tok != Token.NoToken && a.tok.filename != null);
        if (assertion != null) {
          filename = assertion.tok.filename;
        }

        File.AppendAllText("timeouts.csv",
          string.Format(";{0};{1};{2:F0};{3};{4};{5};{6}\n", filename, options.TimeLimit,
            end.Subtract(start).TotalMilliseconds, queries, result, unverified.Count,
            ctx.TimeoutDiagnosticIDToAssertion.Keys.Count));
      }

      return (result, popLater);
    }

    private Task<Outcome> CheckSplit(SortedSet<int> split, uint timeLimit, uint timeLimitPerAssertion,
      ref int queries, CancellationToken cancellationToken)
    {
      var tla = (uint)(timeLimitPerAssertion * split.Count);

      // FIXME: Gross. Timeout should be set in one place! This is also Z3 specific!
      var newTimeout = (0 < tla && tla < timeLimit) ? tla : timeLimit;
      if (newTimeout > 0)
      {
        SendThisVC(string.Format("(set-option :{0} {1})", Z3.TimeoutOption, newTimeout));
      }

      SendThisVC(string.Format("; checking split VC with {0} unverified assertions", split.Count));
      var expr = VCExpressionGenerator.True;
      foreach (var i in ctx.TimeoutDiagnosticIDToAssertion.Keys)
      {
        var lit = VCExprGen.Function(VCExpressionGenerator.TimeoutDiagnosticsOp,
          VCExprGen.Integer(BaseTypes.BigNum.FromInt(i)));
        if (split.Contains(i))
        {
          lit = VCExprGen.Not(lit);
        }

        expr = VCExprGen.AndSimp(expr, lit);
      }

      SendThisVC("(assert " + VCExpr2String(expr, 1) + ")");
      if (options.Solver == SolverKind.Z3)
      {
        SendThisVC("(apply (then (using-params propagate-values :max_rounds 1) simplify) :print false)");
      }

      FlushLogFile();
      SendCheckSat();
      queries++;
      return GetResponse(cancellationToken);
    }

    private async Task<string[]> CalculatePath(int controlFlowConstant, CancellationToken cancellationToken)
    {
      SendThisVC("(get-value ((ControlFlow " + controlFlowConstant + " 0)))");
      var path = new List<string>();
      while (true)
      {
        var response = await Process.GetProverResponse().WaitAsync(cancellationToken);
        if (response == null)
        {
          break;
        }

        if (!(response.Name == "" && response.ArgCount == 1))
        {
          break;
        }

        response = response.Arguments[0];
        if (!(response.Name == "" && response.ArgCount == 2))
        {
          break;
        }

        response = response.Arguments[1];
        var v = response.Name;
        if (v == "-" && response.ArgCount == 1)
        {
          v = response.Arguments[0].Name;
          path.Add(v);
          break;
        }
        else if (response.ArgCount != 0)
        {
          break;
        }

        path.Add(v);
        SendThisVC("(get-value ((ControlFlow " + controlFlowConstant + " " + v + ")))");
      }

      return path.ToArray();
    }

    private async Task<Model> GetErrorModel(CancellationToken cancellationToken)
    {
      if (!libOptions.ExpectingModel)
      {
        return null;
      }

      SendThisVC("(get-model)");
      Process.Ping();
      Model theModel = null;
      while (true)
      {
        var resp = await Process.GetProverResponse().WaitAsync(cancellationToken);
        if (resp == null || Process.IsPong(resp))
        {
          break;
        }

        if (theModel != null)
        {
          HandleProverError("Expecting only one model but got many");
        }

        theModel = ParseErrorModel(resp);
      }

      return theModel;
    }

    private async Task<Outcome> GetResponse(CancellationToken cancellationToken)
    {
      var result = Outcome.Undetermined;
      var wasUnknown = false;

      Process.Ping();

      while (true)
      {
        var resp = await Process.GetProverResponse().WaitAsync(cancellationToken);
        if (resp == null || Process.IsPong(resp))
        {
          break;
        }

        result = ParseOutcome(resp, out wasUnknown);
      }

      if (wasUnknown)
      {
        SendThisVC("(get-info :reason-unknown)");
        Process.Ping();
        while (true)
        {
          var resp = await Process.GetProverResponse().WaitAsync(cancellationToken);
          if (resp == null || Process.IsPong(resp))
          {
            break;
          }

          result = ParseReasonUnknown(resp, result);
          if (result == Outcome.OutOfMemory) {
            ProcessNeedsRestart = true;
          }
        }
      }

      return result;
    }

    public override async Task<object> Evaluate(VCExpr expr)
    {
      string vcString = VCExpr2String(expr, 1);
      SendThisVC("(get-value (" + vcString + "))");
      var resp = await Process.GetProverResponse();
      if (resp == null)
      {
        throw new VCExprEvaluationException();
      }

      if (!(resp.Name == "" && resp.ArgCount == 1))
      {
        throw new VCExprEvaluationException();
      }

      resp = resp.Arguments[0];
      if (resp.Name == "")
      {
        // evaluating an expression
        if (resp.ArgCount == 2)
        {
          resp = resp.Arguments[1];
        }
        else
        {
          throw new VCExprEvaluationException();
        }
      }
      else
      {
        // evaluating a variable
        if (resp.ArgCount == 1)
        {
          resp = resp.Arguments[0];
        }
        else
        {
          throw new VCExprEvaluationException();
        }
      }

      if (resp.Name == "-" && resp.ArgCount == 1) // negative int
      {
        return Microsoft.BaseTypes.BigNum.FromString("-" + resp.Arguments[0].Name);
      }

      if (resp.Name == "_" && resp.ArgCount == 2 && resp.Arguments[0].Name.StartsWith("bv")) // bitvector
      {
        return new BvConst(Microsoft.BaseTypes.BigNum.FromString(resp.Arguments[0].Name.Substring("bv".Length)),
          int.Parse(resp.Arguments[1].Name));
      }

      if (resp.Name == "fp" && resp.ArgCount == 3)
      {
        Func<SExpr, BigInteger> getBvVal = e => BigInteger.Parse(e.Arguments[0].Name.Substring("bv".Length));
        Func<SExpr, int> getBvSize = e => int.Parse(e.Arguments[1].ToString());
        bool isNeg = getBvVal(resp.Arguments[0]).IsOne;
        var expExpr = resp.Arguments[1];
        var sigExpr = resp.Arguments[2];
        BigInteger exp = getBvVal(expExpr);
        int expSize = getBvSize(expExpr);
        BigInteger sig = getBvVal(sigExpr);
        int sigSize = getBvSize(sigExpr) + 1;
        return new BaseTypes.BigFloat(isNeg, sig, exp, sigSize, expSize);
      }

      if (resp.Name == "_" && resp.ArgCount == 3)
      {
        String specialValue = resp.Arguments[0].ToString();
        int expSize = int.Parse(resp.Arguments[1].ToString());
        int sigSize = int.Parse(resp.Arguments[2].ToString());
        return new BaseTypes.BigFloat(specialValue, sigSize, expSize);
      }

      var ary = ParseArrayFromProverResponse(resp);
      if (ary != null)
      {
        return ary;
      }

      if (resp.ArgCount != 0)
      {
        throw new VCExprEvaluationException();
      }

      if (expr.Type.Equals(Boogie.Type.Bool))
      {
        return bool.Parse(resp.Name);
      }
      else if (expr.Type.Equals(Boogie.Type.Int))
      {
        return Microsoft.BaseTypes.BigNum.FromString(resp.Name);
      }
      else
      {
        return resp.Name;
      }
    }

    public override List<string> UnsatCore()
    {
      SendThisVC("(get-unsat-core)");
      var resp = Process.GetProverResponse().ToString();
      return ParseUnsatCore(resp);
    }

    public override void Check()
    {
      PrepareCommon();
      SendCheckSat();
      FlushLogFile();
    }

    private void SendCheckSat()
    {
      UsedNamedAssumes = null;
      SendThisVC("(check-sat)");
    }

    protected override void Send(string s, bool isCommon)
    {
      s = Sanitize(s);

      if (isCommon)
      {
        common.Append(s).Append("\r\n");
      }

      if (Process != null)
      {
        Process.Send(s);
      }

      if (currentLogFile != null)
      {
        currentLogFile.WriteLine(s);
        currentLogFile.Flush();
      }
    }

    public override async Task<int> GetRCount()
    {
      if (options.Solver != SolverKind.Z3) {
        // Only Z3 currently supports retrieving this value. CVC5
        // supports setting a limit, but does not appear to support
        // reporting how much it took to complete a query.
        return 0;
      }

      SendThisVC($"(get-info :{Z3.RlimitOption})");
      return ParseRCount(await Process.GetProverResponse());
    }

    /// <summary>
    /// Extra state for ApiChecker (used by stratifiedInlining)
    /// </summary>
    static int nameCounter;

    public override async Task<(Outcome, List<int>)> CheckAssumptions(List<VCExpr> assumptions,
      ErrorHandler handler, CancellationToken cancellationToken)
    {
      Push();
      // Name the assumptions
      var nameToAssumption = new Dictionary<string, int>();
      int i = 0;
      foreach (var vc in assumptions)
      {
        var name = "a" + nameCounter.ToString();
        nameCounter++;
        nameToAssumption.Add(name, i);

        string vcString = VCExpr2String(vc, 1);
        AssertAxioms();
        SendThisVC(string.Format("(assert (! {0} :named {1}))", vcString, name));
        i++;
      }

      Check();

      var outcome = await CheckOutcomeCore(handler, cancellationToken, libOptions.ErrorLimit);

      if (outcome != Outcome.Valid)
      {
        Pop();
        return (outcome, new List<int>());
      }

      Contract.Assert(usingUnsatCore, "SMTLib prover not setup for computing unsat cores");
      SendThisVC("(get-unsat-core)");
      var resp = await Process.GetProverResponse().WaitAsync(cancellationToken);
      var unsatCore = new List<int>();
      if (resp is not null && resp.Name != "")
      {
        unsatCore.Add(nameToAssumption[resp.Name]);
      }

      if (resp is not null)
      {
        foreach (var s in resp.Arguments)
        {
          unsatCore.Add(nameToAssumption[s.Name]);
        }
      }

      FlushLogFile();
      Pop();
      return (outcome, unsatCore);
    }

    public override async Task<(Outcome, List<int>)> CheckAssumptions(List<VCExpr> hardAssumptions, List<VCExpr> softAssumptions,
      ErrorHandler handler, CancellationToken cancellationToken)
    {

      // First, convert both hard and soft assumptions to SMTLIB strings
      var hardAssumptionStrings = new List<string>();
      foreach (var a in hardAssumptions)
      {
        hardAssumptionStrings.Add(VCExpr2String(a, 1));
      }

      var currAssumptionStrings = new List<string>();
      foreach (var a in softAssumptions)
      {
        currAssumptionStrings.Add(VCExpr2String(a, 1));
      }

      Push();
      AssertAxioms();
      foreach (var a in hardAssumptionStrings)
      {
        SendThisVC("(assert " + a + ")");
      }

      Check();
      var outcome = await GetResponse(cancellationToken);
      if (outcome != Outcome.Invalid)
      {
        Pop();
        return (outcome, new List<int>());
      }

      var k = 0;
      var relaxVars = new List<string>();
      var unsatisfiedSoftAssumptions = new List<int>();
      while (true)
      {
        Push();
        foreach (var a in currAssumptionStrings)
        {
          SendThisVC("(assert " + a + ")");
        }

        Check();
        outcome = await CheckOutcomeCore(handler, cancellationToken, libOptions.ErrorLimit);
        if (outcome != Outcome.Valid)
        {
          break;
        }

        Pop();
        var relaxVar = "relax_" + k;
        relaxVars.Add(relaxVar);
        SendThisVC("(declare-fun " + relaxVar + " () Int)");
        var nextAssumptionStrings = new List<string>();
        for (var i = 0; i < currAssumptionStrings.Count; i++)
        {
          var constraint = "(= " + relaxVar + " " + i + ")";
          nextAssumptionStrings.Add("(or " + currAssumptionStrings[i] + " " + constraint + ")");
        }

        currAssumptionStrings = nextAssumptionStrings;
        k++;
      }

      if (outcome == Outcome.Invalid)
      {
        foreach (var relaxVar in relaxVars)
        {
          SendThisVC("(get-value (" + relaxVar + "))");
          FlushLogFile();
          var resp = await Process.GetProverResponse().WaitAsync(cancellationToken);
          if (resp == null)
          {
            break;
          }

          if (!(resp.Name == "" && resp.ArgCount == 1))
          {
            break;
          }

          resp = resp.Arguments[0];
          if (!(resp.Name != "" && resp.ArgCount == 1))
          {
            break;
          }

          resp = resp.Arguments[0];
          if (resp.ArgCount != 0)
          {
            break;
          }

          if (int.TryParse(resp.Name, out var v))
          {
            unsatisfiedSoftAssumptions.Add(v);
          }
          else
          {
            break;
          }
        }

        Pop();
      }

      Pop();
      return (outcome, unsatisfiedSoftAssumptions);
    }
  }
}
