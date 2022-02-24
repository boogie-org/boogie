using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Globalization;
using System.Numerics;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.TypeErasure;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibBatchTheoremProver : SMTLibProcessTheoremProver
  {
    private SMTLibSolver Process;
    private bool CheckSatSent;
    private int resourceCount;
    private Model errorModel;

    [NotDelayed]
    public SMTLibBatchTheoremProver(SMTLibOptions libOptions, ProverOptions options, VCExpressionGenerator gen,
      SMTLibProverContext ctx) : base(libOptions, options, gen, ctx)
    {
      if (usingUnsatCore) {
        throw new NotSupportedException("Batch mode solver interface does not support unsat cores.");
      }
    }

    public override Task GoBackToIdle()
    {
      return Task.CompletedTask;
    }

    private void SetupProcess()
    {
      Process?.Close();
      Process = options.Solver == SolverKind.NoOpWithZ3Options ? new NoopSolver() : new SMTLibProcess(libOptions, options);
      Process.ErrorHandler += HandleProverError;
      CheckSatSent = false;
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

    public override void Close()
    {
      base.Close();
      Process?.Close();
      Process = null;
    }

    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
    {
      SetupProcess();
      FullReset(gen);

      if (options.LogFilename != null && currentLogFile == null) {
        currentLogFile = OpenOutputFile(descriptiveName);
        currentLogFile.Write(common.ToString());
      }

      PrepareCommon();
      FlushAxioms();

      OptimizationRequests.Clear();

      string vcString = "(assert (not\n" + VCExpr2String(vc, 1) + "\n))";
      FlushAxioms();

      Push();
      SendVCAndOptions(descriptiveName, vcString);
      SendOptimizationRequests();

      FlushLogFile();

      Process.NewProblem(descriptiveName);

      SendCheckSat();
      Pop();

      FlushLogFile();
    }

    public override void Reset(VCExpressionGenerator generator)
    {
    }

    public override void FullReset(VCExpressionGenerator generator)
    {
      if (options.Solver == SolverKind.Z3 || options.Solver == SolverKind.NoOpWithZ3Options)
      {
        this.gen = generator;
        common.Clear();
        SetupAxiomBuilder(gen);
        Axioms.Clear();
        TypeDecls.Clear();
        AxiomsAreSetup = false;
        /*
        ctx.Reset();
        ctx.KnownDatatypes.Clear();
        ctx.parent = this;
        */
        DeclCollector.Reset();
        NamedAssumes.Clear();
        UsedNamedAssumes = null;
      }
    }

    // TODO: move to base?
    private void FlushProverWarnings()
    {
      var handler = currentErrorHandler;
      if (handler != null) {
        lock (proverWarnings) {
          proverWarnings.Iter(handler.OnProverWarning);
          proverWarnings.Clear();
        }
      }
    }

    [NoDefaultContract]
    public override async Task<Outcome> CheckOutcome(ErrorHandler handler, int errorLimit, CancellationToken cancellationToken)
    {
      var result = await CheckOutcomeCore(handler, cancellationToken, errorLimit);

      FlushLogFile();

      return result;
    }

    [NoDefaultContract]
    public override async Task<Outcome> CheckOutcomeCore(ErrorHandler handler, CancellationToken cancellationToken,
      int errorLimit)
    {
      if (Process == null || proverErrors.Count > 0) {
        return Outcome.Undetermined;
      }

      try {
        currentErrorHandler = handler;
        FlushProverWarnings();

        var result = await GetResponse(cancellationToken);

        if (result == Outcome.Invalid) {
          var labels = CalculatePath(handler.StartingProcId(), errorModel, cancellationToken);
          if (labels.Length == 0) {
            // Without a path to an error, we don't know what to report
            result = Outcome.Undetermined;
          } else {
            handler.OnModel(labels, errorModel, result);
          }
        }

        // Note: batch mode never tries to discover more errors

        FlushLogFile();

        Close();

        return result;
      } finally {
        Close();
        currentErrorHandler = null;
      }
    }

    private async Task<Outcome> GetResponse(CancellationToken cancellationToken)
    {
      var wasUnknown = false;

      var outcomeSExp = await Process.GetProverResponse().WaitAsync(cancellationToken);
      var result = ParseOutcome(outcomeSExp, out wasUnknown);

      var unknownSExp = await Process.GetProverResponse().WaitAsync(cancellationToken);
      if (wasUnknown) {
        result = ParseReasonUnknown(unknownSExp, result);
      }

      var rlimitSExp = await Process.GetProverResponse().WaitAsync(cancellationToken);
      resourceCount = ParseRCount(rlimitSExp);

      var modelSExp = await Process.GetProverResponse().WaitAsync(cancellationToken);
      errorModel = GetErrorModel(modelSExp, cancellationToken);

      return result;
    }

    private string[] CalculatePath(int controlFlowConstant, Model model, CancellationToken cancellationToken)
    {
      var path = new List<string>();

      if (model is null) {
        return path.ToArray();
      }

      var function = model.TryGetFunc("ControlFlow");
      var controlFlowElement = model.TryMkElement(controlFlowConstant.ToString());
      var zeroElement = model.TryMkElement("0");
      var v = zeroElement;

      while (true) {
        var result = function?.TryEval(controlFlowElement, v) ?? function?.Else;
        if (result is null) {
          break;
        }
        var resultData = result as Model.DatatypeValue;

        if (resultData is not null && resultData.Arguments.Length >= 1) {
          path.Add(resultData.Arguments[0].ToString());
          break;
        } else if (result is Model.Integer) {
          path.Add(result.ToString());
        } else {
          HandleProverError($"Invalid control flow model received from solver.");
          break;
        }

        v = result;
      }

      return path.ToArray();
    }

    private Model GetErrorModel(SExpr resp, CancellationToken cancellationToken)
    {
      if (resp is null) {
        return null;
      }

      Model theModel = null;
      string modelStr = null;

      if (resp.ArgCount >= 1) {
        var converter = new SMTErrorModelConverter(resp, this);
        modelStr = converter.Convert();
      } else if (resp.ArgCount == 0 && resp.Name.Contains("->")) {
        modelStr = resp.Name;
      } else {
        HandleProverError("Unexpected prover response getting model: " + resp);
      }

      List<Model> models = null;
      try {
        switch (options.Solver) {
          case SolverKind.Z3:
          case SolverKind.CVC5:
            models = Model.ParseModels(new StringReader("Error model: \n" + modelStr), Namer.GetOriginalName);
            break;
          default:
            Debug.Assert(false);
            return null;
        }
      } catch (ArgumentException exn) {
        HandleProverError("Model parsing error: " + exn.Message);
      }

      if (models == null) {
        HandleProverError("Could not parse any models");
      } else if (models.Count == 0) {
        HandleProverError("Could not parse any models");
      } else if (models.Count > 1) {
        HandleProverError("Expecting only one model but got many");
      } else {
        theModel = models[0];
      }

      return theModel;
    }

    public override Task<object> Evaluate(VCExpr expr)
    {
      throw new NotSupportedException("Batch mode solver interface does not support evaluating SMT expressions.");
    }

    public override void Check()
    {
      throw new NotSupportedException("Batch mode solver interface does not support the Check call.");
    }

    private void SendCheckSat()
    {
      UsedNamedAssumes = null;
      SendThisVC("(check-sat)");
      SendThisVC("(get-info :reason-unknown)");
      SendThisVC("(get-info :rlimit)");
      SendThisVC("(get-model)");
      CheckSatSent = true;
      Process.IndicateEndOfInput();
    }

    protected override void Send(string s, bool isCommon)
    {
      s = Sanitize(s);

      if (isCommon) {
        common.Append(s).Append("\r\n");
      }

      // Boogie emits comments after the solver has responded. In batch
      // mode, sending these to the solver is problematic. But they'll
      // still get sent to the log below.
      if (Process != null && !CheckSatSent) {
        Process.Send(s);
      }

      if (currentLogFile != null) {
        currentLogFile.WriteLine(s);
        currentLogFile.Flush();
      }
    }

    public override Task<int> GetRCount()
    {
      return Task.FromResult(resourceCount);
    }

    public override List<string> UnsatCore()
    {
      throw new NotSupportedException("Batch mode solver interface does not support unsat cores.");
    }

    public override Task<(Outcome, List<int>)> CheckAssumptions(List<VCExpr> assumptions,
      ErrorHandler handler, CancellationToken cancellationToken)
    {
      throw new NotSupportedException("Batch mode solver interface does not support checking assumptions.");
    }

    public override Task<(Outcome, List<int>)> CheckAssumptions(List<VCExpr> hardAssumptions, List<VCExpr> softAssumptions,
      ErrorHandler handler, CancellationToken cancellationToken)
    {
      throw new NotSupportedException("Batch mode solver interface does not support checking assumptions.");
    }
  }
}
