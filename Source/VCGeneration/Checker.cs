using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Threading;
using Microsoft.Boogie.VCExprAST;
using System.Threading.Tasks;
using Microsoft.Boogie.SMTLib;
using VC;

namespace Microsoft.Boogie
{
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
  public sealed class Checker
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(gen != null);
      Contract.Invariant(thmProver != null);
    }

    private readonly VCExpressionGenerator gen;

    private ProverInterface thmProver;

    // state for the async interface
    private volatile ProverInterface.Outcome outcome;
    private volatile bool hasOutput;
    private volatile UnexpectedProverOutputException outputExn;
    public DateTime ProverStart { get; private set; }
    private TimeSpan proverRunTime;
    private volatile ProverInterface.ErrorHandler handler;
    private volatile CheckerStatus status;
    public volatile Program Program;
    public readonly ProverOptions SolverOptions;

    public VCGenOptions Options => Pool.Options;
    public CheckerPool Pool { get; }

    public void GetReady()
    {
      Contract.Requires(IsIdle);

      status = CheckerStatus.Ready;
    }

    public async Task GoBackToIdle()
    {
      Contract.Requires(IsBusy);

      status = CheckerStatus.Idle;
      try {
        await thmProver.GoBackToIdle().WaitAsync(TimeSpan.FromMilliseconds(100));
        Pool.AddChecker(this);
      }
      catch(TimeoutException) {
        Pool.CheckerDied();
        Close();
      }
    }

    public Task ProverTask { get; set; }

    public bool WillingToHandle(Program prog)
    {
      return status == CheckerStatus.Idle && (prog == null || Program == prog);
    }

    public VCExpressionGenerator VCExprGen
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);
        return this.gen;
      }
    }

    public ProverInterface TheoremProver
    {
      get
      {
        Contract.Ensures(Contract.Result<ProverInterface>() != null);
        return this.thmProver;
      }
    }

    public Checker(CheckerPool pool, string /*?*/ logFilePath, bool appendLogFile)
    {
      Pool = pool;

      SolverOptions = cce.NonNull(Pool.Options.TheProverFactory).BlankProverOptions(pool.Options);

      if (logFilePath != null)
      {
        SolverOptions.LogFilename = logFilePath;
        if (appendLogFile)
        {
          SolverOptions.AppendLogFile = appendLogFile;
        }
      }

      SolverOptions.Parse(Options.ProverOptions);

      var ctx = Pool.Options.TheProverFactory.NewProverContext(SolverOptions);

      SolverOptions.RandomSeed = Options.RandomSeed;
      var prover = Pool.Options.TheProverFactory.SpawnProver(Pool.Options, SolverOptions, ctx);
      
      thmProver = prover;
      gen = prover.VCExprGen;
    }

    public void Target(Program prog, ProverContext ctx, Split split)
    {
      lock (this)
      {
        hasOutput = default;
        outcome = default;
        outputExn = default;
        handler = default;
        TheoremProver.FullReset(gen);
        ctx.Reset();
        Setup(prog, ctx, split);
      }
    }

    private void SetTimeout(uint timeout)
    {
      TheoremProver.SetTimeout(Util.BoundedMultiply(timeout, 1000));
    }

    private void SetRlimit(uint rlimit)
    {
      TheoremProver.SetRlimit(Util.BoundedMultiply(rlimit, 1000));
    }
    
    /// <summary>
    /// Set up the context.
    /// </summary>
    private void Setup(Program prog, ProverContext ctx, Split split)
    {
      SolverOptions.RandomSeed = 1 < Options.RandomSeedIterations ? split.NextRandom() : split.RandomSeed;
      var random = SolverOptions.RandomSeed == null ? null : new Random(SolverOptions.RandomSeed.Value);

      Program = prog;
      // TODO(wuestholz): Is this lock necessary?
      lock (Program.TopLevelDeclarations)
      {
        var declarations = split == null ? prog.TopLevelDeclarations : split.TopLevelDeclarations;
        var reorderedDeclarations = GetReorderedDeclarations(declarations, random);
        foreach (var declaration in reorderedDeclarations) {
          Contract.Assert(declaration != null);
          if (declaration is TypeCtorDecl typeDecl)
          {
            ctx.DeclareType(typeDecl, null);
          }
          else if (declaration is Constant constDecl)
          {
            ctx.DeclareConstant(constDecl, constDecl.Unique, null);
          }
          else if (declaration is Function funDecl)
          {
            ctx.DeclareFunction(funDecl, null);
          }
          else if (declaration is Axiom axiomDecl)
          {
            ctx.AddAxiom(axiomDecl, null);
          }
          else if (declaration is GlobalVariable glVarDecl)
          {
            ctx.DeclareGlobalVariable(glVarDecl, null);
          }
        }
      }
    }

    private IEnumerable<Declaration> GetReorderedDeclarations(IEnumerable<Declaration> declarations, Random random)
    {
      if (random == null) {
        // By ordering the declarations based on their content and naming them based on order, the solver input stays constant under reordering and renaming.
        return Options.NormalizeDeclarationOrder
          ? declarations.OrderBy(d => d.ContentHash)
          : declarations;
      }

      var copy = declarations.ToList();
      Util.Shuffle(random, copy);
      return copy;
    }

    /// <summary>
    /// Clean-up.
    /// </summary>
    public void Close()
    {
      thmProver.Close();
      status = CheckerStatus.Closed;
    }

    /// <summary>
    /// Push a Verification Condition as an Axiom
    /// (Required for Doomed Program Point detection)
    /// </summary>
    public void PushVCExpr(VCExpr vc)
    {
      Contract.Requires(vc != null);
      //thmProver.Context.AddAxiom(vc);
      thmProver.PushVCExpression(vc);
    }

    public bool IsBusy
    {
      get { return status == CheckerStatus.Busy; }
    }

    public bool IsReady
    {
      get { return status == CheckerStatus.Ready; }
    }

    public bool IsClosed
    {
      get { return status == CheckerStatus.Closed; }
    }

    public bool IsIdle
    {
      get { return status == CheckerStatus.Idle; }
    }

    public bool HasOutput
    {
      get { return hasOutput; }
    }

    public TimeSpan ProverRunTime
    {
      get { return proverRunTime; }
    }

    public Task<int> GetProverResourceCount()
    {
      return thmProver.GetRCount();
    }


    private async Task Check(string descriptiveName, VCExpr vc, CancellationToken cancellationToken) {
      try {
        outcome = await thmProver.Check(descriptiveName, vc, cce.NonNull(handler), Options.ErrorLimit,
          cancellationToken);
      }
      catch (OperationCanceledException) {
        throw;
      }
      catch (UnexpectedProverOutputException e)
      {
        outputExn = e;
      }
      catch (ProverException) {
        throw;
      }
      catch (Exception e)
      {
        outputExn = new UnexpectedProverOutputException(e.ToString());
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
      proverRunTime = DateTime.UtcNow - ProverStart;
    }

    public async Task BeginCheck(string descriptiveName, VCExpr vc, ProverInterface.ErrorHandler handler, uint timeout, uint rlimit, CancellationToken cancellationToken)
    {
      Contract.Requires(descriptiveName != null);
      Contract.Requires(vc != null);
      Contract.Requires(handler != null);
      Contract.Requires(IsReady);

      status = CheckerStatus.Busy;
      hasOutput = false;
      outputExn = null;
      this.handler = handler;

      await thmProver.Reset(gen);
      if (0 < rlimit)
      {
        timeout = 0;
      }
      SetTimeout(timeout);
      SetRlimit(rlimit);
      ProverStart = DateTime.UtcNow;

      ProverTask = Check(descriptiveName, vc, cancellationToken);
    }

    public ProverInterface.Outcome ReadOutcome()
    {
      Contract.Requires(IsBusy);
      Contract.Requires(HasOutput);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      hasOutput = false;

      if (outputExn != null)
      {
        throw outputExn;
      }

      return outcome;
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public class ProverInterfaceContracts : ProverInterface
  {
    public override ProverContext Context
    {
      get
      {
        Contract.Ensures(Contract.Result<ProverContext>() != null);

        throw new NotImplementedException();
      }
    }

    public override VCExpressionGenerator VCExprGen
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);

        throw new NotImplementedException();
      }
    }

    public override Task GoBackToIdle()
    {
      throw new NotImplementedException();
    }

    public override Task<Outcome> Check(string descriptiveName, VCExpr vc, ErrorHandler handler, int errorLimit,
      CancellationToken cancellationToken) {
      throw new NotImplementedException();
    }

    public override Task Reset(VCExpressionGenerator gen)
    {
      throw new NotImplementedException();
    }

    public override void FullReset(VCExpressionGenerator gen)
    {
      throw new NotImplementedException();
    }
  }
}
