using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.VCExprAST;
using System.Threading.Tasks;
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
    private DateTime proverStart;
    private TimeSpan proverRunTime;
    private volatile ProverInterface.ErrorHandler handler;
    private volatile CheckerStatus status;
    private readonly CheckerPool pool;
    public volatile Program Program;
    public readonly ProverOptions SolverOptions;

    public void GetReady()
    {
      Contract.Requires(IsIdle);

      status = CheckerStatus.Ready;
    }

    public void GoBackToIdle()
    {
      Contract.Requires(IsBusy);

      status = CheckerStatus.Idle;
      pool.AddChecker(this);
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

    /////////////////////////////////////////////////////////////////////////////////
    // We share context information for the same program between different Checkers

    /////////////////////////////////////////////////////////////////////////////////

    /// <summary>
    /// Constructor.  Initialize a checker with the program and log file.
    /// Optionally, use prover context provided by parameter "ctx".
    /// </summary>
    public Checker(CheckerPool pool, VC.ConditionGeneration vcgen, Program prog, string /*?*/ logFilePath, bool appendLogFile,
      Split split, ProverContext ctx = null)
    {
      Contract.Requires(vcgen != null);
      Contract.Requires(prog != null);
      this.pool = pool;
      this.Program = prog;

      SolverOptions = cce.NonNull(CommandLineOptions.Clo.TheProverFactory).BlankProverOptions();

      if (logFilePath != null)
      {
        SolverOptions.LogFilename = logFilePath;
        if (appendLogFile)
        {
          SolverOptions.AppendLogFile = appendLogFile;
        }
      }

      SolverOptions.Parse(CommandLineOptions.Clo.ProverOptions);

      ContextCacheKey key = new ContextCacheKey(prog);
      ProverInterface prover;

      if (vcgen.CheckerCommonState == null)
      {
        vcgen.CheckerCommonState = new Dictionary<ContextCacheKey, ProverContext>();
      }

      IDictionary<ContextCacheKey, ProverContext> /*!>!*/
        cachedContexts = (IDictionary<ContextCacheKey, ProverContext /*!*/>) vcgen.CheckerCommonState;

      if (ctx == null && cachedContexts.TryGetValue(key, out ctx))
      {
        ctx = (ProverContext) cce.NonNull(ctx).Clone();
        prover = (ProverInterface)
          CommandLineOptions.Clo.TheProverFactory.SpawnProver(CommandLineOptions.Clo, SolverOptions, ctx);
      }
      else
      {
        if (ctx == null)
        {
          ctx = (ProverContext) CommandLineOptions.Clo.TheProverFactory.NewProverContext(SolverOptions);
        }

        Setup(prog, ctx, split);

        // we first generate the prover and then store a clone of the
        // context in the cache, so that the prover can setup stuff in
        // the context to be cached
        prover = (ProverInterface)
          CommandLineOptions.Clo.TheProverFactory.SpawnProver(CommandLineOptions.Clo, SolverOptions, ctx);
        cachedContexts.Add(key, cce.NonNull((ProverContext) ctx.Clone()));
      }

      this.thmProver = prover;
      this.gen = prover.VCExprGen;
    }

    public void Retarget(Program prog, ProverContext ctx, Split s)
    {
      lock (this)
      {
        hasOutput = default(bool);
        outcome = default(ProverInterface.Outcome);
        outputExn = default(UnexpectedProverOutputException);
        handler = default(ProverInterface.ErrorHandler);
        TheoremProver.FullReset(gen);
        ctx.Reset();
        Setup(prog, ctx, s);
      }
    }

    public void RetargetWithoutReset(Program prog, ProverContext ctx)
    {
      ctx.Clear();
      Setup(prog, ctx);
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
    private void Setup(Program prog, ProverContext ctx, Split split = null)
    {
      SolverOptions.RandomSeed = split?.RandomSeed ?? CommandLineOptions.Clo.RandomSeed;
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

    private static IEnumerable<Declaration> GetReorderedDeclarations(IEnumerable<Declaration> declarations, Random random)
    {
      if (random == null) {
        // By ordering the declarations based on their content and naming them based on order, the solver input stays content under reordering and renaming.
        return CommandLineOptions.Clo.NormalizeDeclarationOrder
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

    public int ProverResourceCount
    {
      get { return thmProver.GetRCount(); }
    }

    private void WaitForOutput(object dummy)
    {
      lock (this)
      {
        try
        {
          outcome = thmProver.CheckOutcome(cce.NonNull(handler), CommandLineOptions.Clo.ErrorLimit);
        }
        catch (UnexpectedProverOutputException e)
        {
          outputExn = e;
        }
        catch (Exception e)
        {
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

    public void BeginCheck(string descriptiveName, VCExpr vc, ProverInterface.ErrorHandler handler, uint timeout, uint rlimit)
    {
      Contract.Requires(descriptiveName != null);
      Contract.Requires(vc != null);
      Contract.Requires(handler != null);
      Contract.Requires(IsReady);

      status = CheckerStatus.Busy;
      hasOutput = false;
      outputExn = null;
      this.handler = handler;

      thmProver.Reset(gen);
      if (0 < rlimit)
      {
        timeout = 0;
      }
      SetTimeout(timeout);
      SetRlimit(rlimit);
      proverStart = DateTime.UtcNow;
      thmProver.BeginCheck(descriptiveName, vc, handler);
      //  gen.ClearSharedFormulas();    PR: don't know yet what to do with this guy

      ProverTask = Task.Factory.StartNew(() => { WaitForOutput(null); }, TaskCreationOptions.LongRunning);
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

    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
    {
      /*Contract.Requires(descriptiveName != null);*/
      //Contract.Requires(vc != null);
      //Contract.Requires(handler != null);
      throw new NotImplementedException();
    }

    [NoDefaultContract]
    public override Outcome CheckOutcome(ErrorHandler handler, int taskID = -1)
    {
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

  public class UnexpectedProverOutputException : ProverException
  {
    public UnexpectedProverOutputException(string s)
      : base(s)
    {
    }
  }

  public class ProverDiedException : UnexpectedProverOutputException
  {
    public ProverDiedException()
      : base("Prover died with no further output, perhaps it ran out of memory or was killed.")
    {
    }
  }
}
