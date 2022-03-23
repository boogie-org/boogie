using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using VC;
using BoogiePL = Microsoft.Boogie;
using System.Runtime.Caching;
using System.Diagnostics;
using System.Net.Mime;

namespace Microsoft.Boogie
{
  #region Output printing

  public interface OutputPrinter
  {
    ExecutionEngineOptions Options { get; set; }
    void ErrorWriteLine(TextWriter tw, string s);
    void ErrorWriteLine(TextWriter tw, string format, params object[] args);
    void AdvisoryWriteLine(TextWriter output, string format, params object[] args);
    void Inform(string s, TextWriter tw);
    void WriteTrailer(TextWriter textWriter, PipelineStatistics stats);
    void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true);
    void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null);
  }

  #endregion

  public enum PipelineOutcome
  {
    Done,
    ResolutionError,
    TypeCheckingError,
    ResolvedAndTypeChecked,
    FatalError,
    Cancelled,
    VerificationCompleted
  }


  public class PipelineStatistics
  {
    public int ErrorCount;
    public int VerifiedCount;
    public int InconclusiveCount;
    public int TimeoutCount;
    public int OutOfResourceCount;
    public int OutOfMemoryCount;
    public int SolverExceptionCount;
    public long[] CachingActionCounts;
    public int CachedErrorCount;
    public int CachedVerifiedCount;
    public int CachedInconclusiveCount;
    public int CachedTimeoutCount;
    public int CachedOutOfResourceCount;
    public int CachedOutOfMemoryCount;
    public int CachedSolverExceptionCount;
  }


  #region Error reporting

  public delegate void ErrorReporterDelegate(ErrorInformation errInfo);


  public enum ErrorKind
  {
    Assertion,
    Precondition,
    Postcondition,
    InvariantEntry,
    InvariantMaintainance
  }


  public class ErrorInformationFactory
  {
    public virtual ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId = null,
      string originalRequestId = null, string category = null)
    {
      Contract.Requires(1 <= tok.line && 1 <= tok.col);
      Contract.Requires(msg != null);

      return ErrorInformation.CreateErrorInformation(tok, msg, requestId, originalRequestId, category);
    }
  }


  public class ErrorInformation
  {
    public readonly IToken Tok;
    public string Msg;
    public string Category { get; set; }
    public readonly List<AuxErrorInfo> Aux = new List<AuxErrorInfo>();
    public string OriginalRequestId { get; set; }
    public string RequestId { get; set; }
    public ErrorKind Kind { get; set; }
    public string ImplementationName { get; set; }
    public TextWriter Out = new StringWriter();
    public TextWriter ModelWriter = new StringWriter();

    public string FullMsg
    {
      get
      {
        return Category != null ? string.Format("{0}: {1}", Category, Msg) : Msg;
      }
    }

    public struct AuxErrorInfo
    {
      public readonly IToken Tok;
      public readonly string Msg;
      public readonly string Category;

      public string FullMsg
      {
        get { return Category != null ? string.Format("{0}: {1}", Category, Msg) : Msg; }
      }

      public AuxErrorInfo(IToken tok, string msg, string category = null)
      {
        Tok = tok;
        Msg = CleanUp(msg);
        Category = category;
      }
    }

    protected ErrorInformation(IToken tok, string msg)
    {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= tok.line && 1 <= tok.col);
      Contract.Requires(msg != null);

      Tok = tok;
      Msg = CleanUp(msg);
    }

    internal static ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId = null,
      string originalRequestId = null, string category = null)
    {
      var result = new ErrorInformation(tok, msg);
      result.RequestId = requestId;
      result.OriginalRequestId = originalRequestId;
      result.Category = category;
      return result;
    }

    public virtual void AddAuxInfo(IToken tok, string msg, string category = null)
    {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= tok.line && 1 <= tok.col);
      Contract.Requires(msg != null);
      Aux.Add(new AuxErrorInfo(tok, msg, category));
    }

    protected static string CleanUp(string msg)
    {
      if (msg.ToLower().StartsWith("error: "))
      {
        return msg.Substring(7);
      }
      else
      {
        return msg;
      }
    }
  }

  #endregion

  public class ExecutionEngine : IDisposable {
    public static ErrorInformationFactory ErrorInformationFactory { get; } = new();

    static int autoRequestIdCount;

    static readonly string AutoRequestIdPrefix = "auto_request_id_";

    public static string FreshRequestId() {
      var id = Interlocked.Increment(ref autoRequestIdCount);
      return AutoRequestIdPrefix + id;
    }

    public static int AutoRequestId(string id) {
      if (id.StartsWith(AutoRequestIdPrefix)) {
        if (int.TryParse(id.Substring(AutoRequestIdPrefix.Length), out var result)) {
          return result;
        }
      }

      return -1;
    }

    public readonly VerificationResultCache Cache;

    static readonly MemoryCache programCache = new MemoryCache("ProgramCache");

    static readonly CacheItemPolicy policy = new CacheItemPolicy
      { SlidingExpiration = new TimeSpan(0, 10, 0), Priority = CacheItemPriority.Default };

    public static Program CachedProgram(string programId) {
      var result = programCache.Get(programId) as Program;
      return result;
    }

    public ExecutionEngine(ExecutionEngineOptions options, VerificationResultCache cache) {
      Options = options;
      Cache = cache;
      checkerPool = new CheckerPool(options);
      verifyImplementationSemaphore = new SemaphoreSlim(Options.VcsCores);
    }

    public static ExecutionEngine CreateWithoutSharedCache(ExecutionEngineOptions options) {
      return new ExecutionEngine(options, new VerificationResultCache());
    }

    public ExecutionEngineOptions Options { get; }
    private readonly CheckerPool checkerPool;
    private readonly SemaphoreSlim verifyImplementationSemaphore;

    static DateTime FirstRequestStart;

    static readonly ConcurrentDictionary<string, TimeSpan>
      TimePerRequest = new ConcurrentDictionary<string, TimeSpan>();

    static readonly ConcurrentDictionary<string, PipelineStatistics> StatisticsPerRequest =
      new ConcurrentDictionary<string, PipelineStatistics>();

    static readonly ConcurrentDictionary<string, CancellationTokenSource> ImplIdToCancellationTokenSource =
      new ConcurrentDictionary<string, CancellationTokenSource>();

    static readonly ConcurrentDictionary<string, CancellationTokenSource> RequestIdToCancellationTokenSource =
      new ConcurrentDictionary<string, CancellationTokenSource>();

    public async Task<bool> ProcessFiles(TextWriter output, IList<string> fileNames, bool lookForSnapshots = true,
      string programId = null) {
      Contract.Requires(cce.NonNullElements(fileNames));

      if (Options.VerifySeparately && 1 < fileNames.Count) {
        var success = true;
        foreach (var fileName in fileNames) {
          success &= await ProcessFiles(output, new List<string> { fileName }, lookForSnapshots, fileName);
        }
        return success;
      }

      if (0 <= Options.VerifySnapshots && lookForSnapshots) {
        var snapshotsByVersion = LookForSnapshots(fileNames);
        var success = true;
        foreach (var snapshots in snapshotsByVersion) {
          // BUG: Reusing checkers during snapshots doesn't work, even though it should. We create a new engine (and thus checker pool) to workaround this.
          using var engine = new ExecutionEngine(Options, Cache);
          success &= await engine.ProcessFiles(output, new List<string>(snapshots), false, programId);
        }
        return success;
      }

      using XmlFileScope xf = new XmlFileScope(Options.XmlSink, fileNames[^1]);
      Program program = ParseBoogieProgram(fileNames, false);
      var bplFileName = fileNames[^1];
      if (program == null) {
        return true;
      }

      return await ProcessProgram(output, program, bplFileName, programId);
    }

    [Obsolete("Please inline this method call")]
    public bool ProcessProgram(Program program, string bplFileName,
      string programId = null) {
      return ProcessProgram(Console.Out, program, bplFileName, programId).Result;
    }

    public async Task<bool> ProcessProgram(TextWriter output, Program program, string bplFileName, string programId = null)
    {
      if (programId == null)
      {
        programId = "main_program_id";
      }
      
      if (Options.PrintFile != null) {
        PrintBplFile(Options.PrintFile, program, false, true, Options.PrettyPrint);
      }

      PipelineOutcome outcome = ResolveAndTypecheck(program, bplFileName, out var civlTypeChecker);
      if (outcome != PipelineOutcome.ResolvedAndTypeChecked) {
        return true;
      }

      if (Options.PrintCFGPrefix != null) {
        foreach (var impl in program.Implementations) {
          using StreamWriter sw = new StreamWriter(Options.PrintCFGPrefix + "." + impl.Name + ".dot");
          sw.Write(program.ProcessLoops(Options, impl).ToDot());
        }
      }

      CivlVCGeneration.Transform(Options, civlTypeChecker);
      if (Options.CivlDesugaredFile != null) {
        int oldPrintUnstructured = Options.PrintUnstructured;
        Options.PrintUnstructured = 1;
        PrintBplFile(Options.CivlDesugaredFile, program, false, false,
          Options.PrettyPrint);
        Options.PrintUnstructured = oldPrintUnstructured;
      }

      EliminateDeadVariables(program);

      CoalesceBlocks(program);

      Inline(program);

      var stats = new PipelineStatistics();
      outcome = await InferAndVerify(output, program, stats, 1 < Options.VerifySnapshots ? programId : null);
      switch (outcome) {
        case PipelineOutcome.Done:
        case PipelineOutcome.VerificationCompleted:
          Options.Printer.WriteTrailer(output, stats);
          return true;
        case PipelineOutcome.FatalError:
          return false;
        default:
          Debug.Assert(false, "Unreachable code");
          return false;
      }
    }

    public static IList<IList<string>> LookForSnapshots(IList<string> fileNames)
    {
      Contract.Requires(fileNames != null);

      var result = new List<IList<string>>();
      for (int version = 0; true; version++)
      {
        var nextSnapshot = new List<string>();
        foreach (var name in fileNames)
        {
          var versionedName = name.Replace(Path.GetExtension(name), ".v" + version + Path.GetExtension(name));
          if (File.Exists(versionedName))
          {
            nextSnapshot.Add(versionedName);
          }
        }

        if (nextSnapshot.Any())
        {
          result.Add(nextSnapshot);
        }
        else
        {
          break;
        }
      }

      return result;
    }

    public void CoalesceBlocks(Program program)
    {
      if (Options.CoalesceBlocks)
      {
        if (Options.Trace)
        {
          Console.WriteLine("Coalescing blocks...");
        }

        Microsoft.Boogie.BlockCoalescer.CoalesceBlocks(program);
      }
    }


    public void CollectModSets(Program program)
    {
      if (Options.DoModSetAnalysis)
      {
        new ModSetCollector(Options).DoModSetAnalysis(program);
      }
    }


    public void EliminateDeadVariables(Program program)
    {
      Microsoft.Boogie.UnusedVarEliminator.Eliminate(program);
    }


    public void PrintBplFile(string filename, Program program, bool allowPrintDesugaring, bool setTokens = true,
      bool pretty = false)
    {
      PrintBplFile(Options, filename, program, allowPrintDesugaring, setTokens, pretty);
    }

    public static void PrintBplFile(ExecutionEngineOptions options, string filename, Program program, bool allowPrintDesugaring, bool setTokens = true,
      bool pretty = false)

    {
      Contract.Requires(program != null);
      Contract.Requires(filename != null);
      bool oldPrintDesugaring = options.PrintDesugarings;
      if (!allowPrintDesugaring)
      {
        options.PrintDesugarings = false;
      }

      using (TokenTextWriter writer = filename == "-"
        ? new TokenTextWriter("<console>", Console.Out, setTokens, pretty, options)
        : new TokenTextWriter(filename, setTokens, pretty, options))
      {
        if (options.ShowEnv != ExecutionEngineOptions.ShowEnvironment.Never)
        {
          writer.WriteLine("// " + options.Version);
          writer.WriteLine("// " + options.Environment);
        }

        writer.WriteLine();
        program.Emit(writer);
      }

      options.PrintDesugarings = oldPrintDesugaring;
    }


    /// <summary>
    /// Parse the given files into one Boogie program.  If an I/O or parse error occurs, an error will be printed
    /// and null will be returned.  On success, a non-null program is returned.
    /// </summary>
    public Program ParseBoogieProgram(IList<string> fileNames, bool suppressTraceOutput)
    {
      Contract.Requires(cce.NonNullElements(fileNames));

      Program program = new Program();
      bool okay = true;
      
      for (int fileId = 0; fileId < fileNames.Count; fileId++)
      {
        string bplFileName = fileNames[fileId];
        if (!suppressTraceOutput)
        {
          if (Options.XmlSink != null)
          {
            Options.XmlSink.WriteFileFragment(bplFileName);
          }

          if (Options.Trace)
          {
            Console.WriteLine("Parsing " + GetFileNameForConsole(Options, bplFileName));
          }
        }

        try
        {
          var defines = new List<string>() {"FILE_" + fileId};
          int errorCount = Parser.Parse(bplFileName, defines, out Program programSnippet,
            Options.UseBaseNameForFileName);
          if (programSnippet == null || errorCount != 0)
          {
            Console.WriteLine("{0} parse errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
            okay = false;
          }
          else
          {
            program.AddTopLevelDeclarations(programSnippet.TopLevelDeclarations);
          }
        }
        catch (IOException e)
        {
          Options.Printer.ErrorWriteLine(Console.Out, "Error opening file \"{0}\": {1}",
            GetFileNameForConsole(Options, bplFileName), e.Message);
          okay = false;
        }
      }

      if (!okay)
      {
        return null;
      }
      else
      {
        if (program.TopLevelDeclarations.Any(d => d.HasCivlAttribute()))
        {
          Options.UseLibrary = true;
        }

        if (Options.UseLibrary)
        {
          Options.UseArrayTheory = true;
          Options.Monomorphize = true;
          var library = Parser.ParseLibraryDefinitions();
          program.AddTopLevelDeclarations(library.TopLevelDeclarations);
        }

        return program;
      }
    }

    internal static string GetFileNameForConsole(ExecutionEngineOptions options, string filename)
    {
      return options.UseBaseNameForFileName && !string.IsNullOrEmpty(filename) &&
             filename != "<console>"
        ? Path.GetFileName(filename)
        : filename;
    }


    /// <summary>
    /// Resolves and type checks the given Boogie program.  Any errors are reported to the
    /// console.  Returns:
    ///  - Done if no errors occurred, and command line specified no resolution or no type checking.
    ///  - ResolutionError if a resolution error occurred
    ///  - TypeCheckingError if a type checking error occurred
    ///  - ResolvedAndTypeChecked if both resolution and type checking succeeded
    /// </summary>
    public PipelineOutcome ResolveAndTypecheck(Program program, string bplFileName,
      out CivlTypeChecker civlTypeChecker)
    {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);

      civlTypeChecker = null;

      // ---------- Resolve ------------------------------------------------------------

      if (Options.NoResolve)
      {
        return PipelineOutcome.Done;
      }

      int errorCount = program.Resolve(Options);
      if (errorCount != 0)
      {
        Console.WriteLine("{0} name resolution errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.ResolutionError;
      }

      // ---------- Type check ------------------------------------------------------------

      if (Options.NoTypecheck)
      {
        return PipelineOutcome.Done;
      }

      if (!FunctionDependencyChecker.Check(program))
      {
        return PipelineOutcome.TypeCheckingError;
      }
      
      errorCount = program.Typecheck(Options);
      if (errorCount != 0)
      {
        Console.WriteLine("{0} type checking errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.TypeCheckingError;
      }

      if (MonomorphismChecker.IsMonomorphic(program))
      {
        Options.TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
      }
      else if (Options.Monomorphize)
      {
        var monomorphizableStatus = Monomorphizer.Monomorphize(Options, program);
        if (monomorphizableStatus == MonomorphizableStatus.Monomorphizable)
        {
          Options.TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
        }
        else if (monomorphizableStatus == MonomorphizableStatus.UnhandledPolymorphism)
        {
          Console.WriteLine("Unable to monomorphize input program: unhandled polymorphic features detected");
          return PipelineOutcome.FatalError;
        }
        else
        {
          Console.WriteLine("Unable to monomorphize input program: expanding type cycle detected");
          return PipelineOutcome.FatalError;
        }
      }
      else if (Options.UseArrayTheory)
      {
        Console.WriteLine(
          "Option /useArrayTheory only supported for monomorphic programs, polymorphism is detected in input program, try using -monomorphize");
        return PipelineOutcome.FatalError;
      } 
      else if (program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>().Any())
      {
        Console.WriteLine(
          "Datatypes only supported for monomorphic programs, polymorphism is detected in input program, try using -monomorphize");
        return PipelineOutcome.FatalError;
      }

      CollectModSets(program);

      civlTypeChecker = new CivlTypeChecker(Options, program);
      civlTypeChecker.TypeCheck();
      if (civlTypeChecker.checkingContext.ErrorCount != 0)
      {
        Console.WriteLine("{0} type checking errors detected in {1}", civlTypeChecker.checkingContext.ErrorCount,
          GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.TypeCheckingError;
      }

      if (Options.PrintFile != null && Options.PrintDesugarings)
      {
        // if PrintDesugaring option is engaged, print the file here, after resolution and type checking
        PrintBplFile(Options.PrintFile, program, true, true, Options.PrettyPrint);
      }

      return PipelineOutcome.ResolvedAndTypeChecked;
    }


    public void Inline(Program program)
    {
      Contract.Requires(program != null);

      if (Options.Trace)
      {
        Console.WriteLine("Inlining...");
      }

      // Inline
      var TopLevelDeclarations = cce.NonNull(program.TopLevelDeclarations);

      if (Options.ProcedureInlining != CoreOptions.Inlining.None)
      {
        bool inline = false;
        foreach (var d in TopLevelDeclarations)
        {
          if ((d is Procedure || d is Implementation) && d.FindExprAttribute("inline") != null)
          {
            inline = true;
          }
        }

        if (inline)
        {
          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            impl.OriginalBlocks = impl.Blocks;
            impl.OriginalLocVars = impl.LocVars;
          }

          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            if (Options.UserWantsToCheckRoutine(impl.Name) && !impl.IsSkipVerification(Options))
            {
              Inliner.ProcessImplementation(Options, program, impl);
            }
          }

          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            impl.OriginalBlocks = null;
            impl.OriginalLocVars = null;
          }
        }
      }
    }

    [Obsolete("Please inline this method call")]
    public PipelineOutcome InferAndVerify(
      Program program,
      PipelineStatistics stats,
      string programId = null,
      ErrorReporterDelegate er = null, string requestId = null) {
      return InferAndVerify(Console.Out, program, stats, programId, er, requestId).Result;
    }

    /// <summary>
    /// Given a resolved and type checked Boogie program, infers invariants for the program
    /// and then attempts to verify it.  Returns:
    ///  - Done if command line specified no verification
    ///  - FatalError if a fatal error occurred, in which case an error has been printed to console
    ///  - VerificationCompleted if inference and verification completed, in which the out
    ///    parameters contain meaningful values
    /// </summary>
    public async Task<PipelineOutcome> InferAndVerify(
      TextWriter output,
      Program program,
      PipelineStatistics stats,
      string programId = null,
      ErrorReporterDelegate er = null, string requestId = null)
    {
      Contract.Requires(program != null);
      Contract.Requires(stats != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out stats.InconclusiveCount) &&
                       0 <= Contract.ValueAtReturn(out stats.TimeoutCount));

      requestId ??= FreshRequestId();


      var start = DateTime.UtcNow;

      #region Do some pre-abstract-interpretation preprocessing on the program

      // Doing lambda expansion before abstract interpretation means that the abstract interpreter
      // never needs to see any lambda expressions.  (On the other hand, if it were useful for it
      // to see lambdas, then it would be better to more lambda expansion until after inference.)
      if (Options.ExpandLambdas)
      {
        LambdaHelper.ExpandLambdas(Options, program);
        if (Options.PrintFile != null && Options.PrintLambdaLifting)
        {
          PrintBplFile(Options.PrintFile, program, false, true, Options.PrettyPrint);
        }
      }

      #endregion

      if (Options.UseAbstractInterpretation)
      {
        new AbstractInterpretation.NativeAbstractInterpretation(Options).RunAbstractInterpretation(program);
      }

      #region Do some post-abstract-interpretation preprocessing on the program (e.g., loop unrolling)

      if (Options.LoopUnrollCount != -1)
      {
        program.UnrollLoops(Options.LoopUnrollCount, Options.SoundLoopUnrolling);
      }

      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo = null;
      if (Options.ExtractLoops)
      {
        extractLoopMappingInfo = program.ExtractLoops(Options);
      }

      if (Options.PrintInstrumented)
      {
        program.Emit(new TokenTextWriter(Console.Out, Options.PrettyPrint, Options));
      }

      #endregion

      if (!Options.Verify)
      {
        return PipelineOutcome.Done;
      }

      if (Options.ContractInfer)
      {
        return await RunHoudini(program, stats, er);
      }

      var stablePrioritizedImpls = GetPrioritizedImplementations(program);

      if (1 < Options.VerifySnapshots)
      {
        CachedVerificationResultInjector.Inject(this, program, stablePrioritizedImpls, requestId, programId,
          out stats.CachingActionCounts);
      }

      var outcome = await VerifyEachImplementation(output, program, stats, programId, er, requestId, stablePrioritizedImpls, extractLoopMappingInfo);

      if (1 < Options.VerifySnapshots && programId != null)
      {
        program.FreezeTopLevelDeclarations();
        programCache.Set(programId, program, policy);
      }

      TraceCachingForBenchmarking(stats, requestId, start);

      return outcome;
    }

    private Implementation[] GetPrioritizedImplementations(Program program)
    {
      var impls = program.Implementations.Where(
        impl => impl != null && Options.UserWantsToCheckRoutine(cce.NonNull(impl.Name)) &&
                !impl.IsSkipVerification(Options));

      // operate on a stable copy, in case it gets updated while we're running
      Implementation[] stablePrioritizedImpls = null;
      if (0 < Options.VerifySnapshots) {
        OtherDefinitionAxiomsCollector.Collect(Options, program.Axioms);
        DependencyCollector.Collect(Options, program);
        stablePrioritizedImpls = impls.OrderByDescending(
          impl => impl.Priority != 1 ? impl.Priority : Cache.VerificationPriority(impl, Options.RunDiagnosticsOnTimeout)).ToArray();
      } else {
        stablePrioritizedImpls = impls.OrderByDescending(impl => impl.Priority).ToArray();
      }

      return stablePrioritizedImpls;
    }

    private async Task<PipelineOutcome> VerifyEachImplementation(TextWriter output, Program program,
      PipelineStatistics stats,
      string programId, ErrorReporterDelegate er, string requestId, Implementation[] stablePrioritizedImpls,
      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
      var consoleCollector = new ConcurrentToSequentialWriteManager(output);
      program.DeclarationDependencies = Prune.ComputeDeclarationDependencies(Options, program);

      var cts = new CancellationTokenSource();
      RequestIdToCancellationTokenSource.AddOrUpdate(requestId, cts, (k, ov) => cts);

      var tasks = stablePrioritizedImpls.Select(async (impl, index) => {
        await using var taskWriter = consoleCollector.AppendWriter();
        var result = await VerifyImplementationAsynchronously(program, stats, programId, er, requestId,
          stablePrioritizedImpls, extractLoopMappingInfo, cts, index, taskWriter);
        return result;
      }).ToList();
      var outcome = PipelineOutcome.VerificationCompleted;

      try {
        await Task.WhenAll(tasks);
        foreach (var task in tasks) {
          task.Result.ProcessXml(this);
        }
      } catch(TaskCanceledException) {
        outcome = PipelineOutcome.Cancelled;
      } catch(ProverException e) {
        Options.Printer.ErrorWriteLine(Console.Out, "Fatal Error: ProverException: {0}", e.Message);
        outcome = PipelineOutcome.FatalError;
      }
      finally {
        CleanupRequest(requestId);
      }

      if (Options.PrintNecessaryAssumes && program.NecessaryAssumes.Any()) {
        Console.WriteLine("Necessary assume command(s): {0}", string.Join(", ", program.NecessaryAssumes.OrderBy(s => s)));
      }

      cce.NonNull(Options.TheProverFactory).Close();

      return outcome;

    }

    async Task<VerificationResult> VerifyImplementationAsynchronously(
      Program program, PipelineStatistics stats,
      string programId, ErrorReporterDelegate er, string requestId, Implementation[] stablePrioritizedImpls,
      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo,
      CancellationTokenSource cts,
      int index, TextWriter taskWriter)
    {
      var implementation = stablePrioritizedImpls[index];
      var id = implementation.Id;
      if (ImplIdToCancellationTokenSource.TryGetValue(id, out var old)) {
        old.Cancel();
      }

      await verifyImplementationSemaphore.WaitAsync(cts.Token);
      try {

        ImplIdToCancellationTokenSource.AddOrUpdate(id, cts, (k, ov) => cts);

        var coreTask = Task.Run(() => VerifyImplementation(program, stats, er, requestId,
          extractLoopMappingInfo, implementation,
          programId, taskWriter), cts.Token);

        var verificationResult = await coreTask;
        var output = verificationResult.GetOutput(Options.Printer, this, stats, er, implementation);

        await taskWriter.WriteAsync(output);
        return verificationResult;
      }
      finally {
        taskWriter.Close();
        verifyImplementationSemaphore.Release();
        ImplIdToCancellationTokenSource.TryRemove(id, out old);
      }
    }

    private void TraceCachingForBenchmarking(PipelineStatistics stats,
      string requestId, DateTime start)
    {
      if (0 <= Options.VerifySnapshots && Options.TraceCachingForBenchmarking) {
        var end = DateTime.UtcNow;
        if (TimePerRequest.Count == 0) {
          FirstRequestStart = start;
        }

        TimePerRequest[requestId] = end.Subtract(start);
        StatisticsPerRequest[requestId] = stats;

        var printTimes = true;

        Console.Out.WriteLine(CachedVerificationResultInjector.Statistics.Output(printTimes));

        Console.Out.WriteLine("Statistics per request as CSV:");
        var actions = string.Join(", ", Enum.GetNames(typeof(VC.ConditionGeneration.CachingAction)));
        Console.Out.WriteLine(
          "Request ID{0}, Error, E (C), Inconclusive, I (C), Out of Memory, OoM (C), Timeout, T (C), Verified, V (C), {1}",
          printTimes ? ", Time (ms)" : "", actions);
        foreach (var kv in TimePerRequest.OrderBy(kv => ExecutionEngine.AutoRequestId(kv.Key))) {
          var s = StatisticsPerRequest[kv.Key];
          var cacs = s.CachingActionCounts;
          var c = cacs != null ? ", " + cacs.Select(ac => string.Format("{0,3}", ac)).Concat(", ") : "";
          var t = printTimes ? string.Format(", {0,8:F0}", kv.Value.TotalMilliseconds) : "";
          Console.Out.WriteLine(
            "{0,-19}{1}, {2,2}, {3,2}, {4,2}, {5,2}, {6,2}, {7,2}, {8,2}, {9,2}, {10,2}, {11,2}{12}", kv.Key, t,
            s.ErrorCount, s.CachedErrorCount, s.InconclusiveCount, s.CachedInconclusiveCount, s.OutOfMemoryCount,
            s.CachedOutOfMemoryCount, s.TimeoutCount, s.CachedTimeoutCount, s.VerifiedCount, s.CachedVerifiedCount, c);
        }

        if (printTimes) {
          Console.Out.WriteLine();
          Console.Out.WriteLine("Total time (ms) since first request: {0:F0}",
            end.Subtract(FirstRequestStart).TotalMilliseconds);
        }
      }
    }

    public static void CancelRequest(string requestId)
    {
      Contract.Requires(requestId != null);

      if (RequestIdToCancellationTokenSource.TryGetValue(requestId, out var cts))
      {
        cts.Cancel();

        CleanupRequest(requestId);
      }
    }

    private static void CleanupRequest(string requestId)
    {
      if (requestId != null)
      {
        RequestIdToCancellationTokenSource.TryRemove(requestId, out var old);
      }
    }

    private async Task<VerificationResult> VerifyImplementation(
      Program program,
      PipelineStatistics stats,
      ErrorReporterDelegate er,
      string requestId, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo,
      Implementation implementation,
      string programId,
      TextWriter traceWriter)
    {
      VerificationResult verificationResult = GetCachedVerificationResult(implementation, traceWriter);
      if (verificationResult != null) {
        UpdateCachedStatistics(stats, verificationResult.Outcome, verificationResult.Errors);
        return verificationResult;
      }

      Options.Printer.Inform("", traceWriter); // newline
      Options.Printer.Inform($"Verifying {implementation.Name} ...", traceWriter);

      verificationResult = await VerifyImplementationWithoutCaching(program, stats, er, requestId,
        extractLoopMappingInfo, programId, implementation, traceWriter);

      if (0 < Options.VerifySnapshots && !string.IsNullOrEmpty(implementation.Checksum))
      {
        Cache.Insert(implementation, verificationResult);
      }

      return verificationResult;
    }

    private VerificationResult GetCachedVerificationResult(Implementation impl, TextWriter output)
    {
      if (0 >= Options.VerifySnapshots)
      {
        return null;
      }

      var cachedResults = Cache.Lookup(impl, Options.RunDiagnosticsOnTimeout, out var priority);
      if (cachedResults == null || priority != Priority.SKIP)
      {
        return null;
      }

      if (Options.VerifySnapshots < 3 ||
          cachedResults.Outcome == ConditionGeneration.Outcome.Correct) {
        Options.Printer.Inform($"Retrieving cached verification result for implementation {impl.Name}...", output);
        return cachedResults;
      }

      return null;
    }

    private ConditionGeneration CreateVCGen(Program program)
    {
      return new VCGen(program, checkerPool);
    }

    private async Task<VerificationResult> VerifyImplementationWithoutCaching(Program program,
      PipelineStatistics stats, ErrorReporterDelegate er, string requestId,
      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo,
      string programId, Implementation impl, TextWriter traceWriter)
    {
      var verificationResult = new VerificationResult(requestId, impl, programId);

      using var vcgen = new VCGen(program, checkerPool);

      vcgen.CachingActionCounts = stats.CachingActionCounts;
      verificationResult.ProofObligationCountBefore = vcgen.CumulativeAssertionCount;
      verificationResult.Start = DateTime.UtcNow;

      try {
        var cancellationToken = RequestIdToCancellationTokenSource[requestId].Token;
        (verificationResult.Outcome, verificationResult.Errors, verificationResult.VCResults) =
          await vcgen.VerifyImplementation(new ImplementationRun(impl, traceWriter), requestId, cancellationToken);
        if (Options.ExtractLoops && verificationResult.Errors != null) {
          if (vcgen is VCGen vcg) {
            for (int i = 0; i < verificationResult.Errors.Count; i++) {
              verificationResult.Errors[i] = vcg.extractLoopTrace(verificationResult.Errors[i], impl.Name,
                program, extractLoopMappingInfo);
            }
          }
        }
      } catch (VCGenException e) {
        var errorInfo = ErrorInformationFactory.CreateErrorInformation(impl.tok,
          $"{e.Message} (encountered in implementation {impl.Name}).", requestId, "Error");
        errorInfo.ImplementationName = impl.Name;
        verificationResult.ErrorBeforeVerification = errorInfo;
        if (er != null) {
          lock (er) {
            er(errorInfo);
          }
        }

        verificationResult.Errors = null;
        verificationResult.Outcome = VCGen.Outcome.Inconclusive;
      } catch (ProverDiedException) {
        throw;
      } catch (UnexpectedProverOutputException upo) {
        Options.Printer.AdvisoryWriteLine(traceWriter,
          "Advisory: {0} SKIPPED because of internal error: unexpected prover output: {1}",
          impl.Name, upo.Message);
        verificationResult.Errors = null;
        verificationResult.Outcome = VCGen.Outcome.Inconclusive;
      } catch (IOException e) {
        Options.Printer.AdvisoryWriteLine(traceWriter, "Advisory: {0} SKIPPED due to I/O exception: {1}",
          impl.Name, e.Message);
        verificationResult.Errors = null;
        verificationResult.Outcome = VCGen.Outcome.SolverException;
      }

      verificationResult.ProofObligationCountAfter = vcgen.CumulativeAssertionCount;
      verificationResult.End = DateTime.UtcNow;
      verificationResult.ResourceCount = vcgen.ResourceCount;

      return verificationResult;
    }


    #region Houdini

    private async Task<PipelineOutcome> RunHoudini(Program program, PipelineStatistics stats, ErrorReporterDelegate er)
    {
      Contract.Requires(stats != null);
      
      if (Options.StagedHoudini != null)
      {
        return await RunStagedHoudini(program, stats, er);
      }

      Houdini.HoudiniSession.HoudiniStatistics houdiniStats = new Houdini.HoudiniSession.HoudiniStatistics();
      Houdini.Houdini houdini = new Houdini.Houdini(Console.Out, Options, program, houdiniStats);
      Houdini.HoudiniOutcome outcome = await houdini.PerformHoudiniInference();
      houdini.Close();

      if (Options.PrintAssignment)
      {
        Console.WriteLine("Assignment computed by Houdini:");
        foreach (var x in outcome.assignment)
        {
          Console.WriteLine(x.Key + " = " + x.Value);
        }
      }

      if (Options.Trace)
      {
        int numTrueAssigns = 0;
        foreach (var x in outcome.assignment)
        {
          if (x.Value)
          {
            numTrueAssigns++;
          }
        }

        Console.WriteLine("Number of true assignments = " + numTrueAssigns);
        Console.WriteLine("Number of false assignments = " + (outcome.assignment.Count - numTrueAssigns));
        Console.WriteLine("Prover time = " + houdiniStats.proverTime.ToString("F2"));
        Console.WriteLine("Unsat core prover time = " + houdiniStats.unsatCoreProverTime.ToString("F2"));
        Console.WriteLine("Number of prover queries = " + houdiniStats.numProverQueries);
        Console.WriteLine("Number of unsat core prover queries = " + houdiniStats.numUnsatCoreProverQueries);
        Console.WriteLine("Number of unsat core prunings = " + houdiniStats.numUnsatCorePrunings);
      }

      foreach (Houdini.VCGenOutcome x in outcome.implementationOutcomes.Values)
      {
        ProcessOutcome(Options.Printer, x.outcome, x.errors, "", stats, Console.Out, Options.TimeLimit, er);
        ProcessErrors(Options.Printer, x.errors, x.outcome, Console.Out, er);
      }

      return PipelineOutcome.Done;
    }

    public Program ProgramFromFile(string filename)
    {
      Program p = ParseBoogieProgram( new List<string> {filename}, false);
      Debug.Assert(p != null);
      PipelineOutcome oc = ResolveAndTypecheck(p, filename, out var civlTypeChecker);
      Debug.Assert(oc == PipelineOutcome.ResolvedAndTypeChecked);
      return p;
    }

    private async Task<PipelineOutcome> RunStagedHoudini(Program program, PipelineStatistics stats, ErrorReporterDelegate er)
    {
      Houdini.HoudiniSession.HoudiniStatistics houdiniStats = new Houdini.HoudiniSession.HoudiniStatistics();
      var stagedHoudini = new Houdini.StagedHoudini(Console.Out, Options, program, houdiniStats, ProgramFromFile);
      Houdini.HoudiniOutcome outcome = await stagedHoudini.PerformStagedHoudiniInference();

      if (Options.PrintAssignment)
      {
        Console.WriteLine("Assignment computed by Houdini:");
        foreach (var x in outcome.assignment)
        {
          Console.WriteLine(x.Key + " = " + x.Value);
        }
      }

      if (Options.Trace)
      {
        int numTrueAssigns = 0;
        foreach (var x in outcome.assignment)
        {
          if (x.Value)
          {
            numTrueAssigns++;
          }
        }

        Console.WriteLine("Number of true assignments = " + numTrueAssigns);
        Console.WriteLine("Number of false assignments = " + (outcome.assignment.Count - numTrueAssigns));
        Console.WriteLine("Prover time = " + houdiniStats.proverTime.ToString("F2"));
        Console.WriteLine("Unsat core prover time = " + houdiniStats.unsatCoreProverTime.ToString("F2"));
        Console.WriteLine("Number of prover queries = " + houdiniStats.numProverQueries);
        Console.WriteLine("Number of unsat core prover queries = " + houdiniStats.numUnsatCoreProverQueries);
        Console.WriteLine("Number of unsat core prunings = " + houdiniStats.numUnsatCorePrunings);
      }

      foreach (Houdini.VCGenOutcome x in outcome.implementationOutcomes.Values)
      {
        ProcessOutcome(Options.Printer, x.outcome, x.errors, "", stats, Console.Out, Options.TimeLimit, er);
        ProcessErrors(Options.Printer, x.errors, x.outcome, Console.Out, er);
      }

      return PipelineOutcome.Done;
    }

    #endregion

    public void ProcessOutcome(OutputPrinter printer, ConditionGeneration.Outcome outcome, List<Counterexample> errors, string timeIndication,
      PipelineStatistics stats, TextWriter tw, uint timeLimit, ErrorReporterDelegate er = null, string implName = null,
      IToken implTok = null, string requestId = null, string msgIfVerifies = null)
    {
      Contract.Requires(stats != null);

      UpdateStatistics(stats, outcome, errors);

      printer.Inform(timeIndication + OutcomeIndication(outcome, errors), tw);

      ReportOutcome(printer, outcome, er, implName, implTok, requestId, msgIfVerifies, tw, timeLimit, errors);
    }

    public void ReportOutcome(OutputPrinter printer,
      ConditionGeneration.Outcome outcome, ErrorReporterDelegate er, string implName,
      IToken implTok, string requestId, string msgIfVerifies, TextWriter tw, uint timeLimit, List<Counterexample> errors)
    {
      ErrorInformation errorInfo = null;

      switch (outcome)
      {
        case VCGen.Outcome.Correct:
          if (msgIfVerifies != null)
          {
            tw.WriteLine(msgIfVerifies);
          }
          break;
        case VCGen.Outcome.ReachedBound:
          tw.WriteLine($"Stratified Inlining: Reached recursion bound of {Options.RecursionBound}");
          break;
        case VCGen.Outcome.Errors:
        case VCGen.Outcome.TimedOut:
          if (implName != null && implTok != null)
          {
            if (outcome == ConditionGeneration.Outcome.TimedOut ||
                (errors != null && errors.Any(e => e.IsAuxiliaryCexForDiagnosingTimeouts)))
            {
              errorInfo = ExecutionEngine.ErrorInformationFactory.CreateErrorInformation(implTok,
                string.Format("Verification of '{1}' timed out after {0} seconds", timeLimit, implName), requestId);
            }

            //  Report timed out assertions as auxiliary info.
            if (errors != null)
            {
              var cmpr = new CounterexampleComparer();
              var timedOutAssertions = errors.Where(e => e.IsAuxiliaryCexForDiagnosingTimeouts).Distinct(cmpr).ToList();
              timedOutAssertions.Sort(cmpr);
              if (0 < timedOutAssertions.Count)
              {
                errorInfo.Msg += $" with {timedOutAssertions.Count} check(s) that timed out individually";
              }

              foreach (Counterexample error in timedOutAssertions)
              {
                var callError = error as CallCounterexample;
                var returnError = error as ReturnCounterexample;
                var assertError = error as AssertCounterexample;
                IToken tok = null;
                string msg = null;
                if (callError != null)
                {
                  tok = callError.FailingCall.tok;
                  msg = callError.FailingCall.ErrorData as string ??
                        callError.FailingCall.Description.FailureDescription;
                }
                else if (returnError != null)
                {
                  tok = returnError.FailingReturn.tok;
                  msg = returnError.FailingReturn.Description.FailureDescription;
                }
                else
                {
                  tok = assertError.FailingAssert.tok;
                  if (assertError.FailingAssert.ErrorMessage == null || Options.ForceBplErrors) {
                      msg = assertError.FailingAssert.ErrorData as string;
                  }
                  else {
                    msg = assertError.FailingAssert.ErrorMessage;
                  }
                  msg ??= assertError.FailingAssert.Description.FailureDescription;
                }

                errorInfo.AddAuxInfo(tok, msg, "Unverified check due to timeout");
              }
            }
          }

          break;
        case VCGen.Outcome.OutOfResource:
          if (implName != null && implTok != null)
          {
            errorInfo = ExecutionEngine.ErrorInformationFactory.CreateErrorInformation(implTok,
              "Verification out of resource (" + implName + ")", requestId);
          }

          break;
        case VCGen.Outcome.OutOfMemory:
          if (implName != null && implTok != null)
          {
            errorInfo = ExecutionEngine.ErrorInformationFactory.CreateErrorInformation(implTok,
              "Verification out of memory (" + implName + ")", requestId);
          }

          break;
        case VCGen.Outcome.SolverException:
          if (implName != null && implTok != null)
          {
            errorInfo = ExecutionEngine.ErrorInformationFactory.CreateErrorInformation(implTok,
              "Verification encountered solver exception (" + implName + ")", requestId);
          }

          break;

        case VCGen.Outcome.Inconclusive:
          if (implName != null && implTok != null)
          {
            errorInfo = ExecutionEngine.ErrorInformationFactory.CreateErrorInformation(implTok,
              "Verification inconclusive (" + implName + ")", requestId);
          }

          break;
      }

      if (errorInfo != null)
      {
        errorInfo.ImplementationName = implName;
        if (er != null)
        {
          lock (er)
          {
            er(errorInfo);
          }
        }
        else
        {
          printer.WriteErrorInformation(errorInfo, tw);
        }
      }
    }


    private static string OutcomeIndication(VC.VCGen.Outcome outcome, List<Counterexample> errors)
    {
      string traceOutput = "";
      switch (outcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new cce.UnreachableException();
        case VCGen.Outcome.ReachedBound:
          traceOutput = "verified";
          break;
        case VCGen.Outcome.Correct:
          traceOutput = "verified";
          break;
        case VCGen.Outcome.TimedOut:
          traceOutput = "timed out";
          break;
        case VCGen.Outcome.OutOfResource:
          traceOutput = "out of resource";
          break;
        case VCGen.Outcome.OutOfMemory:
          traceOutput = "out of memory";
          break;
        case VCGen.Outcome.SolverException:
          traceOutput = "solver exception";
          break;
        case VCGen.Outcome.Inconclusive:
          traceOutput = "inconclusive";
          break;
        case VCGen.Outcome.Errors:
          Contract.Assert(errors != null);
          traceOutput = string.Format("error{0}", errors.Count == 1 ? "" : "s");
          break;
      }

      return traceOutput;
    }


    private static void UpdateStatistics(PipelineStatistics stats, VC.VCGen.Outcome outcome, List<Counterexample> errors)
    {
      Contract.Requires(stats != null);

      switch (outcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new cce.UnreachableException();
        case VCGen.Outcome.ReachedBound:
          Interlocked.Increment(ref stats.VerifiedCount);

          break;
        case VCGen.Outcome.Correct:
          Interlocked.Increment(ref stats.VerifiedCount);

          break;
        case VCGen.Outcome.TimedOut:
          Interlocked.Increment(ref stats.TimeoutCount);

          break;
        case VCGen.Outcome.OutOfResource:
          Interlocked.Increment(ref stats.OutOfResourceCount);

          break;
        case VCGen.Outcome.OutOfMemory:
          Interlocked.Increment(ref stats.OutOfMemoryCount);

          break;
        case VCGen.Outcome.SolverException:
          Interlocked.Increment(ref stats.SolverExceptionCount);

          break;
        case VCGen.Outcome.Inconclusive:
          Interlocked.Increment(ref stats.InconclusiveCount);

          break;
        case VCGen.Outcome.Errors:
          int cnt = errors.Count(e => !e.IsAuxiliaryCexForDiagnosingTimeouts);
          Interlocked.Add(ref stats.ErrorCount, cnt);

          break;
      }
    }

    private static void UpdateCachedStatistics(PipelineStatistics stats, VC.VCGen.Outcome outcome, List<Counterexample> errors) {
      Contract.Requires(stats != null);

      switch (outcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new cce.UnreachableException();
        case VCGen.Outcome.ReachedBound:
          Interlocked.Increment(ref stats.CachedVerifiedCount);

          break;
        case VCGen.Outcome.Correct:
          Interlocked.Increment(ref stats.CachedVerifiedCount);

          break;
        case VCGen.Outcome.TimedOut:
          Interlocked.Increment(ref stats.CachedTimeoutCount);

          break;
        case VCGen.Outcome.OutOfResource:
          Interlocked.Increment(ref stats.CachedOutOfResourceCount);

          break;
        case VCGen.Outcome.OutOfMemory:
          Interlocked.Increment(ref stats.CachedOutOfMemoryCount);

          break;
        case VCGen.Outcome.SolverException:
          Interlocked.Increment(ref stats.CachedSolverExceptionCount);

          break;
        case VCGen.Outcome.Inconclusive:
          Interlocked.Increment(ref stats.CachedInconclusiveCount);

          break;
        case VCGen.Outcome.Errors:
          int cnt = errors.Count(e => !e.IsAuxiliaryCexForDiagnosingTimeouts);
          Interlocked.Add(ref stats.CachedErrorCount, cnt);

          break;
      }
    }

    public void ProcessErrors(OutputPrinter printer,
      List<Counterexample> errors,
      ConditionGeneration.Outcome outcome, TextWriter tw,
      ErrorReporterDelegate er, Implementation impl = null)
    {
      var implName = impl?.Name;

      if (errors == null)
      {
        return;
      }

      errors.Sort(new CounterexampleComparer());
      foreach (Counterexample error in errors)
      {
        if (error.IsAuxiliaryCexForDiagnosingTimeouts)
        {
          continue;
        }

        var errorInfo = CreateErrorInformation(error, outcome);
        errorInfo.ImplementationName = implName;

        if (Options.XmlSink != null)
        {
          WriteErrorInformationToXmlSink(Options.XmlSink, errorInfo, error.Trace);
        }

        if (Options.ErrorTrace > 0)
        {
          errorInfo.Out.WriteLine("Execution trace:");
          error.Print(4, errorInfo.Out, b => { errorInfo.AddAuxInfo(b.tok, b.Label, "Execution trace"); });
          if (Options.EnhancedErrorMessages == 1 && error.AugmentedTrace != null && error.AugmentedTrace.Count > 0)
          {
            errorInfo.Out.WriteLine("Augmented execution trace:");
            error.AugmentedTrace.Iter(elem => errorInfo.Out.Write(elem));
          }
          if (Options.PrintErrorModel >= 1 && error.Model != null)
          {
            error.Model.Write(Options.ModelWriter ?? errorInfo.Out);
          }
        }

        if (Options.ModelViewFile != null) {
          error.PrintModel(errorInfo.ModelWriter, error);
        }

        printer.WriteErrorInformation(errorInfo, tw);

        if (er != null)
        {
          lock (er)
          {
            er(errorInfo);
          }
        }
      }
    }

    private ErrorInformation CreateErrorInformation(Counterexample error, VC.VCGen.Outcome outcome)
    {
      ErrorInformation errorInfo;
      var cause = "Error";
      if (outcome == VCGen.Outcome.TimedOut)
      {
        cause = "Timed out on";
      }
      else if (outcome == VCGen.Outcome.OutOfMemory)
      {
        cause = "Out of memory on";
      }
      else if (outcome == VCGen.Outcome.SolverException)
      {
        cause = "Solver exception on";
      }
      else if (outcome == VCGen.Outcome.OutOfResource)
      {
        cause = "Out of resource on";
      }

      if (error is CallCounterexample callError)
      {
        if (callError.FailingRequires.ErrorMessage == null || Options.ForceBplErrors)
        {
          errorInfo = ErrorInformationFactory.CreateErrorInformation(callError.FailingCall.tok,
            callError.FailingCall.ErrorData as string ?? callError.FailingCall.Description.FailureDescription,
            callError.RequestId, callError.OriginalRequestId, cause);
          errorInfo.Kind = ErrorKind.Precondition;
          errorInfo.AddAuxInfo(callError.FailingRequires.tok,
            callError.FailingRequires.ErrorData as string ?? callError.FailingRequires.Description.FailureDescription,
            "Related location");
        }
        else
        {
          errorInfo = ExecutionEngine.ErrorInformationFactory.CreateErrorInformation(null,
            callError.FailingRequires.ErrorMessage,
            callError.RequestId, callError.OriginalRequestId);
        }
      }
      else if (error is ReturnCounterexample returnError)
      {
        if (returnError.FailingEnsures.ErrorMessage == null || Options.ForceBplErrors)
        {
          errorInfo = ErrorInformationFactory.CreateErrorInformation(returnError.FailingReturn.tok,
            returnError.FailingReturn.Description.FailureDescription,
            returnError.RequestId, returnError.OriginalRequestId, cause);
          errorInfo.Kind = ErrorKind.Postcondition;
          errorInfo.AddAuxInfo(returnError.FailingEnsures.tok,
            returnError.FailingEnsures.ErrorData as string ?? returnError.FailingEnsures.Description.FailureDescription,
            "Related location");
        }
        else
        {
          errorInfo = ExecutionEngine.ErrorInformationFactory.CreateErrorInformation(null,
            returnError.FailingEnsures.ErrorMessage,
            returnError.RequestId, returnError.OriginalRequestId);
        }
      }
      else // error is AssertCounterexample
      {
        Debug.Assert(error is AssertCounterexample);
        var assertError = (AssertCounterexample)error;
        var failingAssert = assertError.FailingAssert;
        if (failingAssert is LoopInitAssertCmd or LoopInvMaintainedAssertCmd)
        {
          errorInfo = ErrorInformationFactory.CreateErrorInformation(failingAssert.tok,
            failingAssert.Description.FailureDescription,
            assertError.RequestId, assertError.OriginalRequestId, cause);
          errorInfo.Kind = failingAssert is LoopInitAssertCmd ?
            ErrorKind.InvariantEntry : ErrorKind.InvariantMaintainance;
          string relatedMessage = null;
          if (failingAssert.ErrorData is string)
          {
            relatedMessage = failingAssert.ErrorData as string;
          }
          else if (failingAssert is LoopInitAssertCmd initCmd)
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
          if (failingAssert.ErrorMessage == null || Options.ForceBplErrors)
          {
            string msg = failingAssert.ErrorData as string ??
                         failingAssert.Description.FailureDescription;
            errorInfo = ErrorInformationFactory.CreateErrorInformation(failingAssert.tok, msg,
              assertError.RequestId, assertError.OriginalRequestId, cause);
            errorInfo.Kind = ErrorKind.Assertion;
          }
          else
          {
            errorInfo = ExecutionEngine.ErrorInformationFactory.CreateErrorInformation(null,
              failingAssert.ErrorMessage, assertError.RequestId, assertError.OriginalRequestId);
          }
        }
      }

      return errorInfo;
    }

    private static void WriteErrorInformationToXmlSink(XmlSink sink, ErrorInformation errorInfo, List<Block> trace)
    {
      var msg = "assertion violation";
      switch (errorInfo.Kind)
      {
        case ErrorKind.Precondition:
          msg = "precondition violation";
          break;

        case ErrorKind.Postcondition:
          msg = "postcondition violation";
          break;

        case ErrorKind.InvariantEntry:
          msg = "loop invariant entry violation";
          break;

        case ErrorKind.InvariantMaintainance:
          msg = "loop invariant maintenance violation";
          break;
      }

      var relatedError = errorInfo.Aux.FirstOrDefault();
      sink.WriteError(msg, errorInfo.Tok, relatedError.Tok, trace);
    }

    public void Dispose()
    {
      checkerPool.Dispose();
    }
  }
}
