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

namespace Microsoft.Boogie
{
  #region Output printing

  public interface OutputPrinter
  {
    void ErrorWriteLine(TextWriter tw, string s);
    void ErrorWriteLine(TextWriter tw, string format, params object[] args);
    void AdvisoryWriteLine(string format, params object[] args);
    void Inform(string s, TextWriter tw);
    void WriteTrailer(PipelineStatistics stats);
    void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true);
    void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null);
  }


  public class ConsolePrinter : OutputPrinter
  {
    public void ErrorWriteLine(TextWriter tw, string s)
    {
      Contract.Requires(s != null);
      if (!s.Contains("Error: ") && !s.Contains("Error BP"))
      {
        tw.WriteLine(s);
        return;
      }

      // split the string up into its first line and the remaining lines
      string remaining = null;
      int i = s.IndexOf('\r');
      if (i >= 0)
      {
        remaining = s.Substring(i + 1);
        if (remaining.StartsWith("\n"))
        {
          remaining = remaining.Substring(1);
        }

        s = s.Substring(0, i);
      }

      ConsoleColor col = Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Red;
      tw.WriteLine(s);
      Console.ForegroundColor = col;

      if (remaining != null)
      {
        tw.WriteLine(remaining);
      }
    }


    public void ErrorWriteLine(TextWriter tw, string format, params object[] args)
    {
      Contract.Requires(format != null);
      string s = string.Format(format, args);
      ErrorWriteLine(tw, s);
    }


    public void AdvisoryWriteLine(string format, params object[] args)
    {
      Contract.Requires(format != null);
      ConsoleColor col = Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Yellow;
      Console.WriteLine(format, args);
      Console.ForegroundColor = col;
    }


    /// <summary>
    /// Inform the user about something and proceed with translation normally.
    /// Print newline after the message.
    /// </summary>
    public void Inform(string s, TextWriter tw)
    {
      if (CommandLineOptions.Clo.Trace || CommandLineOptions.Clo.TraceProofObligations)
      {
        tw.WriteLine(s);
      }
    }


    public void WriteTrailer(PipelineStatistics stats)
    {
      Contract.Requires(stats != null);
      Contract.Requires(0 <= stats.VerifiedCount && 0 <= stats.ErrorCount && 0 <= stats.InconclusiveCount &&
                        0 <= stats.TimeoutCount && 0 <= stats.OutOfMemoryCount);

      Console.WriteLine();
      if (CommandLineOptions.Clo.ShowVerifiedProcedureCount)
      {
        Console.Write("{0} finished with {1} verified, {2} error{3}", CommandLineOptions.Clo.DescriptiveToolName,
          stats.VerifiedCount, stats.ErrorCount, stats.ErrorCount == 1 ? "" : "s");
      }
      else
      {
        Console.Write("{0} finished with {1} error{2}", CommandLineOptions.Clo.DescriptiveToolName, stats.ErrorCount,
          stats.ErrorCount == 1 ? "" : "s");
      }

      if (stats.InconclusiveCount != 0)
      {
        Console.Write(", {0} inconclusive{1}", stats.InconclusiveCount, stats.InconclusiveCount == 1 ? "" : "s");
      }

      if (stats.TimeoutCount != 0)
      {
        Console.Write(", {0} time out{1}", stats.TimeoutCount, stats.TimeoutCount == 1 ? "" : "s");
      }

      if (stats.OutOfMemoryCount != 0)
      {
        Console.Write(", {0} out of memory", stats.OutOfMemoryCount);
      }

      if (stats.OutOfResourceCount != 0)
      {
        Console.Write(", {0} out of resource", stats.OutOfResourceCount);
      }

      Console.WriteLine();
      Console.Out.Flush();
    }


    public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true)
    {
      Contract.Requires(errorInfo != null);

      ReportBplError(errorInfo.Tok, errorInfo.FullMsg, true, tw);

      foreach (var e in errorInfo.Aux)
      {
        if (!(skipExecutionTrace && e.Category != null && e.Category.Contains("Execution trace")))
        {
          ReportBplError(e.Tok, e.FullMsg, false, tw);
        }
      }

      tw.Write(errorInfo.Out.ToString());
      tw.Write(errorInfo.Model.ToString());
      tw.Flush();
    }


    public virtual void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
    {
      Contract.Requires(message != null);

      if (category != null)
      {
        message = string.Format("{0}: {1}", category, message);
      }

      string s;
      if (tok != null)
      {
        s = string.Format("{0}({1},{2}): {3}", ExecutionEngine.GetFileNameForConsole(tok.filename), tok.line, tok.col,
          message);
      }
      else
      {
        s = message;
      }

      if (error)
      {
        ErrorWriteLine(tw, s);
      }
      else
      {
        tw.WriteLine(s);
      }
    }
  }

  #endregion


  public enum PipelineOutcome
  {
    Done,
    ResolutionError,
    TypeCheckingError,
    ResolvedAndTypeChecked,
    FatalError,
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
    public long[] CachingActionCounts;
    public int CachedErrorCount;
    public int CachedVerifiedCount;
    public int CachedInconclusiveCount;
    public int CachedTimeoutCount;
    public int CachedOutOfResourceCount;
    public int CachedOutOfMemoryCount;
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
    public TextWriter Model = new StringWriter();

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


  public sealed class VerificationResult
  {
    public readonly string RequestId;
    public readonly string Checksum;
    public readonly string DependeciesChecksum;
    public readonly string ImplementationName;
    public readonly IToken ImplementationToken;
    public readonly string ProgramId;

    public DateTime Start { get; set; }
    public DateTime End { get; set; }

    public int ProofObligationCount
    {
      get { return ProofObligationCountAfter - ProofObligationCountBefore; }
    }

    public int ProofObligationCountBefore { get; set; }
    public int ProofObligationCountAfter { get; set; }

    public ConditionGeneration.Outcome Outcome { get; set; }
    public List<Counterexample> Errors;

    public ISet<byte[]> AssertionChecksums { get; private set; }

    public VerificationResult(string requestId, Implementation implementation, string programId = null)
    {
      Checksum = implementation.Checksum;
      DependeciesChecksum = implementation.DependencyChecksum;
      RequestId = requestId;
      ImplementationName = implementation.Name;
      ImplementationToken = implementation.tok;
      ProgramId = programId;
      AssertionChecksums = implementation.AssertionChecksums;
    }
  }
  
  public class ExecutionEngine
  {
    public static OutputPrinter printer;

    public static ErrorInformationFactory errorInformationFactory = new ErrorInformationFactory();

    static int autoRequestIdCount;

    static readonly string AutoRequestIdPrefix = "auto_request_id_";

    public static string FreshRequestId()
    {
      var id = Interlocked.Increment(ref autoRequestIdCount);
      return AutoRequestIdPrefix + id;
    }

    public static int AutoRequestId(string id)
    {
      if (id.StartsWith(AutoRequestIdPrefix))
      {
        int result;
        if (int.TryParse(id.Substring(AutoRequestIdPrefix.Length), out result))
        {
          return result;
        }
      }

      return -1;
    }

    public readonly static VerificationResultCache Cache = new VerificationResultCache();

    static readonly MemoryCache programCache = new MemoryCache("ProgramCache");

    static readonly CacheItemPolicy policy = new CacheItemPolicy
      {SlidingExpiration = new TimeSpan(0, 10, 0), Priority = CacheItemPriority.Default};

    public static Program CachedProgram(string programId)
    {
      var result = programCache.Get(programId) as Program;
      return result;
    }

    static List<Checker> Checkers = new List<Checker>();

    static DateTime FirstRequestStart;

    static readonly ConcurrentDictionary<string, TimeSpan>
      TimePerRequest = new ConcurrentDictionary<string, TimeSpan>();

    static readonly ConcurrentDictionary<string, PipelineStatistics> StatisticsPerRequest =
      new ConcurrentDictionary<string, PipelineStatistics>();

    static readonly ConcurrentDictionary<string, CancellationTokenSource> ImplIdToCancellationTokenSource =
      new ConcurrentDictionary<string, CancellationTokenSource>();

    static readonly ConcurrentDictionary<string, CancellationTokenSource> RequestIdToCancellationTokenSource =
      new ConcurrentDictionary<string, CancellationTokenSource>();

    static ThreadTaskScheduler Scheduler = new ThreadTaskScheduler(16 * 1024 * 1024);

    static TextWriter ModelWriter = null;

    public static void ProcessFiles(IList<string> fileNames, bool lookForSnapshots = true, string programId = null)
    {
      Contract.Requires(cce.NonNullElements(fileNames));

      if (programId == null)
      {
        programId = "main_program_id";
      }

      if (CommandLineOptions.Clo.VerifySeparately && 1 < fileNames.Count)
      {
        foreach (var f in fileNames)
        {
          ProcessFiles(new List<string> {f}, lookForSnapshots, f);
        }

        return;
      }

      if (0 <= CommandLineOptions.Clo.VerifySnapshots && lookForSnapshots)
      {
        var snapshotsByVersion = LookForSnapshots(fileNames);
        foreach (var s in snapshotsByVersion)
        {
          ProcessFiles(new List<string>(s), false, programId);
        }

        return;
      }

      using (XmlFileScope xf = new XmlFileScope(CommandLineOptions.Clo.XmlSink, fileNames[fileNames.Count - 1]))
      {
        Program program = ParseBoogieProgram(fileNames, false);
        if (program == null)
          return;
        if (CommandLineOptions.Clo.PrintFile != null)
        {
          PrintBplFile(CommandLineOptions.Clo.PrintFile, program, false, true, CommandLineOptions.Clo.PrettyPrint);
        }

        CivlTypeChecker civlTypeChecker;
        PipelineOutcome oc = ResolveAndTypecheck(program, fileNames[fileNames.Count - 1], out civlTypeChecker);
        if (oc != PipelineOutcome.ResolvedAndTypeChecked)
          return;

        if (CommandLineOptions.Clo.PrintCFGPrefix != null)
        {
          foreach (var impl in program.Implementations)
          {
            using (StreamWriter sw = new StreamWriter(CommandLineOptions.Clo.PrintCFGPrefix + "." + impl.Name + ".dot"))
            {
              sw.Write(program.ProcessLoops(impl).ToDot());
            }
          }
        }

        CivlVCGeneration.Transform(civlTypeChecker);
        if (CommandLineOptions.Clo.CivlDesugaredFile != null)
        {
          int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
          CommandLineOptions.Clo.PrintUnstructured = 1;
          PrintBplFile(CommandLineOptions.Clo.CivlDesugaredFile, program, false, false,
            CommandLineOptions.Clo.PrettyPrint);
          CommandLineOptions.Clo.PrintUnstructured = oldPrintUnstructured;
        }
        
        EliminateDeadVariables(program);

        CoalesceBlocks(program);

        Inline(program);

        var stats = new PipelineStatistics();
        oc = InferAndVerify(program, stats, 1 < CommandLineOptions.Clo.VerifySnapshots ? programId : null);
        switch (oc)
        {
          case PipelineOutcome.Done:
          case PipelineOutcome.VerificationCompleted:
            printer.WriteTrailer(stats);
            break;
          default:
            break;
        }
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


    public static void CoalesceBlocks(Program program)
    {
      if (CommandLineOptions.Clo.CoalesceBlocks)
      {
        if (CommandLineOptions.Clo.Trace)
          Console.WriteLine("Coalescing blocks...");
        Microsoft.Boogie.BlockCoalescer.CoalesceBlocks(program);
      }
    }


    public static void CollectModSets(Program program)
    {
      if (CommandLineOptions.Clo.DoModSetAnalysis)
      {
        new ModSetCollector().DoModSetAnalysis(program);
      }
    }


    public static void EliminateDeadVariables(Program program)
    {
      Microsoft.Boogie.UnusedVarEliminator.Eliminate(program);
    }


    public static void PrintBplFile(string filename, Program program, bool allowPrintDesugaring, bool setTokens = true,
      bool pretty = false)
    {
      Contract.Requires(program != null);
      Contract.Requires(filename != null);
      bool oldPrintDesugaring = CommandLineOptions.Clo.PrintDesugarings;
      if (!allowPrintDesugaring)
      {
        CommandLineOptions.Clo.PrintDesugarings = false;
      }

      using (TokenTextWriter writer = filename == "-"
        ? new TokenTextWriter("<console>", Console.Out, setTokens, pretty)
        : new TokenTextWriter(filename, setTokens, pretty))
      {
        if (CommandLineOptions.Clo.ShowEnv != CommandLineOptions.ShowEnvironment.Never)
        {
          writer.WriteLine("// " + CommandLineOptions.Clo.Version);
          writer.WriteLine("// " + CommandLineOptions.Clo.Environment);
        }

        writer.WriteLine();
        program.Emit(writer);
      }

      CommandLineOptions.Clo.PrintDesugarings = oldPrintDesugaring;
    }


    /// <summary>
    /// Parse the given files into one Boogie program.  If an I/O or parse error occurs, an error will be printed
    /// and null will be returned.  On success, a non-null program is returned.
    /// </summary>
    public static Program ParseBoogieProgram(IList<string> fileNames, bool suppressTraceOutput)
    {
      Contract.Requires(cce.NonNullElements(fileNames));

      Program program = new Program();
      bool okay = true;
      
      for (int fileId = 0; fileId < fileNames.Count; fileId++)
      {
        string bplFileName = fileNames[fileId];
        if (!suppressTraceOutput)
        {
          if (CommandLineOptions.Clo.XmlSink != null)
          {
            CommandLineOptions.Clo.XmlSink.WriteFileFragment(bplFileName);
          }

          if (CommandLineOptions.Clo.Trace)
          {
            Console.WriteLine("Parsing " + GetFileNameForConsole(bplFileName));
          }
        }

        try
        {
          var defines = new List<string>() {"FILE_" + fileId};
          int errorCount = Parser.Parse(bplFileName, defines, out Program programSnippet,
            CommandLineOptions.Clo.UseBaseNameForFileName);
          if (programSnippet == null || errorCount != 0)
          {
            Console.WriteLine("{0} parse errors detected in {1}", errorCount, GetFileNameForConsole(bplFileName));
            okay = false;
          }
          else
          {
            program.AddTopLevelDeclarations(programSnippet.TopLevelDeclarations);
          }
        }
        catch (IOException e)
        {
          printer.ErrorWriteLine(Console.Out, "Error opening file \"{0}\": {1}", GetFileNameForConsole(bplFileName),
            e.Message);
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
          CommandLineOptions.Clo.UseLibrary = true;
          CommandLineOptions.Clo.UseArrayTheory = true;
          CommandLineOptions.Clo.Monomorphize = true;
        }

        if (CommandLineOptions.Clo.UseLibrary)
        {
          var library = Parser.ParseLibraryDefinitions();
          program.AddTopLevelDeclarations(library.TopLevelDeclarations);
        }

        return program;
      }
    }

    internal static string GetFileNameForConsole(string filename)
    {
      return (CommandLineOptions.Clo.UseBaseNameForFileName && !string.IsNullOrEmpty(filename) &&
              filename != "<console>")
        ? System.IO.Path.GetFileName(filename)
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
    public static PipelineOutcome ResolveAndTypecheck(Program program, string bplFileName,
      out CivlTypeChecker civlTypeChecker)
    {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);

      civlTypeChecker = null;

      // ---------- Resolve ------------------------------------------------------------

      if (CommandLineOptions.Clo.NoResolve)
      {
        return PipelineOutcome.Done;
      }

      int errorCount = program.Resolve();
      if (errorCount != 0)
      {
        Console.WriteLine("{0} name resolution errors detected in {1}", errorCount, GetFileNameForConsole(bplFileName));
        return PipelineOutcome.ResolutionError;
      }

      // ---------- Type check ------------------------------------------------------------

      if (CommandLineOptions.Clo.NoTypecheck)
      {
        return PipelineOutcome.Done;
      }

      errorCount = program.Typecheck();
      if (errorCount != 0)
      {
        Console.WriteLine("{0} type checking errors detected in {1}", errorCount, GetFileNameForConsole(bplFileName));
        return PipelineOutcome.TypeCheckingError;
      }

      if (PolymorphismChecker.IsMonomorphic(program))
      {
        CommandLineOptions.Clo.TypeEncodingMethod = CommandLineOptions.TypeEncoding.Monomorphic;
      }
      else if (CommandLineOptions.Clo.Monomorphize)
      {
        if (Monomorphizer.Monomorphize(program))
        {
          CommandLineOptions.Clo.TypeEncodingMethod = CommandLineOptions.TypeEncoding.Monomorphic;
        }
        else
        {
          Console.WriteLine("Unable to monomorphize input program");
          return PipelineOutcome.FatalError;
        }
      }
      else if (CommandLineOptions.Clo.UseArrayTheory)
      {
        Console.WriteLine(
          "Option /useArrayTheory only supported for monomorphic programs and polymorphism is detected in input program");
        return PipelineOutcome.FatalError;
      }

      CollectModSets(program);

      civlTypeChecker = new CivlTypeChecker(program);
      civlTypeChecker.TypeCheck();
      if (civlTypeChecker.checkingContext.ErrorCount != 0)
      {
        Console.WriteLine("{0} type checking errors detected in {1}", civlTypeChecker.checkingContext.ErrorCount,
          GetFileNameForConsole(bplFileName));
        return PipelineOutcome.TypeCheckingError;
      }

      if (CommandLineOptions.Clo.PrintFile != null && CommandLineOptions.Clo.PrintDesugarings)
      {
        // if PrintDesugaring option is engaged, print the file here, after resolution and type checking
        PrintBplFile(CommandLineOptions.Clo.PrintFile, program, true, true, CommandLineOptions.Clo.PrettyPrint);
      }

      return PipelineOutcome.ResolvedAndTypeChecked;
    }


    public static void Inline(Program program)
    {
      Contract.Requires(program != null);

      if (CommandLineOptions.Clo.Trace)
        Console.WriteLine("Inlining...");

      // Inline
      var TopLevelDeclarations = cce.NonNull(program.TopLevelDeclarations);

      if (CommandLineOptions.Clo.ProcedureInlining != CommandLineOptions.Inlining.None)
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
            if (CommandLineOptions.Clo.UserWantsToCheckRoutine(impl.Name) && !impl.SkipVerification)
            {
              Inliner.ProcessImplementation(program, impl);
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


    /// <summary>
    /// Given a resolved and type checked Boogie program, infers invariants for the program
    /// and then attempts to verify it.  Returns:
    ///  - Done if command line specified no verification
    ///  - FatalError if a fatal error occurred, in which case an error has been printed to console
    ///  - VerificationCompleted if inference and verification completed, in which the out
    ///    parameters contain meaningful values
    /// </summary>
    public static PipelineOutcome InferAndVerify(Program program,
      PipelineStatistics stats,
      string programId = null,
      ErrorReporterDelegate er = null, string requestId = null)
    {
      Contract.Requires(program != null);
      Contract.Requires(stats != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out stats.InconclusiveCount) &&
                       0 <= Contract.ValueAtReturn(out stats.TimeoutCount));

      if (requestId == null)
      {
        requestId = FreshRequestId();
      }

      if (CommandLineOptions.Clo.PrintErrorModelFile != null)
      {
        ExecutionEngine.ModelWriter = new StreamWriter(CommandLineOptions.Clo.PrintErrorModelFile, false);
      }

      var start = DateTime.UtcNow;

      #region Do some pre-abstract-interpretation preprocessing on the program

      // Doing lambda expansion before abstract interpretation means that the abstract interpreter
      // never needs to see any lambda expressions.  (On the other hand, if it were useful for it
      // to see lambdas, then it would be better to more lambda expansion until after inference.)
      if (CommandLineOptions.Clo.ExpandLambdas)
      {
        LambdaHelper.ExpandLambdas(program);
        if (CommandLineOptions.Clo.PrintFile != null && CommandLineOptions.Clo.PrintLambdaLifting)
        {
          PrintBplFile(CommandLineOptions.Clo.PrintFile, program, false, true, CommandLineOptions.Clo.PrettyPrint);
        }
      }

      #endregion

      #region Infer invariants using Abstract Interpretation

      if (CommandLineOptions.Clo.UseAbstractInterpretation)
      {
        Microsoft.Boogie.AbstractInterpretation.NativeAbstractInterpretation.RunAbstractInterpretation(program);
      }

      #endregion

      #region Do some post-abstract-interpretation preprocessing on the program (e.g., loop unrolling)

      if (CommandLineOptions.Clo.LoopUnrollCount != -1)
      {
        program.UnrollLoops(CommandLineOptions.Clo.LoopUnrollCount, CommandLineOptions.Clo.SoundLoopUnrolling);
      }

      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo = null;
      if (CommandLineOptions.Clo.ExtractLoops)
      {
        extractLoopMappingInfo = program.ExtractLoops();
      }

      if (CommandLineOptions.Clo.PrintInstrumented)
      {
        program.Emit(new TokenTextWriter(Console.Out, CommandLineOptions.Clo.PrettyPrint));
      }

      #endregion

      if (!CommandLineOptions.Clo.Verify)
      {
        return PipelineOutcome.Done;
      }

      #region Run Houdini and verify

      if (CommandLineOptions.Clo.ContractInfer)
      {
        return RunHoudini(program, stats, er);
      }

      #endregion

      #region Select and prioritize implementations that should be verified

      var impls = program.Implementations.Where(
        impl => impl != null && CommandLineOptions.Clo.UserWantsToCheckRoutine(cce.NonNull(impl.Name)) &&
                !impl.SkipVerification);

      // operate on a stable copy, in case it gets updated while we're running
      Implementation[] stablePrioritizedImpls = null;
      if (0 < CommandLineOptions.Clo.VerifySnapshots)
      {
        OtherDefinitionAxiomsCollector.Collect(program.Axioms);
        DependencyCollector.Collect(program);
        stablePrioritizedImpls = impls.OrderByDescending(
          impl => impl.Priority != 1 ? impl.Priority : Cache.VerificationPriority(impl)).ToArray();
      }
      else
      {
        stablePrioritizedImpls = impls.OrderByDescending(impl => impl.Priority).ToArray();
      }

      #endregion

      if (1 < CommandLineOptions.Clo.VerifySnapshots)
      {
        CachedVerificationResultInjector.Inject(program, stablePrioritizedImpls, requestId, programId,
          out stats.CachingActionCounts);
      }

      #region Verify each implementation

      var outputCollector = new OutputCollector(stablePrioritizedImpls);
      var outcome = PipelineOutcome.VerificationCompleted;

      try
      {
        var cts = new CancellationTokenSource();
        RequestIdToCancellationTokenSource.AddOrUpdate(requestId, cts, (k, ov) => cts);

        var tasks = new Task[stablePrioritizedImpls.Length];
        // We use this semaphore to limit the number of tasks that are currently executing.
        var semaphore = new SemaphoreSlim(CommandLineOptions.Clo.VcsCores);

        // Create a task per implementation.
        for (int i = 0; i < stablePrioritizedImpls.Length; i++)
        {
          var taskIndex = i;
          var id = stablePrioritizedImpls[taskIndex].Id;

          CancellationTokenSource old;
          if (ImplIdToCancellationTokenSource.TryGetValue(id, out old))
          {
            old.Cancel();
          }

          ImplIdToCancellationTokenSource.AddOrUpdate(id, cts, (k, ov) => cts);

          var t = new Task((dummy) =>
          {
            try
            {
              if (outcome == PipelineOutcome.FatalError)
              {
                return;
              }

              if (cts.Token.IsCancellationRequested)
              {
                cts.Token.ThrowIfCancellationRequested();
              }

              VerifyImplementation(program, stats, er, requestId, extractLoopMappingInfo, stablePrioritizedImpls,
                taskIndex, outputCollector, Checkers, programId);
              ImplIdToCancellationTokenSource.TryRemove(id, out old);
            }
            finally
            {
              semaphore.Release();
            }
          }, cts.Token, TaskCreationOptions.None);
          tasks[taskIndex] = t;
        }

        // Execute the tasks.
        int j = 0;
        for (; j < stablePrioritizedImpls.Length && outcome != PipelineOutcome.FatalError; j++)
        {
          try
          {
            semaphore.Wait(cts.Token);
          }
          catch (OperationCanceledException)
          {
            break;
          }

          tasks[j].Start(Scheduler);
        }

        // Don't wait for tasks that haven't been started yet.
        tasks = tasks.Take(j).ToArray();
        Task.WaitAll(tasks);
      }
      catch (AggregateException ae)
      {
        ae.Handle(e =>
        {
          if (e is ProverException)
          {
            printer.ErrorWriteLine(Console.Out, "Fatal Error: ProverException: {0}", e.Message);
            outcome = PipelineOutcome.FatalError;
            return true;
          }

          if (e is OperationCanceledException)
          {
            return true;
          }

          return false;
        });
      }
      finally
      {
        CleanupCheckers(requestId);
      }

      if (CommandLineOptions.Clo.PrintNecessaryAssumes && program.NecessaryAssumes.Any())
      {
        Console.WriteLine("Necessary assume command(s): {0}", string.Join(", ", program.NecessaryAssumes));
      }

      cce.NonNull(CommandLineOptions.Clo.TheProverFactory).Close();

      outputCollector.WriteMoreOutput();

      if (1 < CommandLineOptions.Clo.VerifySnapshots && programId != null)
      {
        program.FreezeTopLevelDeclarations();
        programCache.Set(programId, program, policy);
      }

      if (0 <= CommandLineOptions.Clo.VerifySnapshots && CommandLineOptions.Clo.TraceCachingForBenchmarking)
      {
        var end = DateTime.UtcNow;
        if (TimePerRequest.Count == 0)
        {
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
        foreach (var kv in TimePerRequest.OrderBy(kv => ExecutionEngine.AutoRequestId(kv.Key)))
        {
          var s = StatisticsPerRequest[kv.Key];
          var cacs = s.CachingActionCounts;
          var c = cacs != null ? ", " + cacs.Select(ac => string.Format("{0,3}", ac)).Concat(", ") : "";
          var t = printTimes ? string.Format(", {0,8:F0}", kv.Value.TotalMilliseconds) : "";
          Console.Out.WriteLine(
            "{0,-19}{1}, {2,2}, {3,2}, {4,2}, {5,2}, {6,2}, {7,2}, {8,2}, {9,2}, {10,2}, {11,2}{12}", kv.Key, t,
            s.ErrorCount, s.CachedErrorCount, s.InconclusiveCount, s.CachedInconclusiveCount, s.OutOfMemoryCount,
            s.CachedOutOfMemoryCount, s.TimeoutCount, s.CachedTimeoutCount, s.VerifiedCount, s.CachedVerifiedCount, c);
        }

        if (printTimes)
        {
          Console.Out.WriteLine();
          Console.Out.WriteLine("Total time (ms) since first request: {0:F0}",
            end.Subtract(FirstRequestStart).TotalMilliseconds);
        }
      }

      #endregion

      if (SecureVCGen.outfile != null)
        SecureVCGen.outfile.Close();

      return outcome;
    }

    public static void CancelRequest(string requestId)
    {
      Contract.Requires(requestId != null);

      CancellationTokenSource cts;
      if (RequestIdToCancellationTokenSource.TryGetValue(requestId, out cts))
      {
        cts.Cancel();

        CleanupCheckers(requestId);
      }
    }


    private static void CleanupCheckers(string requestId)
    {
      if (requestId != null)
      {
        CancellationTokenSource old;
        RequestIdToCancellationTokenSource.TryRemove(requestId, out old);
      }

      lock (RequestIdToCancellationTokenSource)
      {
        if (RequestIdToCancellationTokenSource.IsEmpty)
        {
          lock (Checkers)
          {
            foreach (Checker checker in Checkers)
            {
              Contract.Assert(checker != null);
              checker.Close();
            }
          }
        }
      }
    }


    private static void VerifyImplementation(Program program, PipelineStatistics stats, ErrorReporterDelegate er,
      string requestId, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo,
      Implementation[] stablePrioritizedImpls, int index, OutputCollector outputCollector, List<Checker> checkers,
      string programId)
    {
      Implementation impl = stablePrioritizedImpls[index];
      VerificationResult verificationResult = null;
      var output = new StringWriter();

      printer.Inform("", output); // newline
      printer.Inform(string.Format("Verifying {0} ...", impl.Name), output);

      int priority = 0;
      var wasCached = false;
      if (0 < CommandLineOptions.Clo.VerifySnapshots)
      {
        var cachedResults = Cache.Lookup(impl, out priority);
        if (cachedResults != null && priority == Priority.SKIP)
        {
          if (CommandLineOptions.Clo.XmlSink != null)
          {
            CommandLineOptions.Clo.XmlSink.WriteStartMethod(impl.Name, cachedResults.Start);
          }

          printer.Inform(string.Format("Retrieving cached verification result for implementation {0}...", impl.Name),
            output);
          if (CommandLineOptions.Clo.VerifySnapshots < 3 ||
              cachedResults.Outcome == ConditionGeneration.Outcome.Correct)
          {
            verificationResult = cachedResults;
            wasCached = true;
          }
        }
      }

      if (!wasCached)
      {
        #region Verify the implementation

        verificationResult = new VerificationResult(requestId, impl, programId);

        using (var vcgen = CreateVCGen(program, checkers))
        {
          vcgen.CachingActionCounts = stats.CachingActionCounts;
          verificationResult.ProofObligationCountBefore = vcgen.CumulativeAssertionCount;
          verificationResult.Start = DateTime.UtcNow;

          if (CommandLineOptions.Clo.XmlSink != null)
          {
            CommandLineOptions.Clo.XmlSink.WriteStartMethod(impl.Name, verificationResult.Start);
          }

          try
          {
            verificationResult.Outcome = vcgen.VerifyImplementation(impl, out verificationResult.Errors, requestId);
            if (CommandLineOptions.Clo.ExtractLoops && verificationResult.Errors != null)
            {
              var vcg = vcgen as VCGen;
              if (vcg != null)
              {
                for (int i = 0; i < verificationResult.Errors.Count; i++)
                {
                  verificationResult.Errors[i] = vcg.extractLoopTrace(verificationResult.Errors[i], impl.Name,
                    program, extractLoopMappingInfo);
                }
              }
            }            
          }
          catch (VCGenException e)
          {
            var errorInfo = errorInformationFactory.CreateErrorInformation(impl.tok,
              String.Format("{0} (encountered in implementation {1}).", e.Message, impl.Name), requestId, "Error");
            errorInfo.ImplementationName = impl.Name;
            printer.WriteErrorInformation(errorInfo, output);
            if (er != null)
            {
              lock (er)
              {
                er(errorInfo);
              }
            }

            verificationResult.Errors = null;
            verificationResult.Outcome = VCGen.Outcome.Inconclusive;
          }
          catch (UnexpectedProverOutputException upo)
          {
            printer.AdvisoryWriteLine("Advisory: {0} SKIPPED because of internal error: unexpected prover output: {1}",
              impl.Name, upo.Message);
            verificationResult.Errors = null;
            verificationResult.Outcome = VCGen.Outcome.Inconclusive;
          }

          verificationResult.ProofObligationCountAfter = vcgen.CumulativeAssertionCount;
          verificationResult.End = DateTime.UtcNow;
        }

        #endregion

        #region Cache the verification result

        if (0 < CommandLineOptions.Clo.VerifySnapshots && !string.IsNullOrEmpty(impl.Checksum))
        {
          Cache.Insert(impl, verificationResult);
        }

        #endregion
      }

      #region Process the verification results and statistics

      ProcessOutcome(verificationResult.Outcome, verificationResult.Errors, TimeIndication(verificationResult), stats,
        output, impl.TimeLimit, er, verificationResult.ImplementationName, verificationResult.ImplementationToken,
        verificationResult.RequestId, wasCached);

      ProcessErrors(verificationResult.Errors, verificationResult.Outcome, output, er, impl);

      if (CommandLineOptions.Clo.XmlSink != null)
      {
        CommandLineOptions.Clo.XmlSink.WriteEndMethod(verificationResult.Outcome.ToString().ToLowerInvariant(),
          verificationResult.End, verificationResult.End - verificationResult.Start);
      }

      outputCollector.Add(index, output);

      outputCollector.WriteMoreOutput();

      if (verificationResult.Outcome == VCGen.Outcome.Errors || CommandLineOptions.Clo.Trace)
      {
        Console.Out.Flush();
      }

      #endregion
    }


    class OutputCollector
    {
      StringWriter[] outputs;

      int nextPrintableIndex = 0;

      public OutputCollector(Implementation[] implementations)
      {
        outputs = new StringWriter[implementations.Length];
      }

      public void WriteMoreOutput()
      {
        lock (outputs)
        {
          for (; nextPrintableIndex < outputs.Length && outputs[nextPrintableIndex] != null; nextPrintableIndex++)
          {
            Console.Write(outputs[nextPrintableIndex].ToString());
            outputs[nextPrintableIndex] = null;
            Console.Out.Flush();
          }
        }
      }

      public void Add(int index, StringWriter output)
      {
        Contract.Requires(0 <= index && index < outputs.Length);
        Contract.Requires(output != null);

        lock (this)
        {
          outputs[index] = output;
        }
      }
    }


    private static ConditionGeneration CreateVCGen(Program program, List<Checker> checkers)
    {
      ConditionGeneration vcgen = null;
      if (CommandLineOptions.Clo.FixedPointEngine != null)
      {
        vcgen = new FixedpointVC(program, CommandLineOptions.Clo.ProverLogFilePath,
          CommandLineOptions.Clo.ProverLogFileAppend, checkers);
      }
      else if (CommandLineOptions.Clo.SecureVcGen != null)
      {
        vcgen = new SecureVCGen(program, CommandLineOptions.Clo.ProverLogFilePath,
          CommandLineOptions.Clo.ProverLogFileAppend, checkers);
      }
      else
      {
        vcgen = new VCGen(program, CommandLineOptions.Clo.ProverLogFilePath, CommandLineOptions.Clo.ProverLogFileAppend,
          checkers);
      }

      return vcgen;
    }


    #region Houdini

    private static PipelineOutcome RunHoudini(Program program, PipelineStatistics stats, ErrorReporterDelegate er)
    {
      Contract.Requires(stats != null);
      
      if (CommandLineOptions.Clo.StagedHoudini != null)
      {
        return RunStagedHoudini(program, stats, er);
      }

      Houdini.HoudiniSession.HoudiniStatistics houdiniStats = new Houdini.HoudiniSession.HoudiniStatistics();
      Houdini.Houdini houdini = new Houdini.Houdini(program, houdiniStats);
      Houdini.HoudiniOutcome outcome = houdini.PerformHoudiniInference();
      houdini.Close();

      if (CommandLineOptions.Clo.PrintAssignment)
      {
        Console.WriteLine("Assignment computed by Houdini:");
        foreach (var x in outcome.assignment)
        {
          Console.WriteLine(x.Key + " = " + x.Value);
        }
      }

      if (CommandLineOptions.Clo.Trace)
      {
        int numTrueAssigns = 0;
        foreach (var x in outcome.assignment)
        {
          if (x.Value)
            numTrueAssigns++;
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
        ProcessOutcome(x.outcome, x.errors, "", stats, Console.Out, CommandLineOptions.Clo.TimeLimit, er);
        ProcessErrors(x.errors, x.outcome, Console.Out, er);
      }

      return PipelineOutcome.Done;
    }

    public static Program ProgramFromFile(string filename)
    {
      Program p = ParseBoogieProgram(new List<string> {filename}, false);
      System.Diagnostics.Debug.Assert(p != null);
      CivlTypeChecker civlTypeChecker;
      PipelineOutcome oc = ExecutionEngine.ResolveAndTypecheck(p, filename, out civlTypeChecker);
      System.Diagnostics.Debug.Assert(oc == PipelineOutcome.ResolvedAndTypeChecked);
      return p;
    }

    private static PipelineOutcome RunStagedHoudini(Program program, PipelineStatistics stats, ErrorReporterDelegate er)
    {
      Houdini.HoudiniSession.HoudiniStatistics houdiniStats = new Houdini.HoudiniSession.HoudiniStatistics();
      Houdini.StagedHoudini stagedHoudini = new Houdini.StagedHoudini(program, houdiniStats, ProgramFromFile);
      Houdini.HoudiniOutcome outcome = stagedHoudini.PerformStagedHoudiniInference();

      if (CommandLineOptions.Clo.PrintAssignment)
      {
        Console.WriteLine("Assignment computed by Houdini:");
        foreach (var x in outcome.assignment)
        {
          Console.WriteLine(x.Key + " = " + x.Value);
        }
      }

      if (CommandLineOptions.Clo.Trace)
      {
        int numTrueAssigns = 0;
        foreach (var x in outcome.assignment)
        {
          if (x.Value)
            numTrueAssigns++;
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
        ProcessOutcome(x.outcome, x.errors, "", stats, Console.Out, CommandLineOptions.Clo.TimeLimit, er);
        ProcessErrors(x.errors, x.outcome, Console.Out, er);
      }

      return PipelineOutcome.Done;
    }

    #endregion


    private static string TimeIndication(VerificationResult verificationResult)
    {
      var result = "";
      if (CommandLineOptions.Clo.Trace)
      {
        result = string.Format("  [{0:F3} s, {1} proof obligation{2}]  ",
          (verificationResult.End - verificationResult.Start).TotalSeconds, verificationResult.ProofObligationCount,
          verificationResult.ProofObligationCount == 1 ? "" : "s");
      }
      else if (CommandLineOptions.Clo.TraceProofObligations)
      {
        result = string.Format("  [{0} proof obligation{1}]  ", verificationResult.ProofObligationCount,
          verificationResult.ProofObligationCount == 1 ? "" : "s");
      }

      return result;
    }


    private static void ProcessOutcome(VC.VCGen.Outcome outcome, List<Counterexample> errors, string timeIndication,
      PipelineStatistics stats, TextWriter tw, int timeLimit, ErrorReporterDelegate er = null, string implName = null,
      IToken implTok = null, string requestId = null, bool wasCached = false)
    {
      Contract.Requires(stats != null);

      UpdateStatistics(stats, outcome, errors, wasCached);

      printer.Inform(timeIndication + OutcomeIndication(outcome, errors), tw);

      ReportOutcome(outcome, er, implName, implTok, requestId, tw, timeLimit, errors);
    }


    private static void ReportOutcome(VC.VCGen.Outcome outcome, ErrorReporterDelegate er, string implName,
      IToken implTok, string requestId, TextWriter tw, int timeLimit, List<Counterexample> errors)
    {
      ErrorInformation errorInfo = null;

      switch (outcome)
      {
        case VCGen.Outcome.ReachedBound:
          tw.WriteLine(string.Format("Stratified Inlining: Reached recursion bound of {0}",
            CommandLineOptions.Clo.RecursionBound));
          break;
        case VCGen.Outcome.Errors:
        case VCGen.Outcome.TimedOut:
          if (implName != null && implTok != null)
          {
            if (outcome == ConditionGeneration.Outcome.TimedOut ||
                (errors != null && errors.Any(e => e.IsAuxiliaryCexForDiagnosingTimeouts)))
            {
              errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
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
                errorInfo.Msg += string.Format(" with {0} check(s) that timed out individually",
                  timedOutAssertions.Count);
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
                  msg = callError.FailingCall.ErrorData as string ?? "A precondition for this call might not hold.";
                }
                else if (returnError != null)
                {
                  tok = returnError.FailingReturn.tok;
                  msg = "A postcondition might not hold on this return path.";
                }
                else
                {
                  tok = assertError.FailingAssert.tok;
                  if (assertError.FailingAssert is LoopInitAssertCmd)
                  {
                    msg = "This loop invariant might not hold on entry.";
                  }
                  else if (assertError.FailingAssert is LoopInvMaintainedAssertCmd)
                  {
                    msg = "This loop invariant might not be maintained by the loop.";
                  }
                  else
                  {
                    if (assertError.FailingAssert.ErrorMessage == null || CommandLineOptions.Clo.ForceBplErrors)
                    {
                      msg = assertError.FailingAssert.ErrorData as string;
                    }
                    else
                    {
                      msg = assertError.FailingAssert.ErrorMessage;
                    }
                    if (msg == null)
                    {
                      msg = "This assertion might not hold.";
                    }
                  }
                }

                errorInfo.AddAuxInfo(tok, msg, "Unverified check due to timeout");
              }
            }
          }

          break;
        case VCGen.Outcome.OutOfResource:
          if (implName != null && implTok != null)
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
              "Verification out of resource (" + implName + ")", requestId);
          }

          break;
        case VCGen.Outcome.OutOfMemory:
          if (implName != null && implTok != null)
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
              "Verification out of memory (" + implName + ")", requestId);
          }

          break;
        case VCGen.Outcome.Inconclusive:
          if (implName != null && implTok != null)
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(implTok,
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


    private static void UpdateStatistics(PipelineStatistics stats, VC.VCGen.Outcome outcome,
      List<Counterexample> errors, bool wasCached)
    {
      Contract.Requires(stats != null);

      switch (outcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new cce.UnreachableException();
        case VCGen.Outcome.ReachedBound:
          Interlocked.Increment(ref stats.VerifiedCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedVerifiedCount);
          }

          break;
        case VCGen.Outcome.Correct:
          Interlocked.Increment(ref stats.VerifiedCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedVerifiedCount);
          }

          break;
        case VCGen.Outcome.TimedOut:
          Interlocked.Increment(ref stats.TimeoutCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedTimeoutCount);
          }

          break;
        case VCGen.Outcome.OutOfResource:
          Interlocked.Increment(ref stats.OutOfResourceCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedOutOfResourceCount);
          }

          break;
        case VCGen.Outcome.OutOfMemory:
          Interlocked.Increment(ref stats.OutOfMemoryCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedOutOfMemoryCount);
          }

          break;
        case VCGen.Outcome.Inconclusive:
          Interlocked.Increment(ref stats.InconclusiveCount);
          if (wasCached)
          {
            Interlocked.Increment(ref stats.CachedInconclusiveCount);
          }

          break;
        case VCGen.Outcome.Errors:
          int cnt = errors.Where(e => !e.IsAuxiliaryCexForDiagnosingTimeouts).Count();
          Interlocked.Add(ref stats.ErrorCount, cnt);
          if (wasCached)
          {
            Interlocked.Add(ref stats.CachedErrorCount, cnt);
          }

          break;
      }
    }


    private static void ProcessErrors(List<Counterexample> errors, VC.VCGen.Outcome outcome, TextWriter tw,
      ErrorReporterDelegate er, Implementation impl = null)
    {
      var implName = impl != null ? impl.Name : null;

      if (errors != null)
      {
        errors.Sort(new CounterexampleComparer());
        foreach (Counterexample error in errors)
        {
          if (error.IsAuxiliaryCexForDiagnosingTimeouts)
          {
            continue;
          }

          var errorInfo = CreateErrorInformation(error, outcome);
          errorInfo.ImplementationName = implName;

          if (CommandLineOptions.Clo.XmlSink != null)
          {
            WriteErrorInformationToXmlSink(errorInfo, error.Trace);
          }

          if (CommandLineOptions.Clo.ErrorTrace > 0)
          {
            errorInfo.Out.WriteLine("Execution trace:");
            error.Print(4, errorInfo.Out, b => { errorInfo.AddAuxInfo(b.tok, b.Label, "Execution trace"); });
            if (CommandLineOptions.Clo.EnhancedErrorMessages == 1 && error.AugmentedTrace != null && error.AugmentedTrace.Count > 0)
            {
              errorInfo.Out.WriteLine("Augmented execution trace:");
              foreach (var elem in error.AugmentedTrace)
              {
                if (elem is IdentifierExpr identifierExpr)
                {
                  errorInfo.Out.Write(error.GetModelValue(identifierExpr.Decl));
                }
                else
                {
                  errorInfo.Out.Write(elem);
                }
              }
            }
            if (CommandLineOptions.Clo.PrintErrorModel >= 1 && error.Model != null)
            {
              error.Model.Write(ExecutionEngine.ModelWriter == null ? errorInfo.Out : ExecutionEngine.ModelWriter);
            }
          }

          if (CommandLineOptions.Clo.ModelViewFile != null)
          {
            error.PrintModel(errorInfo.Model, error);
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
    }


    private static ErrorInformation CreateErrorInformation(Counterexample error, VC.VCGen.Outcome outcome)
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
      else if (outcome == VCGen.Outcome.OutOfResource)
      {
        cause = "Out of resource on";
      }

      if (error is CallCounterexample callError)
      {
        if (callError.FailingRequires.ErrorMessage == null || CommandLineOptions.Clo.ForceBplErrors)
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(callError.FailingCall.tok,
            callError.FailingCall.ErrorData as string ?? "A precondition for this call might not hold.",
            callError.RequestId, callError.OriginalRequestId, cause);
          errorInfo.Kind = ErrorKind.Precondition;
          errorInfo.AddAuxInfo(callError.FailingRequires.tok,
            callError.FailingRequires.ErrorData as string ?? "This is the precondition that might not hold.",
            "Related location");
        }
        else
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(null,
            callError.FailingRequires.ErrorMessage,
            callError.RequestId, callError.OriginalRequestId);
        }
      }
      else if (error is ReturnCounterexample returnError)
      {
        if (returnError.FailingEnsures.ErrorMessage == null || CommandLineOptions.Clo.ForceBplErrors)
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(returnError.FailingReturn.tok,
            "A postcondition might not hold on this return path.",
            returnError.RequestId, returnError.OriginalRequestId, cause);
          errorInfo.Kind = ErrorKind.Postcondition;
          errorInfo.AddAuxInfo(returnError.FailingEnsures.tok,
            returnError.FailingEnsures.ErrorData as string ?? "This is the postcondition that might not hold.",
            "Related location");
        }
        else
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(null,
            returnError.FailingEnsures.ErrorMessage,
            returnError.RequestId, returnError.OriginalRequestId);
        }
      }
      else // error is AssertCounterexample
      {
        Debug.Assert(error is AssertCounterexample);
        var assertError = (AssertCounterexample)error;
        if (assertError.FailingAssert is LoopInitAssertCmd)
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(assertError.FailingAssert.tok,
            "This loop invariant might not hold on entry.",
            assertError.RequestId, assertError.OriginalRequestId, cause);
          errorInfo.Kind = ErrorKind.InvariantEntry;
          if ((assertError.FailingAssert.ErrorData as string) != null)
          {
            errorInfo.AddAuxInfo(assertError.FailingAssert.tok, assertError.FailingAssert.ErrorData as string,
              "Related message");
          }
        }
        else if (assertError.FailingAssert is LoopInvMaintainedAssertCmd)
        {
          errorInfo = errorInformationFactory.CreateErrorInformation(assertError.FailingAssert.tok,
            "This loop invariant might not be maintained by the loop.",
            assertError.RequestId, assertError.OriginalRequestId, cause);
          errorInfo.Kind = ErrorKind.InvariantMaintainance;
          if ((assertError.FailingAssert.ErrorData as string) != null)
          {
            errorInfo.AddAuxInfo(assertError.FailingAssert.tok, assertError.FailingAssert.ErrorData as string,
              "Related message");
          }
        }
        else
        {
          if (assertError.FailingAssert.ErrorMessage == null || CommandLineOptions.Clo.ForceBplErrors)
          {
            string msg = assertError.FailingAssert.ErrorData as string ?? "This assertion might not hold.";
            errorInfo = errorInformationFactory.CreateErrorInformation(assertError.FailingAssert.tok, msg,
              assertError.RequestId, assertError.OriginalRequestId, cause);
            errorInfo.Kind = ErrorKind.Assertion;
          }
          else
          {
            errorInfo = errorInformationFactory.CreateErrorInformation(null, 
              assertError.FailingAssert.ErrorMessage,
              assertError.RequestId, assertError.OriginalRequestId);
          }
        }
      }

      return errorInfo;
    }

    private static void WriteErrorInformationToXmlSink(ErrorInformation errorInfo, List<Block> trace)
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
      CommandLineOptions.Clo.XmlSink.WriteError(msg, errorInfo.Tok, relatedError.Tok, trace);
    }
  }
}