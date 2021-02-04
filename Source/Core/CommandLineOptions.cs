using System;
using System.Collections.Generic;
using System.Collections.Specialized;
using System.IO;
using System.Linq;
using System.Diagnostics.Contracts;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie
{
  public class CommandLineOptionEngine
  {
    public readonly string ToolName;
    public readonly string DescriptiveToolName;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(ToolName != null);
      Contract.Invariant(DescriptiveToolName != null);
      Contract.Invariant(this._environment != null);
      Contract.Invariant(cce.NonNullElements(this._files));
      Contract.Invariant(this._fileTimestamp != null);
    }

    private string /*!*/
      _environment = "";

    public string Environment
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._environment;
      }
      set
      {
        Contract.Requires(value != null);
        this._environment = value;
      }
    }

    private readonly List<string /*!*/> /*!*/
      _files = new List<string /*!*/>();

    public IList<string /*!*/> /*!*/ Files
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IList<string>>()));
        Contract.Ensures(Contract.Result<IList<string>>().IsReadOnly);
        return this._files.AsReadOnly();
      }
    }

    public bool VersionRequested = false;
    public bool HelpRequested = false;
    public bool AttributeHelpRequested = false;

    public CommandLineOptionEngine(string toolName, string descriptiveName)
    {
      Contract.Requires(toolName != null);
      Contract.Requires(descriptiveName != null);
      ToolName = toolName;
      DescriptiveToolName = descriptiveName;
    }

    public virtual string /*!*/ VersionNumber
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return cce.NonNull(cce
          .NonNull(System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly()
            .Location)).FileVersion);
      }
    }

    public virtual string /*!*/ VersionSuffix
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return " version " + VersionNumber + ", Copyright (c) 2003-2014, Microsoft.";
      }
    }

    public virtual string /*!*/ Version
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return DescriptiveToolName + VersionSuffix;
      }
    }

    private string /*!*/
      _fileTimestamp = cce.NonNull(DateTime.Now.ToString("o")).Replace(':', '.');

    public string FileTimestamp
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._fileTimestamp;
      }
      set
      {
        Contract.Requires(value != null);
        this._fileTimestamp = value;
      }
    }

    public void ExpandFilename(ref string pattern, string logPrefix, string fileTimestamp)
    {
      if (pattern != null)
      {
        pattern = pattern.Replace("@PREFIX@", logPrefix).Replace("@TIME@", fileTimestamp);
        string fn = Files.Count == 0 ? "" : Files[Files.Count - 1];
        fn = fn.Replace(':', '-').Replace('/', '-').Replace('\\', '-');
        pattern = pattern.Replace("@FILE@", fn);
      }
    }

    /// <summary>
    /// Process the option and modify "ps" accordingly.
    /// Return true if the option is one that is recognized.
    /// </summary>
    protected virtual bool ParseOption(string name, CommandLineParseState ps)
    {
      Contract.Requires(name != null);
      Contract.Requires(ps != null);

      if (ps.CheckBooleanFlag("version", ref VersionRequested) ||
          ps.CheckBooleanFlag("help", ref HelpRequested) ||
          ps.CheckBooleanFlag("?", ref HelpRequested) ||
          ps.CheckBooleanFlag("attrHelp", ref AttributeHelpRequested))
      {
        return true;
      }

      return false; // unrecognized option
    }

    protected class CommandLineParseState
    {
      public string s;
      public bool hasColonArgument;

      public readonly string[] /*!*/
        args;

      public int i;
      public int nextIndex;
      public bool EncounteredErrors;
      public readonly string ToolName;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(args != null);
        Contract.Invariant(0 <= i && i <= args.Length);
        Contract.Invariant(0 <= nextIndex && nextIndex <= args.Length);
      }


      public CommandLineParseState(string[] args, string toolName)
      {
        Contract.Requires(args != null);
        Contract.Requires(Contract.ForAll(0, args.Length, i => args[i] != null));
        Contract.Requires(toolName != null);
        Contract.Ensures(this.args == args);
        this.ToolName = toolName;
        this.s = null; // set later by client
        this.hasColonArgument = false; // set later by client
        this.args = args;
        this.i = 0;
        this.nextIndex = 0; // set later by client
        this.EncounteredErrors = false;
      }

      public bool CheckBooleanFlag(string flagName, ref bool flag, bool valueWhenPresent)
      {
        Contract.Requires(flagName != null);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        bool flagPresent = false;

        if ((s == "/" + flagName || s == "-" + flagName) && ConfirmArgumentCount(0))
        {
          flag = valueWhenPresent;
          flagPresent = true;
        }

        return flagPresent;
      }

      public bool CheckBooleanFlag(string flagName, ref bool flag)
      {
        Contract.Requires(flagName != null);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        return CheckBooleanFlag(flagName, ref flag, true);
      }

      /// <summary>
      /// If there is one argument and it is a non-negative integer, then set "arg" to that number and return "true".
      /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
      /// </summary>
      public bool GetNumericArgument(ref int arg)
      {
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        return GetNumericArgument(ref arg, a => 0 <= a);
      }

      /// <summary>
      /// If there is one argument and the filtering predicate holds, then set "arg" to that number and return "true".
      /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
      /// </summary>
      public bool GetNumericArgument(ref int arg, Predicate<int> filter)
      {
        Contract.Requires(filter != null);

        if (this.ConfirmArgumentCount(1))
        {
          try
          {
            Contract.Assume(args[i] != null);
            Contract.Assert(args[i] is string); // needed to prove args[i].IsPeerConsistent
            int d = Convert.ToInt32(this.args[this.i]);
            if (filter == null || filter(d))
            {
              arg = d;
              return true;
            }
          }
          catch (System.FormatException)
          {
          }
          catch (System.OverflowException)
          {
          }
        }
        else
        {
          return false;
        }

        Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
        return false;
      }

      /// <summary>
      /// If there is one argument and it is a non-negative integer less than "limit",
      /// then set "arg" to that number and return "true".
      /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
      /// </summary>
      public bool GetNumericArgument(ref int arg, int limit)
      {
        Contract.Requires(this.i < args.Length);
        Contract.Ensures(Math.Min(arg, 0) <= Contract.ValueAtReturn(out arg) &&
                         Contract.ValueAtReturn(out arg) < limit);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        int a = arg;
        if (!GetNumericArgument(ref a))
        {
          return false;
        }
        else if (a < limit)
        {
          arg = a;
          return true;
        }
        else
        {
          Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
          return false;
        }
      }

      /// <summary>
      /// If there is one argument and it is a non-negative real, then set "arg" to that number and return "true".
      /// Otherwise, emit an error message, leave "arg" unchanged, and return "false".
      /// </summary>
      public bool GetNumericArgument(ref double arg)
      {
        Contract.Ensures(Contract.ValueAtReturn(out arg) >= 0);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        if (this.ConfirmArgumentCount(1))
        {
          try
          {
            Contract.Assume(args[i] != null);
            Contract.Assert(args[i] is string); // needed to prove args[i].IsPeerConsistent
            double d = Convert.ToDouble(this.args[this.i]);
            if (0 <= d)
            {
              arg = d;
              return true;
            }
          }
          catch (System.FormatException)
          {
          }
          catch (System.OverflowException)
          {
          }
        }
        else
        {
          return false;
        }

        Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
        return false;
      }

      public bool ConfirmArgumentCount(int argCount)
      {
        Contract.Requires(0 <= argCount);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        Contract.Ensures(Contract.Result<bool>() ==
                         (!(hasColonArgument && argCount != 1) && !(args.Length < i + argCount)));
        if (hasColonArgument && argCount != 1)
        {
          Error("\"{0}\" cannot take a colon argument", s);
          nextIndex = args.Length;
          return false;
        }
        else if (args.Length < i + argCount)
        {
          Error("\"{0}\" expects {1} argument{2}", s, argCount.ToString(), (string) (argCount == 1 ? "" : "s"));
          nextIndex = args.Length;
          return false;
        }
        else
        {
          nextIndex = i + argCount;
          return true;
        }
      }

      public void Error(string message, params string[] args)
      {
        Contract.Requires(args != null);
        Contract.Requires(message != null);
        //modifies encounteredErrors, Console.Error.*;
        Console.Error.WriteLine("{0}: Error: {1}", ToolName, String.Format(message, args));
        EncounteredErrors = true;
      }
    }

    public virtual string Help =>
      $"Usage: {ToolName} [ option ... ] [ filename ... ]" + @"

  ---- General options -------------------------------------------------------

  /version      print the " + ToolName + @" version number
  /help         print this message
  /attrHelp     print a message about supported declaration attributes";

    public virtual string AttributeHelp => "";

    /// <summary>
    /// This method is called after all parsing is done, if no parse errors were encountered.
    /// </summary>
    public virtual void ApplyDefaultOptions()
    {
    }

    public virtual bool ProcessInfoFlags()
    {
      if (VersionRequested)
      {
        Console.WriteLine(Version);
        return true;
      }
      if (HelpRequested)
      {
        Console.WriteLine(Help);
        return true;
      }
      if (AttributeHelpRequested)
      {
        Console.WriteLine(AttributeHelp);
        return true;
      }
      
      return false;
    }

    /// <summary>
    /// Parses the command-line arguments "args" into the global flag variables.  Returns true
    /// if there were no errors.
    /// </summary>
    /// <param name="args">Consumed ("captured" and possibly modified) by the method.</param>
    public bool Parse([Captured] string[] /*!*/ args)
    {
      Contract.Requires(cce.NonNullElements(args));

      // save the command line options for the log files
      Environment += "Command Line Options: " + args.Concat(" ");
      args = cce.NonNull((string[]) args.Clone()); // the operations performed may mutate the array, so make a copy
      var ps = new CommandLineParseState(args, ToolName);

      while (ps.i < args.Length)
      {
        cce.LoopInvariant(ps.args == args);
        string arg = args[ps.i];
        Contract.Assert(arg != null);
        ps.s = arg.Trim();

        bool isOption = ps.s.StartsWith("-") || ps.s.StartsWith("/");
        int colonIndex = ps.s.IndexOf(':');
        if (0 <= colonIndex && isOption)
        {
          ps.hasColonArgument = true;
          args[ps.i] = ps.s.Substring(colonIndex + 1);
          ps.s = ps.s.Substring(0, colonIndex);
        }
        else
        {
          ps.i++;
          ps.hasColonArgument = false;
        }

        ps.nextIndex = ps.i;

        if (isOption)
        {
          if (!ParseOption(ps.s.Substring(1), ps))
          {
            if (Path.DirectorySeparatorChar == '/' && ps.s.StartsWith("/"))
              this._files.Add(arg);
            else
              ps.Error("unknown switch: {0}", ps.s);
          }
        }
        else
        {
          this._files.Add(arg);
        }

        ps.i = ps.nextIndex;
      }

      if (ps.EncounteredErrors)
      {
        Console.Error.WriteLine("Use /help for available options");
        return false;
      }
      else
      {
        this.ApplyDefaultOptions();
        return true;
      }
    }
  }

  /// <summary>
  /// Boogie command-line options (other tools can subclass this class in order to support a
  /// superset of Boogie's options).
  /// </summary>
  public class CommandLineOptions : CommandLineOptionEngine
  {
    public CommandLineOptions()
      : base("Boogie", "Boogie program verifier")
    {
    }

    protected CommandLineOptions(string toolName, string descriptiveName)
      : base(toolName, descriptiveName)
    {
      Contract.Requires(toolName != null);
      Contract.Requires(descriptiveName != null);
    }

    private static CommandLineOptions clo;

    public static CommandLineOptions /*!*/ Clo
    {
      get { return clo; }
    }

    public static void Install(CommandLineOptions options)
    {
      Contract.Requires(options != null);
      clo = options;
    }

    // Flags and arguments

    public bool RunningBoogieFromCommandLine = false; // "false" means running Boogie from the plug-in

    [ContractInvariantMethod]
    void ObjectInvariant2()
    {
      Contract.Invariant(LogPrefix != null);
      Contract.Invariant(0 <= PrintUnstructured &&
                         PrintUnstructured <
                         3); // 0 = print only structured,  1 = both structured and unstructured,  2 = only unstructured
    }

    public int VerifySnapshots = -1;
    public bool VerifySeparately = false;
    public string PrintFile = null;
    public int PrintUnstructured = 0;
    public bool UseBaseNameForFileName = false;
    public bool PrintDesugarings = false;
    public bool PrintLambdaLifting = false;
    public bool FreeVarLambdaLifting = false;
    public string ProverLogFilePath = null;
    public bool ProverLogFileAppend = false;

    public bool PrintInstrumented = false;
    public bool InstrumentWithAsserts = false;
    public string ProverPreamble = null;
    public bool WarnNotEliminatedVars = false;

    public enum InstrumentationPlaces
    {
      LoopHeaders,
      Everywhere
    }

    public InstrumentationPlaces InstrumentInfer = InstrumentationPlaces.LoopHeaders;
    public bool PrintWithUniqueASTIds = false;
    private string XmlSinkFilename = null;
    [Peer] public XmlSink XmlSink = null;
    public bool Wait = false;
    public bool Trace = false;
    public bool TraceTimes = false;
    public bool TraceProofObligations = false;

    public bool TraceCachingForTesting
    {
      get { return TraceCaching == 1 || TraceCaching == 3; }
    }

    public bool TraceCachingForBenchmarking
    {
      get { return TraceCaching == 2 || TraceCaching == 3; }
    }

    public bool TraceCachingForDebugging
    {
      get { return TraceCaching == 3; }
    }

    internal int TraceCaching = 0;
    public bool NoResolve = false;
    public bool NoTypecheck = false;
    public bool OverlookBoogieTypeErrors = false;
    public bool Verify = true;
    public bool TraceVerify = false;

    public int /*(0:3)*/
      ErrorTrace = 1;
    
    public bool ContractInfer = false;
    public bool ExplainHoudini = false;
    public bool ReverseHoudiniWorklist = false;
    public bool ConcurrentHoudini = false;
    public bool ModifyTopologicalSorting = false;
    public bool DebugConcurrentHoudini = false;
    public bool HoudiniUseCrossDependencies = false;
    public string StagedHoudini = null;
    public bool DebugStagedHoudini = false;
    public bool StagedHoudiniReachabilityAnalysis = false;
    public bool StagedHoudiniMergeIgnoredAnnotations = false;
    public int StagedHoudiniThreads = 1;
    public string VariableDependenceIgnore = null;
    public bool UseUnsatCoreForContractInfer = false;

    public bool PrintAssignment = false;

    // TODO(wuestholz): Add documentation for this flag.
    public bool PrintNecessaryAssumes = false;
    public int InlineDepth = -1;

    public bool
      UseProverEvaluate = false; // Use ProverInterface's Evaluate method, instead of model to get variable values

    public bool SoundnessSmokeTest = false;
    public int KInductionDepth = -1;
    public int EnableUnSatCoreExtract = 0;

    private string /*!*/
      _logPrefix = "";

    public string LogPrefix
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._logPrefix;
      }
      set
      {
        Contract.Requires(value != null);
        this._logPrefix = value;
      }
    }

    public bool PrettyPrint = true;

    public enum ProverWarnings
    {
      None,
      Stdout,
      Stderr
    }

    public ProverWarnings PrintProverWarnings = ProverWarnings.None;

    public enum SubsumptionOption
    {
      Never,
      NotForQuantifiers,
      Always
    }

    public SubsumptionOption UseSubsumption = SubsumptionOption.Always;

    public bool AlwaysAssumeFreeLoopInvariants = false;

    public enum ShowEnvironment
    {
      Never,
      DuringPrint,
      Always
    }

    public ShowEnvironment ShowEnv = ShowEnvironment.DuringPrint;
    public bool ShowVerifiedProcedureCount = true;

    [ContractInvariantMethod]
    void ObjectInvariant3()
    {
      Contract.Invariant(0 <= PrintErrorModel && PrintErrorModel <= 1);
      Contract.Invariant(0 <= EnhancedErrorMessages && EnhancedErrorMessages < 2);
      Contract.Invariant(0 <= Ai.StepsBeforeWidening && Ai.StepsBeforeWidening <= 9);
      Contract.Invariant(-1 <= this.bracketIdsInVC && this.bracketIdsInVC <= 1);
      Contract.Invariant(cce.NonNullElements(this.ProverOptions));
    }

    public int LoopUnrollCount = -1; // -1 means don't unroll loops
    public bool SoundLoopUnrolling = false;
    public int PrintErrorModel = 0;
    public string PrintErrorModelFile = null;

    public string /*?*/
      ModelViewFile = null;

    public int EnhancedErrorMessages = 0;
    public string PrintCFGPrefix = null;
    public bool ForceBplErrors = false; // if true, boogie error is shown even if "msg" attribute is present
    public bool UseArrayTheory = false;
    public bool RunDiagnosticsOnTimeout = false;
    public bool TraceDiagnosticsOnTimeout = false;
    public int TimeLimitPerAssertionInPercent = 10;
    public bool SIBoolControlVC = false;
    public bool ExpandLambdas = true; // not useful from command line, only to be set to false programatically
    public bool DoModSetAnalysis = false;
    public bool UseAbstractInterpretation = false;

    public string CivlDesugaredFile = null;
    public bool TrustMoverTypes = false;
    public bool TrustNoninterference = false;
    public int TrustLayersUpto = -1;
    public int TrustLayersDownto = int.MaxValue;

    public bool RemoveEmptyBlocks = true;
    public bool CoalesceBlocks = true;
    public bool PruneInfeasibleEdges = true;

    [Rep] public ProverFactory TheProverFactory;
    public string ProverDllName;
    public bool ProverHelpRequested = false;
    public List<string> ProverOptions = new List<string>();

    private int bracketIdsInVC = -1; // -1 - not specified, 0 - no, 1 - yes

    public int BracketIdsInVC
    {
      get
      {
        Contract.Ensures(-1 <= Contract.Result<int>() && Contract.Result<int>() <= 1);
        return this.bracketIdsInVC;
      }
      set
      {
        Contract.Requires(-1 <= value && value <= 1);
        this.bracketIdsInVC = value;
      }
    }

    public int TimeLimit = 0; // 0 means no limit
    public int ResourceLimit = 0; // default to 0
    public int SmokeTimeout = 10; // default to 10s
    public int ErrorLimit = 5; // 0 means attempt to falsify each assertion in a desugared implementation 
    public bool RestartProverPerVC = false;

    public double VcsMaxCost = 1.0;
    public double VcsPathJoinMult = 0.8;
    public double VcsPathCostMult = 1.0;
    public double VcsAssumeMult = 0.01;
    public double VcsPathSplitMult = 0.5; // 0.5-always, 2-rarely do path splitting
    public int VcsMaxSplits = 1;
    public int VcsMaxKeepGoingSplits = 1;
    public int VcsFinalAssertTimeout = 30;
    public int VcsKeepGoingTimeout = 1;
    public int VcsCores = 1;
    public bool VcsDumpSplits = false;

    public bool DebugRefuted = false;

    public XmlSink XmlRefuted
    {
      get
      {
        if (DebugRefuted)
          return XmlSink;
        else
          return null;
      }
    }

    // whether procedure inlining is enabled at call sites.
    public enum Inlining
    {
      None,
      Assert,
      Assume,
      Spec
    }

    public Inlining ProcedureInlining = Inlining.Assume;
    public bool PrintInlined = false;
    public bool ExtractLoops = false;
    public bool DeterministicExtractLoops = false;
    public string SecureVcGen = null;
    // Turns on FixedPointVC generation (Duality algorithm)
    public string FixedPointEngine = null;

    // Enables VC generation for Stratified Inlining. 
    // Set programmatically by Corral.
    public int StratifiedInlining = 0;

    // disable model generation, used by Corral/SI
    public bool StratifiedInliningWithoutModels = false; 

    // Sets the recursion bound, used for loop extraction, fixedpoint vc, etc.
    public int RecursionBound = 500;

    // Inference mode for fixed point engine
    public enum FixedPointInferenceMode
    {
      Corral,
      OldCorral,
      Flat,
      Procedure,
      Call
    }

    public FixedPointInferenceMode FixedPointMode = FixedPointInferenceMode.Procedure;

    public string PrintFixedPoint = null;

    public string PrintConjectures = null;

    public bool ExtractLoopsUnrollIrreducible = true; // unroll irreducible loops? (set programmatically)

    public enum TypeEncoding
    {
      Predicates,
      Arguments,
      Monomorphic
    }

    public TypeEncoding TypeEncodingMethod = TypeEncoding.Predicates;

    public bool Monomorphize = false;

    public bool ReflectAdd = false;

    public int LiveVariableAnalysis = 1;

    public bool UseLibrary = false;
    
    // Note that procsToCheck stores all patterns <p> supplied with /proc:<p>
    // (and similarly procsToIgnore for /noProc:<p>). Thus, if procsToCheck
    // is empty it means that all procedures should be checked.
    private List<string /*!*/> procsToCheck = new List<string /*!*/>();
    private List<string /*!*/> procsToIgnore = new List<string /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvariant5()
    {
      Contract.Invariant(cce.NonNullElements(this.procsToCheck, true));
      Contract.Invariant(cce.NonNullElements(this.procsToIgnore, true));
      Contract.Invariant(Ai != null);
    }

    public class AiFlags
    {
      public bool J_Trivial = false;
      public bool J_Intervals = false;

      public int /*0..9*/
        StepsBeforeWidening = 0;

      public bool DebugStatistics = false;
    }

    public readonly AiFlags /*!*/
      Ai = new AiFlags();

    public class ConcurrentHoudiniOptions
    {
      public List<string> ProverOptions = new List<string>();
      public int ErrorLimit = 5;
      public bool DisableLoopInvEntryAssert = false;
      public bool DisableLoopInvMaintainedAssert = false;
      public bool ModifyTopologicalSorting = false;
    }

    public List<ConcurrentHoudiniOptions> Cho = new List<ConcurrentHoudiniOptions>();

    protected override bool ParseOption(string name, CommandLineOptionEngine.CommandLineParseState ps)
    {
      var args = ps.args; // convenient synonym
      switch (name)
      {
        case "infer":
          if (ps.ConfirmArgumentCount(1))
          {
            UseAbstractInterpretation = true;
            foreach (char c in cce.NonNull(args[ps.i]))
            {
              switch (c)
              {
                case 't':
                  Ai.J_Trivial = true;
                  break;
                case 'j':
                  Ai.J_Intervals = true;
                  break;
                case 's':
                  Ai.DebugStatistics = true;
                  break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                case '8':
                case '9':
                  Ai.StepsBeforeWidening = (int) char.GetNumericValue(c);
                  break;
                default:
                  ps.Error("Invalid argument '{0}' to option {1}", c.ToString(), ps.s);
                  break;
              }
            }

            if (Ai.J_Trivial == Ai.J_Intervals)
            {
              ps.Error("Option {0} requires the selection of exactly one abstract domain", ps.s);
            }
          }

          return true;

        case "break":
        case "launch":
          if (ps.ConfirmArgumentCount(0))
          {
            System.Diagnostics.Debugger.Launch();
          }

          return true;

        case "lib":
          if (ps.ConfirmArgumentCount(0))
          {
            this.UseLibrary = true;
          }

          return true;
        
        case "proc":
          if (ps.ConfirmArgumentCount(1))
          {
            this.procsToCheck.Add(cce.NonNull(args[ps.i]));
          }

          return true;

        case "noProc":
          if (ps.ConfirmArgumentCount(1))
          {
            this.procsToIgnore.Add(cce.NonNull(args[ps.i]));
          }

          return true;

        case "xml":
          if (ps.ConfirmArgumentCount(1))
          {
            XmlSinkFilename = args[ps.i];
          }

          return true;

        case "print":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintFile = args[ps.i];
          }

          return true;

        case "pretty":
          int val = 1;
          if (ps.GetNumericArgument(ref val, 2))
          {
            PrettyPrint = val == 1;
          }

          return true;

        case "civlDesugaredFile":
          if (ps.ConfirmArgumentCount(1))
          {
            CivlDesugaredFile = args[ps.i];
          }

          return true;

        case "trustLayersUpto":
          if (ps.ConfirmArgumentCount(1))
          {
            ps.GetNumericArgument(ref TrustLayersUpto);
          }

          return true;

        case "trustLayersDownto":
          if (ps.ConfirmArgumentCount(1))
          {
            ps.GetNumericArgument(ref TrustLayersDownto);
          }

          return true;

        case "proverLog":
          if (ps.ConfirmArgumentCount(1))
          {
            ProverLogFilePath = args[ps.i];
          }

          return true;

        case "proverPreamble":
          if (ps.ConfirmArgumentCount(1))
          {
            ProverPreamble = args[ps.i];
          }

          return true;

        case "logPrefix":
          if (ps.ConfirmArgumentCount(1))
          {
            string s = cce.NonNull(args[ps.i]);
            LogPrefix += s.Replace('/', '-').Replace('\\', '-');
          }

          return true;

        case "errorTrace":
          ps.GetNumericArgument(ref ErrorTrace, 3);
          return true;

        case "proverWarnings":
        {
          int pw = 0;
          if (ps.GetNumericArgument(ref pw, 3))
          {
            switch (pw)
            {
              case 0:
                PrintProverWarnings = ProverWarnings.None;
                break;
              case 1:
                PrintProverWarnings = ProverWarnings.Stdout;
                break;
              case 2:
                PrintProverWarnings = ProverWarnings.Stderr;
                break;
              default:
              {
                Contract.Assert(false);
                throw new cce.UnreachableException();
              } // postcondition of GetNumericArgument guarantees that we don't get here
            }
          }

          return true;
        }

        case "env":
        {
          int e = 0;
          if (ps.GetNumericArgument(ref e, 3))
          {
            switch (e)
            {
              case 0:
                ShowEnv = ShowEnvironment.Never;
                break;
              case 1:
                ShowEnv = ShowEnvironment.DuringPrint;
                break;
              case 2:
                ShowEnv = ShowEnvironment.Always;
                break;
              default:
              {
                Contract.Assert(false);
                throw new cce.UnreachableException();
              } // postcondition of GetNumericArgument guarantees that we don't get here
            }
          }

          return true;
        }

        case "printVerifiedProceduresCount":
        {
          int n = 0;
          if (ps.GetNumericArgument(ref n, 2))
          {
            ShowVerifiedProcedureCount = n != 0;
          }

          return true;
        }

        case "loopUnroll":
          ps.GetNumericArgument(ref LoopUnrollCount);
          return true;

        case "printModel":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "0":
                PrintErrorModel = 0;
                break;
              case "1":
                PrintErrorModel = 1;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;

        case "mv":
          if (ps.ConfirmArgumentCount(1))
          {
            ModelViewFile = args[ps.i];
          }

          return true;

        case "printModelToFile":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintErrorModelFile = args[ps.i];
          }

          return true;

        case "enhancedErrorMessages":
          ps.GetNumericArgument(ref EnhancedErrorMessages, 2);
          return true;

        case "printCFG":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintCFGPrefix = args[ps.i];
          }

          return true;

        case "inlineDepth":
          ps.GetNumericArgument(ref InlineDepth);
          return true;

        case "subsumption":
        {
          int s = 0;
          if (ps.GetNumericArgument(ref s, 3))
          {
            switch (s)
            {
              case 0:
                UseSubsumption = SubsumptionOption.Never;
                break;
              case 1:
                UseSubsumption = SubsumptionOption.NotForQuantifiers;
                break;
              case 2:
                UseSubsumption = SubsumptionOption.Always;
                break;
              default:
              {
                Contract.Assert(false);
                throw new cce.UnreachableException();
              } // postcondition of GetNumericArgument guarantees that we don't get here
            }
          }

          return true;
        }

        case "liveVariableAnalysis":
        {
          int lva = 0;
          if (ps.GetNumericArgument(ref lva, 3))
          {
            LiveVariableAnalysis = lva;
          }

          return true;
        }

        case "removeEmptyBlocks":
        {
          int reb = 0;
          if (ps.GetNumericArgument(ref reb, 2))
          {
            RemoveEmptyBlocks = reb == 1;
          }

          return true;
        }

        case "coalesceBlocks":
        {
          int cb = 0;
          if (ps.GetNumericArgument(ref cb, 2))
          {
            CoalesceBlocks = cb == 1;
          }

          return true;
        }

        case "noPruneInfeasibleEdges":
        {
          if (ps.ConfirmArgumentCount(0))
          {
            PruneInfeasibleEdges = false;
          }

          return true;
        }

        case "stagedHoudini":
        {
          if (ps.ConfirmArgumentCount(1))
          {
            if (args[ps.i] == "COARSE" ||
                args[ps.i] == "FINE" ||
                args[ps.i] == "BALANCED")
            {
              StagedHoudini = args[ps.i];
            }
            else
            {
              ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
            }
          }

          return true;
        }

        case "stagedHoudiniThreads":
        {
          ps.GetNumericArgument(ref StagedHoudiniThreads);
          return true;
        }

        case "stagedHoudiniReachabilityAnalysis":
        {
          if (ps.ConfirmArgumentCount(0))
          {
            StagedHoudiniReachabilityAnalysis = true;
          }

          return true;
        }

        case "stagedHoudiniMergeIgnoredAnnotations":
        {
          if (ps.ConfirmArgumentCount(0))
          {
            StagedHoudiniMergeIgnoredAnnotations = true;
          }

          return true;
        }

        case "debugStagedHoudini":
        {
          if (ps.ConfirmArgumentCount(0))
          {
            DebugStagedHoudini = true;
          }

          return true;
        }

        case "variableDependenceIgnore":
        {
          if (ps.ConfirmArgumentCount(1))
          {
            VariableDependenceIgnore = args[ps.i];
          }

          return true;
        }
        
        case "proverDll":
          if (ps.ConfirmArgumentCount(1))
          {
            ProverDllName = cce.NonNull(args[ps.i]);
            TheProverFactory = ProverFactory.Load(ProverDllName);
          }

          return true;

        case "p":
        case "proverOpt":
          if (ps.ConfirmArgumentCount(1))
          {
            ProverOptions.Add(cce.NonNull(args[ps.i]));
          }

          return true;

        case "extractLoops":
          if (ps.ConfirmArgumentCount(0))
          {
            ExtractLoops = true;
          }

          return true;

        case "deterministicExtractLoops":
          if (ps.ConfirmArgumentCount(0))
          {
            DeterministicExtractLoops = true;
          }

          return true;

        case "inline":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "none":
                ProcedureInlining = Inlining.None;
                break;
              case "assert":
                ProcedureInlining = Inlining.Assert;
                break;
              case "assume":
                ProcedureInlining = Inlining.Assume;
                break;
              case "spec":
                ProcedureInlining = Inlining.Spec;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;
        case "secure":
          if (ps.ConfirmArgumentCount(1))
            SecureVcGen = args[ps.i];
          return true;
        case "fixedPointEngine":
          if (ps.ConfirmArgumentCount(1))
          {
            FixedPointEngine = args[ps.i];
          }

          return true;
        case "fixedPointInfer":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "corral":
                FixedPointMode = FixedPointInferenceMode.Corral;
                break;
              case "oldCorral":
                FixedPointMode = FixedPointInferenceMode.OldCorral;
                break;
              case "flat":
                FixedPointMode = FixedPointInferenceMode.Flat;
                break;
              case "procedure":
                FixedPointMode = FixedPointInferenceMode.Procedure;
                break;
              case "call":
                FixedPointMode = FixedPointInferenceMode.Call;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;
        case "printFixedPoint":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintFixedPoint = args[ps.i];
          }

          return true;
        case "printConjectures":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintConjectures = args[ps.i];
          }

          return true;
        case "recursionBound":
          if (ps.ConfirmArgumentCount(1))
          {
            RecursionBound = Int32.Parse(cce.NonNull(args[ps.i]));
          }

          return true;
        case "enableUnSatCoreExtraction":
          if (ps.ConfirmArgumentCount(1))
          {
            EnableUnSatCoreExtract = Int32.Parse(cce.NonNull(args[ps.i]));
          }

          return true;
        
        case "typeEncoding":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "p":
              case "predicates":
                TypeEncodingMethod = TypeEncoding.Predicates;
                break;
              case "a":
              case "arguments":
                TypeEncodingMethod = TypeEncoding.Arguments;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;

        case "monomorphize":
          if (ps.ConfirmArgumentCount(0))
          {
            Monomorphize = true;
          }
          
          return true;

        case "instrumentInfer":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "e":
                InstrumentInfer = InstrumentationPlaces.Everywhere;
                break;
              case "h":
                InstrumentInfer = InstrumentationPlaces.LoopHeaders;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;

        case "concurrentHoudini":
          if (ps.ConfirmArgumentCount(0))
          {
            ConcurrentHoudini = true;
          }

          return true;

        case "modifyTopologicalSorting":
          if (ps.ConfirmArgumentCount(0))
          {
            ModifyTopologicalSorting = true;
          }

          return true;

        case "debugConcurrentHoudini":
          if (ps.ConfirmArgumentCount(0))
          {
            DebugConcurrentHoudini = true;
          }

          return true;

        case "vcBrackets":
          ps.GetNumericArgument(ref bracketIdsInVC, 2);
          return true;

        case "vcsMaxCost":
          ps.GetNumericArgument(ref VcsMaxCost);
          return true;

        case "vcsPathJoinMult":
          ps.GetNumericArgument(ref VcsPathJoinMult);
          return true;

        case "vcsPathCostMult":
          ps.GetNumericArgument(ref VcsPathCostMult);
          return true;

        case "vcsAssumeMult":
          ps.GetNumericArgument(ref VcsAssumeMult);
          return true;

        case "vcsPathSplitMult":
          ps.GetNumericArgument(ref VcsPathSplitMult);
          return true;

        case "vcsMaxSplits":
          ps.GetNumericArgument(ref VcsMaxSplits);
          return true;

        case "vcsMaxKeepGoingSplits":
          ps.GetNumericArgument(ref VcsMaxKeepGoingSplits);
          return true;

        case "vcsFinalAssertTimeout":
          ps.GetNumericArgument(ref VcsFinalAssertTimeout);
          return true;

        case "vcsKeepGoingTimeout":
          ps.GetNumericArgument(ref VcsKeepGoingTimeout);
          return true;

        case "vcsCores":
          ps.GetNumericArgument(ref VcsCores, a => 1 <= a);
          return true;

        case "vcsLoad":
          double load = 0.0;
          if (ps.GetNumericArgument(ref load))
          {
            if (3.0 <= load)
            {
              ps.Error("surprisingly high load specified; got {0}, expected nothing above 3.0", load.ToString());
              load = 3.0;
            }

            int p = (int) Math.Round(System.Environment.ProcessorCount * load);
            VcsCores = p < 1 ? 1 : p;
          }

          return true;

        case "timeLimit":
          ps.GetNumericArgument(ref TimeLimit);
          return true;

        case "rlimit":
          ps.GetNumericArgument(ref ResourceLimit);
          return true;

        case "timeLimitPerAssertionInPercent":
          ps.GetNumericArgument(ref TimeLimitPerAssertionInPercent, a => 0 < a);
          return true;

        case "smokeTimeout":
          ps.GetNumericArgument(ref SmokeTimeout);
          return true;

        case "errorLimit":
          ps.GetNumericArgument(ref ErrorLimit);
          return true;

        case "verifySnapshots":
          ps.GetNumericArgument(ref VerifySnapshots, 4);
          return true;

        case "traceCaching":
          ps.GetNumericArgument(ref TraceCaching, 4);
          return true;

        case "kInductionDepth":
          ps.GetNumericArgument(ref KInductionDepth);
          return true;

        default:
          bool optionValue = false;
          if (ps.CheckBooleanFlag("printUnstructured", ref optionValue))
          {
            PrintUnstructured = optionValue ? 1 : 0;
            return true;
          }

          if (ps.CheckBooleanFlag("printDesugared", ref PrintDesugarings) ||
              ps.CheckBooleanFlag("printLambdaLifting", ref PrintLambdaLifting) ||
              ps.CheckBooleanFlag("printInstrumented", ref PrintInstrumented) ||
              ps.CheckBooleanFlag("printWithUniqueIds", ref PrintWithUniqueASTIds) ||
              ps.CheckBooleanFlag("wait", ref Wait) ||
              ps.CheckBooleanFlag("trace", ref Trace) ||
              ps.CheckBooleanFlag("traceTimes", ref TraceTimes) ||
              ps.CheckBooleanFlag("tracePOs", ref TraceProofObligations) ||
              ps.CheckBooleanFlag("noResolve", ref NoResolve) ||
              ps.CheckBooleanFlag("noTypecheck", ref NoTypecheck) ||
              ps.CheckBooleanFlag("overlookTypeErrors", ref OverlookBoogieTypeErrors) ||
              ps.CheckBooleanFlag("noVerify", ref Verify, false) ||
              ps.CheckBooleanFlag("traceverify", ref TraceVerify) ||
              ps.CheckBooleanFlag("alwaysAssumeFreeLoopInvariants", ref AlwaysAssumeFreeLoopInvariants, true) ||
              ps.CheckBooleanFlag("proverHelp", ref ProverHelpRequested) ||
              ps.CheckBooleanFlag("proverLogAppend", ref ProverLogFileAppend) ||
              ps.CheckBooleanFlag("soundLoopUnrolling", ref SoundLoopUnrolling) ||
              ps.CheckBooleanFlag("checkInfer", ref InstrumentWithAsserts) ||
              ps.CheckBooleanFlag("restartProver", ref RestartProverPerVC) ||
              ps.CheckBooleanFlag("printInlined", ref PrintInlined) ||
              ps.CheckBooleanFlag("smoke", ref SoundnessSmokeTest) ||
              ps.CheckBooleanFlag("vcsDumpSplits", ref VcsDumpSplits) ||
              ps.CheckBooleanFlag("dbgRefuted", ref DebugRefuted) ||
              ps.CheckBooleanFlag("reflectAdd", ref ReflectAdd) ||
              ps.CheckBooleanFlag("useArrayTheory", ref UseArrayTheory) ||
              ps.CheckBooleanFlag("doModSetAnalysis", ref DoModSetAnalysis) ||
              ps.CheckBooleanFlag("runDiagnosticsOnTimeout", ref RunDiagnosticsOnTimeout) ||
              ps.CheckBooleanFlag("traceDiagnosticsOnTimeout", ref TraceDiagnosticsOnTimeout) ||
              ps.CheckBooleanFlag("boolControlVC", ref SIBoolControlVC, true) ||
              ps.CheckBooleanFlag("contractInfer", ref ContractInfer) ||
              ps.CheckBooleanFlag("explainHoudini", ref ExplainHoudini) ||
              ps.CheckBooleanFlag("reverseHoudiniWorklist", ref ReverseHoudiniWorklist) ||
              ps.CheckBooleanFlag("crossDependencies", ref HoudiniUseCrossDependencies) ||
              ps.CheckBooleanFlag("useUnsatCoreForContractInfer", ref UseUnsatCoreForContractInfer) ||
              ps.CheckBooleanFlag("printAssignment", ref PrintAssignment) ||
              ps.CheckBooleanFlag("printNecessaryAssumes", ref PrintNecessaryAssumes) ||
              ps.CheckBooleanFlag("useProverEvaluate", ref UseProverEvaluate) ||
              ps.CheckBooleanFlag("deterministicExtractLoops", ref DeterministicExtractLoops) ||
              ps.CheckBooleanFlag("verifySeparately", ref VerifySeparately) ||
              ps.CheckBooleanFlag("trustMoverTypes", ref TrustMoverTypes) ||
              ps.CheckBooleanFlag("trustNoninterference", ref TrustNoninterference) ||
              ps.CheckBooleanFlag("useBaseNameForFileName", ref UseBaseNameForFileName) ||
              ps.CheckBooleanFlag("freeVarLambdaLifting", ref FreeVarLambdaLifting) ||
              ps.CheckBooleanFlag("warnNotEliminatedVars", ref WarnNotEliminatedVars)
          )
          {
            // one of the boolean flags matched
            return true;
          }

          break;
      }

      return base.ParseOption(name, ps); // defer to superclass
    }

    public override void ApplyDefaultOptions()
    {
      Contract.Ensures(TheProverFactory != null);

      base.ApplyDefaultOptions();

      // expand macros in filenames, now that LogPrefix is fully determined
      ExpandFilename(ref XmlSinkFilename, LogPrefix, FileTimestamp);
      ExpandFilename(ref PrintFile, LogPrefix, FileTimestamp);
      ExpandFilename(ref ProverLogFilePath, LogPrefix, FileTimestamp);
      ExpandFilename(ref PrintErrorModelFile, LogPrefix, FileTimestamp);

      Contract.Assume(XmlSink == null); // XmlSink is to be set here
      if (XmlSinkFilename != null)
      {
        XmlSink = new XmlSink(XmlSinkFilename);
      }

      if (TheProverFactory == null)
      {
        ProverDllName = "SMTLib";
        TheProverFactory = ProverFactory.Load(ProverDllName);
      }

      if (StratifiedInlining > 0)
      {
        TypeEncodingMethod = TypeEncoding.Monomorphic;
        UseArrayTheory = true;
        UseAbstractInterpretation = false;
        if (ProverDllName == "SMTLib")
        {
          ErrorLimit = 1;
        }

        if (UseProverEvaluate)
          StratifiedInliningWithoutModels = true;
      }

      if (Trace)
      {
        BoogieDebug.DoPrinting = true; // reuse the -trace option for debug printing
      }
    }

    public override bool ProcessInfoFlags()
    {
      if (base.ProcessInfoFlags())
      {
        return true;
      }

      if (ProverHelpRequested)
      {
        Console.WriteLine(ProverHelp);
        return true;
      }

      return false;
    }

    public bool UserWantsToCheckRoutine(string methodFullname)
    {
      Contract.Requires(methodFullname != null);
      Func<string, bool> match = s => Regex.IsMatch(methodFullname, "^" + Regex.Escape(s).Replace(@"\*", ".*") + "$");
      return (procsToCheck.Count == 0 || procsToCheck.Any(match)) && !procsToIgnore.Any(match);
    }

    // Used by Dafny to decide if it should perform compilation
    public bool UserConstrainedProcsToCheck => procsToCheck.Count > 0 || procsToIgnore.Count > 0;

    public virtual StringCollection ParseNamedArgumentList(string argList)
    {
      if (argList == null || argList.Length == 0)
        return null;
      StringCollection result = new StringCollection();
      int i = 0;
      for (int n = argList.Length; i < n;)
      {
        cce.LoopInvariant(0 <= i);
        int separatorIndex = this.GetArgumentSeparatorIndex(argList, i);
        if (separatorIndex > i)
        {
          result.Add(argList.Substring(i, separatorIndex - i));
          i = separatorIndex + 1;
          continue;
        }

        result.Add(argList.Substring(i));
        break;
      }

      return result;
    }

    public int GetArgumentSeparatorIndex(string argList, int startIndex)
    {
      Contract.Requires(argList != null);
      Contract.Requires(0 <= startIndex && startIndex <= argList.Length);
      Contract.Ensures(Contract.Result<int>() < argList.Length);
      int commaIndex = argList.IndexOf(",", startIndex);
      int semicolonIndex = argList.IndexOf(";", startIndex);
      if (commaIndex == -1)
        return semicolonIndex;
      if (semicolonIndex == -1)
        return commaIndex;
      if (commaIndex < semicolonIndex)
        return commaIndex;
      return semicolonIndex;
    }

    public string ProverHelp => TheProverFactory.BlankProverOptions().Help;

    public override string AttributeHelp =>
@"Boogie: The following attributes are supported by this version.

  ---- On top-level declarations ---------------------------------------------

    {:ignore}
      Ignore the declaration (after checking for duplicate names).

    {:extern}
      If two top-level declarations introduce the same name (for example, two
      constants with the same name or two procedures with the same name), then
      Boogie usually produces an error message.  However, if at least one of
      the declarations is declared with :extern, one of the declarations is
      ignored.  If both declarations are :extern, Boogie arbitrarily chooses
      one of them to keep; otherwise, Boogie ignore the :extern declaration
      and keeps the other.

    {:checksum <string>}
      Attach a checksum to be used for verification result caching.

  ---- On implementations and procedures -------------------------------------

     {:inline N}
       Inline given procedure (can be also used on implementation).
       N should be a non-negative number and represents the inlining depth.
       With /inline:assume call is replaced with ""assume false"" once inlining depth is reached.
       With /inline:assert call is replaced with ""assert false"" once inlining depth is reached.
       With /inline:spec call is left as is once inlining depth is reached.
       With /inline:none the entire attribute is ignored.
       With /inline:assume and /inline:assert options, methods with the attribute {:inline N} are not verified.

     {:verify false}
       Skip verification of an implementation.

     {:vcs_max_cost N}
     {:vcs_max_splits N}
     {:vcs_max_keep_going_splits N}
       Per-implementation versions of
       /vcsMaxCost, /vcsMaxSplits and /vcsMaxKeepGoingSplits.

     {:selective_checking true}
       Turn all asserts into assumes except for the ones reachable from
       assumptions marked with the attribute {:start_checking_here}.
       Thus, ""assume {:start_checking_here} something;"" becomes an inverse
       of ""assume false;"": the first one disables all verification before
       it, and the second one disables all verification after.

     {:priority N}
       Assign a positive priority 'N' to an implementation to control the
       order in which implementations are verified (default: N = 1).

     {:id <string>}
       Assign a unique ID to an implementation to be used for verification
       result caching (default: ""<impl. name>:0"").

     {:timeLimit N}
       Set the time limit for verifying a given implementation.

     {:rlimit N}
       Set the Z3 resource limit for verifying a given implementation.

     {:random_seed N}
       Set the random seed for verifying a given implementation.

  ---- On functions ----------------------------------------------------------

     {:builtin ""spec""}
     {:bvbuiltin ""spec""}
       Rewrite the function to built-in prover function symbol 'fn'.

     {:define}
     {:define true}
       Turn this function into a definition (using the define-fun construct)
       when using the SMT-LIB backend.  Can only be used with non-recursive
       functions. Cannot be combined with :inline attribute.
       Currently works only with monomorphic functions.

     {:inline}
     {:inline true}
       Expand function according to its definition before going to the prover.
       Cannot be combined with :define attribute.

     {:never_pattern true}
       Terms starting with this function symbol will never be
       automatically selected as patterns. It does not prevent them
       from being used inside the triggers, and does not affect explicit
       trigger annotations. Internally it works by adding {:nopats ...}
       annotations to quantifiers.

     {:identity}
     {:identity true}
       If the function has 1 argument and the use of it has type X->X for
       some X, then the abstract interpreter will treat the function as an
       identity function.  Note, the abstract interpreter trusts the
       attribute--it does not try to verify that the function really is an
       identity function.

  ---- On variables ----------------------------------------------------------

     {:existential true}
       Marks a global Boolean variable as existentially quantified. If
       used in combination with option /contractInfer Boogie will check
       whether there exists a Boolean assignment to the existentials
       that makes all verification conditions valid.  Without option
       /contractInfer the attribute is ignored.

  ---- On assert statements --------------------------------------------------

     {:subsumption n}
       Overrides the /subsumption command-line setting for this assertion.

     {:split_here}
       Verifies code leading to this point and code leading from this point
       to the next split_here as separate pieces.  May help with timeouts.
       May also occasionally double-report errors.

     {:msg <string>}
       Prints <string> rather than the standard message for assertion failure.
       Also applicable to requires and ensures declarations. 

  ---- On statements ---------------------------------------------------------

     {:print e0, e1, e2, ...}
       Indicates that expressions e0, e1, e2, ... must be printed.  Must be
       used in conjunction with /enhancedErrorMessages:n command-line option.

     {:captureState s}
       When this attribute is applied to assume commands, it causes the 
       /mv:<string> command-line option to group each counterexample model
       into a sequence of states. In particular, this sequence of states
       shows the values of variables at each {:captureState ...} point in
       the counterexample trace. The argument 's' is to be a string, and it
       will be printed as part of /mv's output.

  ---- CIVL ------------------------------------------------------------------

     {:yields}
       Yielding procedure.

     {:atomic}
     {:right}
     {:left}
     {:both}
       Mover type of atomic action or mover procedure.

     {:intro}
       Introduction action.

     {:lemma}
       Lemma procedure.

     {:yield_invariant}
       Yield invariant.

     {:layer N}
     {:layer M, N}
     {:layer N1, N2, ...}
       Layer number, layer range, or set of layer numbers, respectively.

     {:hide}
       Hidden input/output parameter.

     {:yield_requires ""inv"", e0, e1, ...}
     {:yield_ensures ""inv"", e0, e1, ...}
     {:yield_preserves ""inv"", e0, e1, ...}
     {:yield_loop ""inv"", e0, e1, ...}
       Invocation of yield invariant.

     {:refines ""action""}
       Refined atomic action of a yielding procedure.

     {:cooperates}
       Cooperating loop or mover procedure.

     {:linear ""domain""}
       Permission type for domain.
       Collector function for domain.
       Linear variable (both global and local).

     {:linear_in ""domain""}
     {:linear_out ""domain""}
       Linear input/output parameter.

     {:witness ""g""}
     {:commutativity ""A"", ""B""}
       Function provides witness for global variable g in commutativity check
       between action A and action B. Multiple declarations of :commutativity
       are supported.

     {:pending_async}
       Pending async datatype.
       Local variable collecting pending asyncs in yielding procedure.
     {:pending_async ""action""}
       Pending async datatype constructor for action.
     {:pending_async ""action1"", ""action2"", ...}
       Output parameter of atomic action.

     {:sync}
       Synchronized async call.

     {:IS ""B"", ""I""}
       Apply inductive sequentialization to convert an action into action B
       using invariant action I
     {:elim ""A""}
     {:elim ""A"", ""A'""}
       by eliminating multiple actions A (optionally using abstraction A')
     {:choice}
       and optionally using an output parameter to indicate the selected
       pending async.

     {:IS_invariant}
     {:IS_abstraction}
       Actions that are only used as invariant actions or abstractions in
       inductive sequentialization. These are exempt from the overall pool of
       actions for commutativity checking.

     {:backward}
       Backward assignment in atomic action.";

    public override string Help =>
      base.Help + @"
  /env:<n>      print command line arguments
                  0 - never, 1 (default) - during BPL print and prover log,
                  2 - like 1 and also to standard output
  /printVerifiedProceduresCount:<n>
                0 - no
                1 (default) - yes
  /wait         await Enter from keyboard before terminating program
  /xml:<file>   also produce output in XML format to <file>

  ---- Boogie options --------------------------------------------------------

  Multiple .bpl files supplied on the command line are concatenated into one
  Boogie program.

  /lib           : Include library definitions
  /proc:<p>      : Only check procedures matched by pattern <p>. This option
                   may be specified multiple times to match multiple patterns.
                   The pattern <p> matches the whole procedure name and may
                   contain * wildcards which match any character zero or more
                   times.
  /noProc:<p>    : Do not check procedures matched by pattern <p>. Exclusions
                   with /noProc are applied after inclusions with /proc.
  /noResolve     : parse only
  /noTypecheck   : parse and resolve only

  /print:<file>  : print Boogie program after parsing it
                   (use - as <file> to print to console)
  /pretty:<n>
                0 - print each Boogie statement on one line (faster).
                1 (default) - pretty-print with some line breaks.
  /printWithUniqueIds : print augmented information that uniquely
                   identifies variables
  /printUnstructured : with /print option, desugars all structured statements
  /printDesugared : with /print option, desugars calls
  /printLambdaLifting : with /print option, desugars lambda lifting

  /freeVarLambdaLifting : Boogie's lambda lifting transforms the bodies of lambda
                         expressions into templates with holes. By default, holes
                         are maximally large subexpressions that do not contain
                         bound variables. This option performs a form of lambda
                         lifting in which holes are the lambda's free variables.

  /overlookTypeErrors : skip any implementation with resolution or type
                        checking errors

  /loopUnroll:<n>
                unroll loops, following up to n back edges (and then some)
  /soundLoopUnrolling
                sound loop unrolling
  /printModel:<n>
                0 (default) - do not print Z3's error model
                1 - print Z3's error model
  /printModelToFile:<file>
                print model to <file> instead of console
  /mv:<file>    Specify file to save the model with captured states 
                (see documentation for :captureState attribute)
  /enhancedErrorMessages:<n>
                0 (default) - no enhanced error messages
                1 - Z3 error model enhanced error messages

  /printCFG:<prefix> : print control flow graph of each implementation in
                       Graphviz format to files named:
                         <prefix>.<procedure name>.dot

  /useBaseNameForFileName : When parsing use basename of file for tokens instead
                            of the path supplied on the command line

  ---- Inference options -----------------------------------------------------

  /infer:<flags>
                use abstract interpretation to infer invariants
                <flags> must specify exactly one of the following domains:
                   t = trivial bottom/top lattice
                   j = stronger intervals
                together with any of the following options:
                   s = debug statistics
                0..9 = number of iterations before applying a widen (default=0)
  /checkInfer   instrument inferred invariants as asserts to be checked by
                theorem prover
  /contractInfer
                perform procedure contract inference
  /instrumentInfer
                h - instrument inferred invariants only at beginning of
                    loop headers (default)
                e - instrument inferred invariants at beginning and end
                    of every block (this mode is intended for use in
                    debugging of abstract domains)
  /printInstrumented
                print Boogie program after it has been instrumented with
                invariants

  ---- Debugging and general tracing options ---------------------------------

  /trace        blurt out various debug trace information
  /traceTimes   output timing information at certain points in the pipeline
  /tracePOs     output information about the number of proof obligations
                (also included in the /trace output)
  /break        launch and break into debugger

  ---- CIVL options ----------------------------------------------------------

  /trustMoverTypes
                do not verify mover type annotations on atomic action declarations
  /trustNoninterference
                do not perform noninterference checks
  /trustLayersUpto:<n>
                do not verify layers <n> and below
  /trustLayersDownto:<n>
                do not verify layers <n> and above
  /civlDesugaredFile:<file>
                print plain Boogie program to <file>

  ---- Verification-condition generation options -----------------------------

  /liveVariableAnalysis:<c>
                0 = do not perform live variable analysis
                1 = perform live variable analysis (default)
                2 = perform interprocedural live variable analysis
  /noVerify     skip VC generation and invocation of the theorem prover
  /verifySnapshots:<n>
                verify several program snapshots (named <filename>.v0.bpl
                to <filename>.vN.bpl) using verification result caching:
                0 - do not use any verification result caching (default)
                1 - use the basic verification result caching
                2 - use the more advanced verification result caching
                3 - use the more advanced caching and report errors according
                    to the new source locations for errors and their
                    related locations (but not /errorTrace and CaptureState
                    locations)
  /traceCaching:<n>
                0 (default) - none
                1 - for testing
                2 - for benchmarking
                3 - for testing, benchmarking, and debugging
  /verifySeparately
                verify each input program separately
  /removeEmptyBlocks:<c>
                0 - do not remove empty blocks during VC generation
                1 - remove empty blocks (default)
  /coalesceBlocks:<c>
                0 = do not coalesce blocks
                1 = coalesce blocks (default)
  /traceverify  print debug output during verification condition generation
  /subsumption:<c>
                apply subsumption to asserted conditions:
                0 - never, 1 - not for quantifiers, 2 (default) - always
  /alwaysAssumeFreeLoopInvariants
                usually, a free loop invariant (or assume
                statement in that position) is ignored in checking contexts
                (like other free things); this option includes these free
                loop invariants as assumes in both contexts
  /inline:<i>   use inlining strategy <i> for procedures with the :inline
                attribute, see /attrHelp for details:
                  none
                  assume (default)
                  assert
                  spec
  /printInlined
                print the implementation after inlining calls to
                procedures with the :inline attribute (works with /inline)
  /fixedPointEngine:<engine>
                Use the specified fixed point engine for inference
  /recursionBound:<n>
                Set the recursion bound for stratified inlining to
                be n (default 500)
  /smoke        Soundness Smoke Test: try to stick assert false; in some
                places in the BPL and see if we can still prove it
  /smokeTimeout:<n>
                Timeout, in seconds, for a single theorem prover
                invocation during smoke test, defaults to 10.
  /causalImplies
                Translate Boogie's A ==> B into prover's A ==> A && B.
  /typeEncoding:<m>
                Encoding of types when generating VC of a polymorphic program:
                   p = predicates (default)
                   a = arguments
                Boogie automatically detects monomorphic programs and enables
                monomorphic VC generation, thereby overriding the above option.
  /monomorphize
                Try to monomorphize program. An error is reported if
                monomorphization is not possible. This feature is experimental!
  /useArrayTheory
                Use the SMT theory of arrays (as opposed to axioms). Supported
                only for monomorphic programs.
  /reflectAdd   In the VC, generate an auxiliary symbol, elsewhere defined
                to be +, instead of +.

  ---- Verification-condition splitting --------------------------------------

  /vcsMaxCost:<f>
                VC will not be split unless the cost of a VC exceeds this
                number, defaults to 2000.0. This does NOT apply in the
                keep-going mode after first round of splitting.
  /vcsMaxSplits:<n>
                Maximal number of VC generated per method. In keep
                going mode only applies to the first round.
                Defaults to 1.
  /vcsMaxKeepGoingSplits:<n>
                If set to more than 1, activates the keep
                going mode, where after the first round of splitting,
                VCs that timed out are split into <n> pieces and retried
                until we succeed proving them, or there is only one
                assertion on a single path and it timeouts (in which
                case error is reported for that assertion).
                Defaults to 1.
  /vcsKeepGoingTimeout:<n>
                Timeout in seconds for a single theorem prover
                invocation in keep going mode, except for the final
                single-assertion case. Defaults to 1s.
  /vcsFinalAssertTimeout:<n>
                Timeout in seconds for the single last
                assertion in the keep going mode. Defaults to 30s.
  /vcsPathJoinMult:<f>
                If more than one path join at a block, by how much
                multiply the number of paths in that block, to accomodate
                for the fact that the prover will learn something on one
                paths, before proceeding to another. Defaults to 0.8.
  /vcsPathCostMult:<f1>
  /vcsAssumeMult:<f2>
                The cost of a block is
                    (<assert-cost> + <f2>*<assume-cost>) *
                    (1.0 + <f1>*<entering-paths>)
                <f1> defaults to 1.0, <f2> defaults to 0.01.
                The cost of a single assertion or assumption is
                currently always 1.0.
  /vcsPathSplitMult:<f>
                If the best path split of a VC of cost A is into
                VCs of cost B and C, then the split is applied if
                A >= <f>*(B+C), otherwise assertion splitting will be
                applied. Defaults to 0.5 (always do path splitting if
                possible), set to more to do less path splitting
                and more assertion splitting.
  /vcsDumpSplits
                For split #n dump split.n.dot and split.n.bpl.
                Warning: Affects error reporting.
  /vcsCores:<n>
                Try to verify <n> VCs at once. Defaults to 1.
  /vcsLoad:<f>  Sets vcsCores to the machine's ProcessorCount * f,
                rounded to the nearest integer (where 0.0 <= f <= 3.0),
                but never to less than 1.

  ---- Prover options --------------------------------------------------------

  /errorLimit:<num>
                Limit the number of errors produced for each procedure
                (default is 5, some provers may support only 1)
  /timeLimit:<num>
                Limit the number of seconds spent trying to verify
                each procedure
  /rlimit:<num>
                Limit the Z3 resource spent trying to verify each procedure
  /errorTrace:<n>
                0 - no Trace labels in the error output,
                1 (default) - include useful Trace labels in error output,
                2 - include all Trace labels in the error output
  /vcBrackets:<b>
                bracket odd-charactered identifier names with |'s.  <b> is:
                   0 - no (default),
                   1 - yes
  /proverDll:<tp>
                use theorem prover <tp>, where <tp> is either the name of
                a DLL containing the prover interface located in the
                Boogie directory, or a full path to a DLL containing such
                an interface. The default interface shipped is:
                    SMTLib (uses the SMTLib2 format and calls an SMT solver)
  /proverOpt:KEY[=VALUE]
                Provide a prover-specific option (short form /p).
  /proverHelp   Print prover-specific options supported by /proverOpt.
  /proverLog:<file>
                Log input for the theorem prover.  Like filenames
                supplied as arguments to other options, <file> can use the
                following macros:
                    @TIME@    expands to the current time
                    @PREFIX@  expands to the concatenation of strings given
                              by /logPrefix options
                    @FILE@    expands to the last filename specified on the
                              command line
                In addition, /proverLog can also use the macro '@PROC@',
                which causes there to be one prover log file per
                verification condition, and the macro then expands to the
                name of the procedure that the verification condition is for.
  /logPrefix:<str>
                Defines the expansion of the macro '@PREFIX@', which can
                be used in various filenames specified by other options.
  /proverLogAppend
                Append (not overwrite) the specified prover log file
  /proverWarnings
                0 (default) - don't print, 1 - print to stdout,
                2 - print to stderr
  /restartProver
                Restart the prover after each query";
  }
}
