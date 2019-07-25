//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.Specialized;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie {
  public class CommandLineOptionEngine
  {
    public readonly string ToolName;
    public readonly string DescriptiveToolName;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(ToolName != null);
      Contract.Invariant(DescriptiveToolName != null);
      Contract.Invariant(this._environment != null);
      Contract.Invariant(cce.NonNullElements(this._files));
      Contract.Invariant(this._fileTimestamp != null);
    }

    private string/*!*/ _environment = "";

    public string Environment {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._environment;
      }
      set {
        Contract.Requires(value != null);
        this._environment = value;
      }
    }

    private readonly List<string/*!*/>/*!*/ _files = new List<string/*!*/>();

    public IList<string/*!*/>/*!*/ Files {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IList<string>>()));
        Contract.Ensures(Contract.Result<IList<string>>().IsReadOnly);
        return this._files.AsReadOnly();
      }
    }

    public bool HelpRequested = false;
    public bool AttrHelpRequested = false;

    public CommandLineOptionEngine(string toolName, string descriptiveName) {
      Contract.Requires(toolName != null);
      Contract.Requires(descriptiveName != null);
      ToolName = toolName;
      DescriptiveToolName = descriptiveName;
    }

    public virtual string/*!*/ VersionNumber {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return cce.NonNull(cce.NonNull(System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly().Location)).FileVersion);
      }
    }
    public virtual string/*!*/ VersionSuffix {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return " version " + VersionNumber + ", Copyright (c) 2003-2014, Microsoft.";
      }
    }
    public virtual string/*!*/ Version {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return DescriptiveToolName + VersionSuffix;
      }
    }

    private string/*!*/ _fileTimestamp = cce.NonNull(DateTime.Now.ToString("o")).Replace(':', '.');

    public string FileTimestamp {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._fileTimestamp;
      }
      set {
        Contract.Requires(value != null);
        this._fileTimestamp = value;
      }
    }

    public void ExpandFilename(ref string pattern, string logPrefix, string fileTimestamp) {
      if (pattern != null) {
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
    protected virtual bool ParseOption(string name, CommandLineParseState ps) {
      Contract.Requires(name != null);
      Contract.Requires(ps != null);

      switch (name) {
        case "help":
        case "?":
          if (ps.ConfirmArgumentCount(0)) {
            HelpRequested = true;
          }
          return true;
        case "attrHelp":
          if (ps.ConfirmArgumentCount(0)) {
            AttrHelpRequested = true;
          }
          return true;
        default:
          break;
      }
      return false;  // unrecognized option
    }

    protected class CommandLineParseState
    {
      public string s;
      public bool hasColonArgument;
      public readonly string[]/*!*/ args;
      public int i;
      public int nextIndex;
      public bool EncounteredErrors;
      public readonly string ToolName;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(args != null);
        Contract.Invariant(0 <= i && i <= args.Length);
        Contract.Invariant(0 <= nextIndex && nextIndex <= args.Length);
      }


      public CommandLineParseState(string[] args, string toolName) {
        Contract.Requires(args != null);
        Contract.Requires(Contract.ForAll(0, args.Length, i => args[i] != null));
        Contract.Requires(toolName != null);
        Contract.Ensures(this.args == args);
        this.ToolName = toolName;
        this.s = null;  // set later by client
        this.hasColonArgument = false;  // set later by client
        this.args = args;
        this.i = 0;
        this.nextIndex = 0;  // set later by client
        this.EncounteredErrors = false;
      }

      public bool CheckBooleanFlag(string flagName, ref bool flag, bool valueWhenPresent) {
        Contract.Requires(flagName != null);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        bool flagPresent = false;

        if ((s == "/" + flagName || s == "-" + flagName) && ConfirmArgumentCount(0)) {
          flag = valueWhenPresent;
          flagPresent = true;
        }
        return flagPresent;
      }

      public bool CheckBooleanFlag(string flagName, ref bool flag) {
        Contract.Requires(flagName != null);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        return CheckBooleanFlag(flagName, ref flag, true);
      }

      /// <summary>
      /// If there is one argument and it is a non-negative integer, then set "arg" to that number and return "true".
      /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
      /// </summary>
      public bool GetNumericArgument(ref int arg) {
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        return GetNumericArgument(ref arg, a => 0 <= a);
      }

      /// <summary>
      /// If there is one argument and the filtering predicate holds, then set "arg" to that number and return "true".
      /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
      /// </summary>
      public bool GetNumericArgument(ref int arg, Predicate<int> filter) {
        Contract.Requires(filter != null);

        if (this.ConfirmArgumentCount(1)) {
          try {
            Contract.Assume(args[i] != null);
            Contract.Assert(args[i] is string);  // needed to prove args[i].IsPeerConsistent
            int d = Convert.ToInt32(this.args[this.i]);
            if (filter == null || filter(d)) {
              arg = d;
              return true;
            }
          } catch (System.FormatException) {
          } catch (System.OverflowException) {
          }
        } else {
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
      public bool GetNumericArgument(ref int arg, int limit) {
        Contract.Requires(this.i < args.Length);
        Contract.Ensures(Math.Min(arg, 0) <= Contract.ValueAtReturn(out arg) && Contract.ValueAtReturn(out arg) < limit);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        int a = arg;
        if (!GetNumericArgument(ref a)) {
          return false;
        } else if (a < limit) {
          arg = a;
          return true;
        } else {
          Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
          return false;
        }
      }

      /// <summary>
      /// If there is one argument and it is a non-negative real, then set "arg" to that number and return "true".
      /// Otherwise, emit an error message, leave "arg" unchanged, and return "false".
      /// </summary>
      public bool GetNumericArgument(ref double arg) {
        Contract.Ensures(Contract.ValueAtReturn(out arg) >= 0);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        if (this.ConfirmArgumentCount(1)) {
          try {
            Contract.Assume(args[i] != null);
            Contract.Assert(args[i] is string);  // needed to prove args[i].IsPeerConsistent
            double d = Convert.ToDouble(this.args[this.i]);
            if (0 <= d) {
              arg = d;
              return true;
            }
          } catch (System.FormatException) {
          } catch (System.OverflowException) {
          }
        } else {
          return false;
        }
        Error("Invalid argument \"{0}\" to option {1}", args[this.i], this.s);
        return false;
      }

      public bool ConfirmArgumentCount(int argCount) {
        Contract.Requires(0 <= argCount);
        //modifies nextIndex, encounteredErrors, Console.Error.*;
        Contract.Ensures(Contract.Result<bool>() == (!(hasColonArgument && argCount != 1) && !(args.Length < i + argCount)));
        if (hasColonArgument && argCount != 1) {
          Error("\"{0}\" cannot take a colon argument", s);
          nextIndex = args.Length;
          return false;
        } else if (args.Length < i + argCount) {
          Error("\"{0}\" expects {1} argument{2}", s, argCount.ToString(), (string)(argCount == 1 ? "" : "s"));
          nextIndex = args.Length;
          return false;
        } else {
          nextIndex = i + argCount;
          return true;
        }
      }

      public void Error(string message, params string[] args) {
        Contract.Requires(args != null);
        Contract.Requires(message != null);
        //modifies encounteredErrors, Console.Error.*;
        Console.Error.WriteLine("{0}: Error: {1}", ToolName, String.Format(message, args));
        EncounteredErrors = true;
      }
    }

    public virtual void Usage() {
      Console.WriteLine("{0}: usage:  {0} [ option ... ] [ filename ... ]", ToolName);
      Console.WriteLine(@"  where <option> is one of

  ---- General options -------------------------------------------------------

  /help         this message
  /attrHelp     print a message about declaration attributes supported by
                this implementation");
    }

    public virtual void AttributeUsage() {
    }

    /// <summary>
    /// This method is called after all parsing is done, if no parse errors were encountered.
    /// </summary>
    public virtual void ApplyDefaultOptions() {
    }
      
    /// <summary>
    /// Parses the command-line arguments "args" into the global flag variables.  Returns true
    /// if there were no errors.
    /// </summary>
    /// <param name="args">Consumed ("captured" and possibly modified) by the method.</param>
    public bool Parse([Captured] string[]/*!*/ args) {
      Contract.Requires(cce.NonNullElements(args));

      // save the command line options for the log files
      Environment += "Command Line Options: " + args.Concat(" ");
      args = cce.NonNull((string[])args.Clone());  // the operations performed may mutate the array, so make a copy
      var ps = new CommandLineParseState(args, ToolName);

      while (ps.i < args.Length) {
        cce.LoopInvariant(ps.args == args);
        string arg = args[ps.i];
        Contract.Assert(arg != null);
        ps.s = arg.Trim();

        bool isOption = ps.s.StartsWith("-") || ps.s.StartsWith("/");
        int colonIndex = ps.s.IndexOf(':');
        if (0 <= colonIndex && isOption) {
          ps.hasColonArgument = true;
          args[ps.i] = ps.s.Substring(colonIndex + 1);
          ps.s = ps.s.Substring(0, colonIndex);
        } else {
          ps.i++;
          ps.hasColonArgument = false;
        }
        ps.nextIndex = ps.i;

        if (isOption) {
          if (!ParseOption(ps.s.Substring(1), ps)) {
            if (Path.DirectorySeparatorChar == '/' && ps.s.StartsWith("/"))
              this._files.Add(arg);
            else
              ps.Error("unknown switch: {0}", ps.s);
          }
        } else {
          this._files.Add(arg);
        }

        ps.i = ps.nextIndex;
      }

      if (HelpRequested) {
        Usage();
      } else if (AttrHelpRequested) {
        AttributeUsage();
      } else if (ps.EncounteredErrors) {
        Console.WriteLine("Use /help for available options");
      }

      if (ps.EncounteredErrors) {
        return false;
      } else {
        this.ApplyDefaultOptions();
        return true;
      }
    }

  }

  /// <summary>
  /// Boogie command-line options (other tools can subclass this class in order to support a
  /// superset of Boogie's options.
  /// </summary>
  public class CommandLineOptions : CommandLineOptionEngine {

    public CommandLineOptions()
      : base("Boogie", "Boogie program verifier") {
    }

    protected CommandLineOptions(string toolName, string descriptiveName)
      : base(toolName, descriptiveName) {
      Contract.Requires(toolName != null);
      Contract.Requires(descriptiveName != null);
    }

    private static CommandLineOptions clo;
    public static CommandLineOptions/*!*/ Clo
    {
      get { return clo; }
    }

    public static void Install(CommandLineOptions options) {
      Contract.Requires(options != null);
      clo = options;
    }

    public const long Megabyte = 1048576;

    // Flags and arguments

    public bool RunningBoogieFromCommandLine = false;  // "false" means running Boogie from the plug-in

    [ContractInvariantMethod]
    void ObjectInvariant2() {
      Contract.Invariant(LogPrefix != null);
      Contract.Invariant(0 <= PrintUnstructured && PrintUnstructured < 3);  // 0 = print only structured,  1 = both structured and unstructured,  2 = only unstructured
    }

    public int VerifySnapshots = -1;
    public bool VerifySeparately = false;
    public string PrintFile = null;
    public int PrintUnstructured = 0;
    public bool UseBaseNameForFileName = false;
    public int DoomStrategy = -1;
    public bool DoomRestartTP = false;
    public bool PrintDesugarings = false;
    public bool PrintLambdaLifting = false;
    public bool FreeVarLambdaLifting = false;
    public string SimplifyLogFilePath = null;
    public bool PrintInstrumented = false;
    public bool InstrumentWithAsserts = false;
    public string ProverPreamble = null;

    public enum InstrumentationPlaces {
      LoopHeaders,
      Everywhere
    }
    public InstrumentationPlaces InstrumentInfer = InstrumentationPlaces.LoopHeaders;
    public bool PrintWithUniqueASTIds = false;
    private string XmlSinkFilename = null;
    [Peer]
    public XmlSink XmlSink = null;
    public bool Wait = false;
    public bool Trace = false;
    public bool TraceTimes = false;
    public bool TraceProofObligations = false;
    public bool TraceCachingForTesting
    {
      get
      {
        return TraceCaching == 1 || TraceCaching == 3;
      }
    }
    public bool TraceCachingForBenchmarking
    {
      get
      {
        return TraceCaching == 2 || TraceCaching == 3;
      }
    }
    public bool TraceCachingForDebugging
    {
      get
      {
        return TraceCaching == 3;
      }
    }
    internal int TraceCaching = 0;
    public bool NoResolve = false;
    public bool NoTypecheck = false;
    public bool OverlookBoogieTypeErrors = false;
    public bool Verify = true;
    public bool TraceVerify = false;
    public int /*(0:3)*/ ErrorTrace = 1;
    public bool IntraproceduralInfer = true;
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
    public string AbstractHoudini = null;
    public bool UseUnsatCoreForContractInfer = false;
    public bool PrintAssignment = false;
    // TODO(wuestholz): Add documentation for this flag.
    public bool PrintNecessaryAssumes = false;
    public int InlineDepth = -1;
    public bool UseProverEvaluate = false; // Use ProverInterface's Evaluate method, instead of model to get variable values
    public bool UseUncheckedContracts = false;
    public bool SimplifyLogFileAppend = false;
    public bool SoundnessSmokeTest = false;
    public string Z3ExecutablePath = null;
    public string Z3ExecutableName = null;
    public string CVC4ExecutablePath = null;
    public int KInductionDepth = -1;
    public int EnableUnSatCoreExtract = 0;

    private string/*!*/ _logPrefix = "";

    public string LogPrefix {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._logPrefix;
      }
      set {
        Contract.Requires(value != null);
        this._logPrefix = value;
      }
    }

    public bool PrettyPrint = true;

    public enum ProverWarnings {
      None,
      Stdout,
      Stderr
    }
    public ProverWarnings PrintProverWarnings = ProverWarnings.None;
    public int ProverShutdownLimit = 0;

    public enum SubsumptionOption {
      Never,
      NotForQuantifiers,
      Always
    }
    public SubsumptionOption UseSubsumption = SubsumptionOption.Always;

    public bool AlwaysAssumeFreeLoopInvariants = false;

    public enum ShowEnvironment {
      Never,
      DuringPrint,
      Always
    }
    public ShowEnvironment ShowEnv = ShowEnvironment.DuringPrint;
    public bool DontShowLogo = false;
    public bool ShowVerifiedProcedureCount = true;
    [ContractInvariantMethod]
    void ObjectInvariant3() {
      Contract.Invariant(-1 <= LoopFrameConditions && LoopFrameConditions < 3);
      Contract.Invariant(0 <= ModifiesDefault && ModifiesDefault < 7);
      Contract.Invariant((0 <= PrintErrorModel && PrintErrorModel <= 2) || PrintErrorModel == 4);
      Contract.Invariant(0 <= EnhancedErrorMessages && EnhancedErrorMessages < 2);
      Contract.Invariant(0 <= StepsBeforeWidening && StepsBeforeWidening <= 9);
      Contract.Invariant(-1 <= this.bracketIdsInVC && this.bracketIdsInVC <= 1);
      Contract.Invariant(cce.NonNullElements(this.proverOptions));
    }

    public int LoopUnrollCount = -1;  // -1 means don't unroll loops
    public bool SoundLoopUnrolling = false;
    public int LoopFrameConditions = -1;  // -1 means not specified -- this will be replaced by the "implications" section below
    public int ModifiesDefault = 5;
    public bool LocalModifiesChecks = true;
    public bool NoVerifyByDefault = false;
    public enum OwnershipModelOption {
      Standard,
      Experimental,
      Trivial
    }
    public OwnershipModelOption OwnershipModelEncoding = OwnershipModelOption.Standard;
    public int PrintErrorModel = 0;
    public string PrintErrorModelFile = null;
    public string/*?*/ ModelViewFile = null;
    public int EnhancedErrorMessages = 0;
    public string PrintCFGPrefix = null;
    public bool ForceBplErrors = false; // if true, boogie error is shown even if "msg" attribute is present
    public bool UseArrayTheory = false;
    public bool UseSmtOutputFormat = false;
    public bool WeakArrayTheory = false;
    public bool UseLabels = true;
    public bool RunDiagnosticsOnTimeout = false;
    public bool TraceDiagnosticsOnTimeout = false;
    public int TimeLimitPerAssertionInPercent = 10;
    public bool SIBoolControlVC = false;
    public bool MonomorphicArrays {
      get {
        return UseArrayTheory || TypeEncodingMethod == TypeEncoding.Monomorphic;
      }
    }
    public bool ExpandLambdas = true; // not useful from command line, only to be set to false programatically
    public bool DoModSetAnalysis = false;
    public bool UseAbstractInterpretation = true;          // true iff the user want to use abstract interpretation
    private int  /*0..9*/stepsBeforeWidening = 0;           // The number of steps that must be done before applying a widen operator

    public int StepsBeforeWidening
    {
      get
      {
        Contract.Ensures(0 <= Contract.Result<int>() && Contract.Result<int>() <= 9);
        return this.stepsBeforeWidening;
      }
      set
      {
        Contract.Requires(0 <= value && value <= 9);
        this.stepsBeforeWidening = value;
      }
    }

    public string CivlDesugaredFile = null;
    public bool TrustAtomicityTypes = false;
    public bool TrustNonInterference = false;
    public int TrustLayersUpto = -1;
    public int TrustLayersDownto = int.MaxValue;

    public enum VCVariety {
      Structured,
      Block,
      Local,
      BlockNested,
      BlockReach,
      BlockNestedReach,
      Dag,
      DagIterative,
      Doomed,
      Unspecified
    }
    public VCVariety vcVariety = VCVariety.Unspecified;  // will not be Unspecified after command line has been parsed

    public bool RemoveEmptyBlocks = true;
    public bool CoalesceBlocks = true;
    public bool PruneInfeasibleEdges = true;

    [Rep]
    public ProverFactory TheProverFactory;
    public string ProverName;
    [Peer]
    private List<string> proverOptions = new List<string>();

    public IEnumerable<string> ProverOptions
    {
      set
      {
        Contract.Requires(cce.NonNullElements(value));

        this.proverOptions = new List<string>(value);
      }
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<string>>()));

        foreach (string s in this.proverOptions)
          yield return s;
      }
    }

    [Obsolete("use the setter for 'ProverOptions' directly")]
    public void AddProverOption(string option)
    {
      Contract.Requires(option != null);

      this.ProverOptions = this.ProverOptions.Concat1(option);
    }

    [Obsolete("use the setter for 'ProverOptions' directly")]
    public void RemoveAllProverOptions(Predicate<string> match)
    {
      this.ProverOptions = this.ProverOptions.Where(s => !match(s));
    }

    private int bracketIdsInVC = -1;  // -1 - not specified, 0 - no, 1 - yes

    public int BracketIdsInVC {
      get {
        Contract.Ensures(-1 <= Contract.Result<int>() && Contract.Result<int>() <= 1);
        return this.bracketIdsInVC;
      }
      set {
        Contract.Requires(-1 <= value && value <= 1);
        this.bracketIdsInVC = value;
      }
    }

    public bool CausalImplies = false;

    public int SimplifyProverMatchDepth = -1;  // -1 means not specified
    public int ProverKillTime = -1;  // -1 means not specified
    public int Resourcelimit = 0; // default to 0
    public int SmokeTimeout = 10; // default to 10s
    public int ProverCCLimit = 5;
    public bool z3AtFlag = true;
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

    public XmlSink XmlRefuted {
      get {
        if (DebugRefuted)
          return XmlSink;
        else
          return null;
      }
    }
    [ContractInvariantMethod]
    void ObjectInvariant4() {
      Contract.Invariant(cce.NonNullElements(this.z3Options));
      Contract.Invariant(0 <= Z3lets && Z3lets < 4);
    }

    [Peer]
    private List<string> z3Options = new List<string>();

    public IEnumerable<string> Z3Options
    {
      get
      {
        Contract.Ensures(Contract.Result<IEnumerable<string>>() != null);
        foreach (string s in z3Options)
          yield return s;
      }
    }

    public void AddZ3Option(string option)
    {
      Contract.Requires(option != null);
      this.z3Options.Add(option);
    }

    public bool Z3types = false;
    public int Z3lets = 3;  // 0 - none, 1 - only LET TERM, 2 - only LET FORMULA, 3 - (default) any


    // Maximum amount of virtual memory (in bytes) for the prover to use
    //
    // Non-positive number indicates unbounded.
    public long MaxProverMemory = 100 * Megabyte;

    // Minimum number of prover calls before restart
    public int MinNumOfProverCalls = 5;

    public enum PlatformType {
      notSpecified,
      v1,
      v11,
      v2,
      cli1
    }
    public PlatformType TargetPlatform;
    public string TargetPlatformLocation;
    public string StandardLibraryLocation;

    // whether procedure inlining is enabled at call sites.
    public enum Inlining {
      None,
      Assert,
      Assume,
      Spec
    };
    public Inlining ProcedureInlining = Inlining.Assume;
    public bool PrintInlined = false;
    public bool ExtractLoops = false;
    public bool DeterministicExtractLoops = false;
    public string SecureVcGen = null;
    public int StratifiedInlining = 0;
    public string FixedPointEngine = null;
    public int StratifiedInliningOption = 0;
    public bool StratifiedInliningWithoutModels = false; // disable model generation for SI
    public int StratifiedInliningVerbose = 0; // verbosity level
    public int RecursionBound = 500;
    public bool NonUniformUnfolding = false;
    public int StackDepthBound = 0; 
    public string inferLeastForUnsat = null;

    // Inference mode for fixed point engine
    public enum FixedPointInferenceMode {
       Corral,
       OldCorral,
       Flat,
       Procedure,
       Call
    };
    public FixedPointInferenceMode FixedPointMode = FixedPointInferenceMode.Procedure;
		
    public string PrintFixedPoint = null;

    public string PrintConjectures = null;
		
    public bool ExtractLoopsUnrollIrreducible = true; // unroll irreducible loops? (set programmatically)

    public enum TypeEncoding {
      None,
      Predicates,
      Arguments,
      Monomorphic
    };
    public TypeEncoding TypeEncodingMethod = TypeEncoding.Predicates;

    public bool Monomorphize = false;

    public bool ReflectAdd = false;

    public int LiveVariableAnalysis = 1;

    // Static constructor
    static CommandLineOptions() {
      if (System.Type.GetType("Mono.Runtime") == null) {  // MONO
#if !COREFX_SUBSET
        TraceListenerCollection/*!*/ dbl = Debug.Listeners;
        Contract.Assert(dbl != null);
        Contract.Assume(cce.IsPeerConsistent(dbl));  // hangs off static field
        dbl.Add(new DefaultTraceListener());
#endif
      }
    }

    public IEnumerable<string/*!*/> ProcsToCheck {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<string/*!*/>>(), true));
        return this.procsToCheck != null ? this.procsToCheck.AsEnumerable() : null;
      }
    }

    private List<string/*!*/> procsToCheck = null;  // null means "no restriction"
    
    [ContractInvariantMethod]
    void ObjectInvariant5() {
      Contract.Invariant(cce.NonNullElements(this.procsToCheck, true));
      Contract.Invariant(Ai != null);
    }

    public class AiFlags {
      public bool J_Trivial = false;
      public bool J_Intervals = false;
      public bool DebugStatistics = false;
    }
    public readonly AiFlags/*!*/ Ai = new AiFlags();

    public class ConcurrentHoudiniOptions
    {
      public List<string> ProverOptions = new List<string>();
      public int ProverCCLimit = 5;
      public bool DisableLoopInvEntryAssert = false;
      public bool DisableLoopInvMaintainedAssert = false;
      public bool ModifyTopologicalSorting = false;
    }
    public List<ConcurrentHoudiniOptions> Cho = new List<ConcurrentHoudiniOptions>();

    protected override bool ParseOption(string name, CommandLineOptionEngine.CommandLineParseState ps) {
      var args = ps.args;  // convenient synonym
      switch (name) {
        case "infer":
          if (ps.ConfirmArgumentCount(1)) {
            foreach (char c in cce.NonNull(args[ps.i])) {
              switch (c) {
                case 't':
                  Ai.J_Trivial = true;
                  UseAbstractInterpretation = true;
                  break;
                case 'j':
                  Ai.J_Intervals = true;
                  UseAbstractInterpretation = true;
                  break;
                case 's':
                  Ai.DebugStatistics = true;
                  UseAbstractInterpretation = true;
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
                  StepsBeforeWidening = (int)char.GetNumericValue(c);
                  break;
                default:
                  ps.Error("Invalid argument '{0}' to option {1}", c.ToString(), ps.s);
                  break;
              }
            }
          }
          return true;

        case "noinfer":
          if (ps.ConfirmArgumentCount(0)) {
            UseAbstractInterpretation = false;
          }
          return true;

        case "break":
        case "launch":
          if (ps.ConfirmArgumentCount(0)) {
            System.Diagnostics.Debugger.Launch();
          }
          return true;

        case "proc":
          if (this.procsToCheck == null) {
            this.procsToCheck = new List<string/*!*/>();
          }
          if (ps.ConfirmArgumentCount(1)) {
            this.procsToCheck.Add(cce.NonNull(args[ps.i]));
          }
          return true;

        case "xml":
          if (ps.ConfirmArgumentCount(1)) {
            XmlSinkFilename = args[ps.i];
          }
          return true;

        case "print":
          if (ps.ConfirmArgumentCount(1)) {
            PrintFile = args[ps.i];
          }
          return true;

        case "pretty":
          int val = 1;
          if (ps.GetNumericArgument(ref val, 2)) {
            PrettyPrint = val == 1;
          } 
          return true;

        case "CivlDesugaredFile":
          if (ps.ConfirmArgumentCount(1)) {
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
          if (ps.ConfirmArgumentCount(1)) {
            SimplifyLogFilePath = args[ps.i];
          }
          return true;

        case "proverPreamble": 
          if (ps.ConfirmArgumentCount(1))
          {
            ProverPreamble = args[ps.i];
          }
           return true;
          
          case "logPrefix":
          if (ps.ConfirmArgumentCount(1)) {
            string s = cce.NonNull(args[ps.i]);
            LogPrefix += s.Replace('/', '-').Replace('\\', '-');
          }
          return true;

        case "proverShutdownLimit":
          ps.GetNumericArgument(ref ProverShutdownLimit);
          return true;

        case "errorTrace":
          ps.GetNumericArgument(ref ErrorTrace, 3);
          return true;

        case "proverWarnings": {
            int pw = 0;
            if (ps.GetNumericArgument(ref pw, 3)) {
              switch (pw) {
                case 0:
                  PrintProverWarnings = ProverWarnings.None;
                  break;
                case 1:
                  PrintProverWarnings = ProverWarnings.Stdout;
                  break;
                case 2:
                  PrintProverWarnings = ProverWarnings.Stderr;
                  break;
                default: {
                    Contract.Assert(false);
                    throw new cce.UnreachableException();
                  } // postcondition of GetNumericArgument guarantees that we don't get here
              }
            }
            return true;
          }

        case "env": {
            int e = 0;
            if (ps.GetNumericArgument(ref e, 3)) {
              switch (e) {
                case 0:
                  ShowEnv = ShowEnvironment.Never;
                  break;
                case 1:
                  ShowEnv = ShowEnvironment.DuringPrint;
                  break;
                case 2:
                  ShowEnv = ShowEnvironment.Always;
                  break;
                default: {
                    Contract.Assert(false);
                    throw new cce.UnreachableException();
                  } // postcondition of GetNumericArgument guarantees that we don't get here
              }
            }
            return true;
          }

        case "printVerifiedProceduresCount": {
            int n = 0;
            if (ps.GetNumericArgument(ref n, 2)) {
              ShowVerifiedProcedureCount = n != 0;
            }
            return true;
          }

        case "loopUnroll":
          ps.GetNumericArgument(ref LoopUnrollCount);
          return true;

        case "printModel":
          if (ps.ConfirmArgumentCount(1)) {
            switch (args[ps.i]) {
              case "0":
                PrintErrorModel = 0;
                break;
              case "1":
                PrintErrorModel = 1;
                break;
              case "2":
                PrintErrorModel = 2;
                break;
              case "4":
                PrintErrorModel = 4;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }
          return true;

        case "mv":
          if (ps.ConfirmArgumentCount(1)) {
            ModelViewFile = args[ps.i];
          }
          return true;

        case "printModelToFile":
          if (ps.ConfirmArgumentCount(1)) {
            PrintErrorModelFile = args[ps.i];
          }
          return true;

        case "enhancedErrorMessages":
          ps.GetNumericArgument(ref EnhancedErrorMessages, 2);
          return true;

        case "printCFG":
          if (ps.ConfirmArgumentCount(1)) {
            PrintCFGPrefix = args[ps.i];
          }
          return true;

        case "inlineDepth":
          ps.GetNumericArgument(ref InlineDepth);
          return true;

        case "subsumption": {
            int s = 0;
            if (ps.GetNumericArgument(ref s, 3)) {
              switch (s) {
                case 0:
                  UseSubsumption = SubsumptionOption.Never;
                  break;
                case 1:
                  UseSubsumption = SubsumptionOption.NotForQuantifiers;
                  break;
                case 2:
                  UseSubsumption = SubsumptionOption.Always;
                  break;
                default: {
                    Contract.Assert(false);
                    throw new cce.UnreachableException();
                  } // postcondition of GetNumericArgument guarantees that we don't get here
              }
            }
            return true;
          }

        case "liveVariableAnalysis": {
            int lva = 0;
            if (ps.GetNumericArgument(ref lva, 3)) {
              LiveVariableAnalysis = lva;
            }
            return true;
          }

        case "removeEmptyBlocks": {
            int reb = 0;
            if (ps.GetNumericArgument(ref reb, 2)) {
              RemoveEmptyBlocks = reb == 1;
            }
            return true;
          }

        case "coalesceBlocks": {
            int cb = 0;
            if (ps.GetNumericArgument(ref cb, 2)) {
              CoalesceBlocks = cb == 1;
            }
            return true;
          }

        case "noPruneInfeasibleEdges": {
            if (ps.ConfirmArgumentCount(0)) {
              PruneInfeasibleEdges = false;
            }
            return true;
        }

        case "stagedHoudini": {
            if (ps.ConfirmArgumentCount(1)) {
                if(args[ps.i] == "COARSE" ||
                   args[ps.i] == "FINE" ||
                   args[ps.i] == "BALANCED") {
                    StagedHoudini = args[ps.i];
                } else {
                    ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                }
            }
            return true;
        }

        case "stagedHoudiniThreads": {
            ps.GetNumericArgument(ref StagedHoudiniThreads);
            return true;
        }

        case "stagedHoudiniReachabilityAnalysis": {
            if (ps.ConfirmArgumentCount(0)) {
              StagedHoudiniReachabilityAnalysis = true;
            }
            return true;
          }

        case "stagedHoudiniMergeIgnoredAnnotations": {
            if (ps.ConfirmArgumentCount(0)) {
              StagedHoudiniMergeIgnoredAnnotations = true;
            }
            return true;
          }

        case "debugStagedHoudini": {
            if (ps.ConfirmArgumentCount(0)) {
              DebugStagedHoudini = true;
            }
            return true;
          }

        case "variableDependenceIgnore": {
            if (ps.ConfirmArgumentCount(1)) {
              VariableDependenceIgnore = args[ps.i];
            }
            return true;
          }

        case "abstractHoudini":
            {
                if (ps.ConfirmArgumentCount(1))
                {
                    AbstractHoudini = args[ps.i];
                }
                return true;
            }
        case "vc":
          if (ps.ConfirmArgumentCount(1)) {
            switch (args[ps.i]) {
              case "s":
              case "structured":
                vcVariety = VCVariety.Structured;
                break;
              case "b":
              case "block":
                vcVariety = VCVariety.Block;
                break;
              case "l":
              case "local":
                vcVariety = VCVariety.Local;
                break;
              case "n":
              case "nested":
                vcVariety = VCVariety.BlockNested;
                break;
              case "m":
                vcVariety = VCVariety.BlockNestedReach;
                break;
              case "r":
                vcVariety = VCVariety.BlockReach;
                break;
              case "d":
              case "dag":
                vcVariety = VCVariety.Dag;
                break;
              case "i":
                vcVariety = VCVariety.DagIterative;
                break;
              case "doomed":
                vcVariety = VCVariety.Doomed;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }
          return true;

        case "prover":
          if (ps.ConfirmArgumentCount(1)) {
            TheProverFactory = ProverFactory.Load(cce.NonNull(args[ps.i]));
            ProverName = cce.NonNull(args[ps.i]).ToUpper();
          }
          return true;

        case "p":
        case "proverOpt":
          if (ps.ConfirmArgumentCount(1)) {
            ProverOptions = ProverOptions.Concat1(cce.NonNull(args[ps.i]));
          }
          return true;

        case "DoomStrategy":
          ps.GetNumericArgument(ref DoomStrategy);
          return true;

        case "DoomRestartTP":
          if (ps.ConfirmArgumentCount(0)) {
            DoomRestartTP = true;
          }
          return true;

        case "extractLoops":
          if (ps.ConfirmArgumentCount(0)) {
            ExtractLoops = true;
          }
          return true;  

        case "deterministicExtractLoops":
          if (ps.ConfirmArgumentCount(0)) {
            DeterministicExtractLoops = true;
          }
          return true;

        case "inline":
          if (ps.ConfirmArgumentCount(1)) {
            switch (args[ps.i]) {
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
        case "stratifiedInline":
          if (ps.ConfirmArgumentCount(1)) {
            switch (args[ps.i]) {
              case "0":
                StratifiedInlining = 0;
                break;
              case "1":
                StratifiedInlining = 1;
                break;
              default:
                StratifiedInlining = Int32.Parse(cce.NonNull(args[ps.i]));
                //ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }
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
        case "siVerbose":
          if (ps.ConfirmArgumentCount(1)) {
            StratifiedInliningVerbose = Int32.Parse(cce.NonNull(args[ps.i]));
          }
          return true;
        case "recursionBound":
          if (ps.ConfirmArgumentCount(1)) {
            RecursionBound = Int32.Parse(cce.NonNull(args[ps.i]));
          }
          return true;
        case "enableUnSatCoreExtraction":
            if (ps.ConfirmArgumentCount(1))
            {
                EnableUnSatCoreExtract = Int32.Parse(cce.NonNull(args[ps.i]));
            }
            return true;
        case "stackDepthBound":
          if (ps.ConfirmArgumentCount(1))
          {
              StackDepthBound = Int32.Parse(cce.NonNull(args[ps.i]));
          }
          return true;
        case "stratifiedInlineOption":
          if (ps.ConfirmArgumentCount(1)) {
            StratifiedInliningOption = Int32.Parse(cce.NonNull(args[ps.i]));
          }
          return true;

        case "inferLeastForUnsat":
          if (ps.ConfirmArgumentCount(1)) {
            inferLeastForUnsat = args[ps.i];
          }
          return true;

        case "typeEncoding":
          if (ps.ConfirmArgumentCount(1)) {
            switch (args[ps.i]) {
              case "n":
              case "none":
                TypeEncodingMethod = TypeEncoding.None;
                break;
              case "p":
              case "predicates":
                TypeEncodingMethod = TypeEncoding.Predicates;
                break;
              case "a":
              case "arguments":
                TypeEncodingMethod = TypeEncoding.Arguments;
                break;
              case "m":
              case "monomorphic":
                TypeEncodingMethod = TypeEncoding.Monomorphic;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }
          return true;

        case "instrumentInfer":
          if (ps.ConfirmArgumentCount(1)) {
            switch (args[ps.i]) {
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
          if (ps.ConfirmArgumentCount(0)) {
            ConcurrentHoudini = true;
          }
          return true;

        case "modifyTopologicalSorting":
          if (ps.ConfirmArgumentCount(0)) {
            ModifyTopologicalSorting = true;
          }
          return true;

        case "debugConcurrentHoudini":
          if (ps.ConfirmArgumentCount(0)) {
            DebugConcurrentHoudini = true;
          }
          return true;

        case "vcBrackets":
          ps.GetNumericArgument(ref bracketIdsInVC, 2);
          return true;

        case "proverMemoryLimit": {
            int d = 0;
            if (ps.GetNumericArgument(ref d)) {
              MaxProverMemory = d * Megabyte;
            }
            return true;
          }

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
          if (ps.GetNumericArgument(ref load)) {
            if (3.0 <= load) {
              ps.Error("surprisingly high load specified; got {0}, expected nothing above 3.0", load.ToString());
              load = 3.0;
            }
            int p = (int)Math.Round(System.Environment.ProcessorCount * load);
            VcsCores = p < 1 ? 1 : p;
          }
          return true;

        case "simplifyMatchDepth":
          ps.GetNumericArgument(ref SimplifyProverMatchDepth);
          return true;

        case "timeLimit":
          ps.GetNumericArgument(ref ProverKillTime);
          return true;

        case "rlimit":
          ps.GetNumericArgument(ref Resourcelimit);
          return true;

        case "timeLimitPerAssertionInPercent":
          ps.GetNumericArgument(ref TimeLimitPerAssertionInPercent, a => 0 < a);
          return true;

        case "smokeTimeout":
          ps.GetNumericArgument(ref SmokeTimeout);
          return true;

        case "errorLimit":
          ps.GetNumericArgument(ref ProverCCLimit);
          return true;

        case "verifySnapshots":
          ps.GetNumericArgument(ref VerifySnapshots, 4);
          return true;

        case "traceCaching":
          ps.GetNumericArgument(ref TraceCaching, 4);
          return true;
		
		case "useSmtOutputFormat": {
		  if (ps.ConfirmArgumentCount(0)) {
			UseSmtOutputFormat = true;
		  }
	      return true;
		}        
        case "z3opt":
          if (ps.ConfirmArgumentCount(1)) {
            AddZ3Option(cce.NonNull(args[ps.i]));
          }
          return true;

        case "z3lets":
          ps.GetNumericArgument(ref Z3lets, 4);
          return true;

        case "platform":
          if (ps.ConfirmArgumentCount(1)) {
            StringCollection platformOptions = this.ParseNamedArgumentList(args[ps.i]);
            if (platformOptions != null && platformOptions.Count > 0) {
              try {
                this.TargetPlatform = (PlatformType)cce.NonNull(Enum.Parse(typeof(PlatformType), cce.NonNull(platformOptions[0])));
              } catch {
                ps.Error("Bad /platform type '{0}'", platformOptions[0]);
                break;
              }
              if (platformOptions.Count > 1) {
                this.TargetPlatformLocation = platformOptions[1];
                if (!Directory.Exists(platformOptions[1])) {
                  ps.Error("/platform directory '{0}' does not exist", platformOptions[1]);
                  break;
                }
              }
            }
          }
          return true;

        case "z3exe":
          if (ps.ConfirmArgumentCount(1)) {
            Z3ExecutablePath = args[ps.i];
          }
          return true;
         // This sets name of z3 binary boogie binary directory, not path
        case "z3name":
          if (ps.ConfirmArgumentCount(1))
          {
              Z3ExecutableName = args[ps.i];
          }
          return true;

        case "cvc4exe":
			if (ps.ConfirmArgumentCount(1)) {
				CVC4ExecutablePath = args[ps.i];
			}
			return true;

        case "kInductionDepth":
          ps.GetNumericArgument(ref KInductionDepth);
          return true;

        default:
          bool optionValue = false;
          if (ps.CheckBooleanFlag("printUnstructured", ref optionValue)) {
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
              ps.CheckBooleanFlag("nologo", ref DontShowLogo) ||
              ps.CheckBooleanFlag("proverLogAppend", ref SimplifyLogFileAppend) ||
              ps.CheckBooleanFlag("soundLoopUnrolling", ref SoundLoopUnrolling) ||
              ps.CheckBooleanFlag("checkInfer", ref InstrumentWithAsserts) ||
              ps.CheckBooleanFlag("interprocInfer", ref IntraproceduralInfer, false) ||
              ps.CheckBooleanFlag("restartProver", ref RestartProverPerVC) ||
              ps.CheckBooleanFlag("printInlined", ref PrintInlined) ||
              ps.CheckBooleanFlag("smoke", ref SoundnessSmokeTest) ||
              ps.CheckBooleanFlag("vcsDumpSplits", ref VcsDumpSplits) ||
              ps.CheckBooleanFlag("dbgRefuted", ref DebugRefuted) ||
              ps.CheckBooleanFlag("causalImplies", ref CausalImplies) ||
              ps.CheckBooleanFlag("reflectAdd", ref ReflectAdd) ||
              ps.CheckBooleanFlag("z3types", ref Z3types) ||
              ps.CheckBooleanFlag("z3multipleErrors", ref z3AtFlag, false) ||
              ps.CheckBooleanFlag("monomorphize", ref Monomorphize) ||
              ps.CheckBooleanFlag("useArrayTheory", ref UseArrayTheory) ||
              ps.CheckBooleanFlag("weakArrayTheory", ref WeakArrayTheory) || 
              ps.CheckBooleanFlag("doModSetAnalysis", ref DoModSetAnalysis) ||
              ps.CheckBooleanFlag("doNotUseLabels", ref UseLabels, false) ||
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
              ps.CheckBooleanFlag("nonUniformUnfolding", ref NonUniformUnfolding) ||
              ps.CheckBooleanFlag("deterministicExtractLoops", ref DeterministicExtractLoops) ||
              ps.CheckBooleanFlag("verifySeparately", ref VerifySeparately) ||
              ps.CheckBooleanFlag("trustAtomicityTypes", ref TrustAtomicityTypes) ||
              ps.CheckBooleanFlag("trustNonInterference", ref TrustNonInterference) ||
              ps.CheckBooleanFlag("useBaseNameForFileName", ref UseBaseNameForFileName) ||
              ps.CheckBooleanFlag("freeVarLambdaLifting", ref FreeVarLambdaLifting)
              ) {
            // one of the boolean flags matched
            return true;
          }
          break;
      }

      return base.ParseOption(name, ps);  // defer to superclass
    }

    public override void ApplyDefaultOptions() {
      Contract.Ensures(TheProverFactory != null);
      Contract.Ensures(vcVariety != VCVariety.Unspecified);

      base.ApplyDefaultOptions();

      // expand macros in filenames, now that LogPrefix is fully determined
      ExpandFilename(ref XmlSinkFilename, LogPrefix, FileTimestamp);
      ExpandFilename(ref PrintFile, LogPrefix, FileTimestamp);
      ExpandFilename(ref SimplifyLogFilePath, LogPrefix, FileTimestamp);
      ExpandFilename(ref PrintErrorModelFile, LogPrefix, FileTimestamp);

      Contract.Assume(XmlSink == null);  // XmlSink is to be set here
      if (XmlSinkFilename != null) {
        XmlSink = new XmlSink(XmlSinkFilename);
      }

      if (TheProverFactory == null) {
        TheProverFactory = ProverFactory.Load("SMTLib");
        ProverName = "SMTLib".ToUpper();
      }

      var proverOpts = TheProverFactory.BlankProverOptions();
      proverOpts.Parse(ProverOptions);
      if (!TheProverFactory.SupportsLabels(proverOpts)) {
        UseLabels = false;
      }

      if (vcVariety == VCVariety.Unspecified) {
        vcVariety = TheProverFactory.DefaultVCVariety;
      }

      if (UseArrayTheory) {
        Monomorphize = true;
      }

      if (inferLeastForUnsat != null) {
        StratifiedInlining = 1;
      }

      if (StratifiedInlining > 0) {
        TypeEncodingMethod = TypeEncoding.Monomorphic;
        UseArrayTheory = true;
        UseAbstractInterpretation = false;
        MaxProverMemory = 0; // no max: avoids restarts
        if (ProverName == "Z3API" || ProverName == "SMTLIB") {
          ProverCCLimit = 1;
        }
        if (UseProverEvaluate)
            StratifiedInliningWithoutModels = true;
      }

      if (Trace) {
        BoogieDebug.DoPrinting = true;  // reuse the -trace option for debug printing
      }
    }



    public bool UserWantsToCheckRoutine(string methodFullname) {
      Contract.Requires(methodFullname != null);
      if (ProcsToCheck == null) {
        // no preference
        return true;
      }
      return ProcsToCheck.Any(s => Regex.IsMatch(methodFullname, "^" + Regex.Escape(s).Replace(@"\*", ".*") + "$"));
    }

    public virtual StringCollection ParseNamedArgumentList(string argList) {
      if (argList == null || argList.Length == 0)
        return null;
      StringCollection result = new StringCollection();
      int i = 0;
      for (int n = argList.Length; i < n; ) {
        cce.LoopInvariant(0 <= i);
        int separatorIndex = this.GetArgumentSeparatorIndex(argList, i);
        if (separatorIndex > i) {
          result.Add(argList.Substring(i, separatorIndex - i));
          i = separatorIndex + 1;
          continue;
        }
        result.Add(argList.Substring(i));
        break;
      }
      return result;
    }
    public int GetArgumentSeparatorIndex(string argList, int startIndex) {
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

    public override void AttributeUsage() {
      Console.WriteLine(
@"Boogie: The following attributes are supported by this implementation.

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
       Assign a positive priority 'N' to an implementation to control the order
       in which implementations are verified (default: N = 1).

     {:id <string>}
       Assign a unique ID to an implementation to be used for verification
       result caching (default: ""<impl. name>:0"").

     {:timeLimit N}
       Set the time limit for a given implementation.

     {:rlimit N}
       Set the Z3 resource limit for a given implementation.

  ---- On functions ----------------------------------------------------------

     {:builtin ""spec""}
     {:bvbuiltin ""spec""}
       Rewrite the function to built-in prover function symbol 'fn'.

     {:inline}
     {:inline true}
       Expand function according to its definition before going to the prover.

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

  ---- The end ---------------------------------------------------------------
");
    }

    public override void Usage() {
      Console.WriteLine(@"
  /nologo       suppress printing of version number, copyright message
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

  /proc:<p>      : Only check procedures matched by pattern <p>. This option
                   may be specified multiple times to match multiple patterns.
                   The pattern <p> matches the whole procedure name (i.e.
                   pattern ""foo"" will only match a procedure called foo and
                   not fooBar). The pattern <p> may contain * wildcards which
                   match any character zero or more times. For example the
                   pattern ""ab*d"" would match abd, abcd and abccd but not
                   Aabd nor abdD. The pattern ""*ab*d*"" would match abd,
                   abcd, abccd, Abd and abdD.
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
                2 - print Z3's error model plus reverse mappings
                4 - print Z3's error model in a more human readable way
  /printModelToFile:<file>
                print model to <file> instead of console
  /mv:<file>    Specify file where to save the model in BVD format
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
                The default is /infer:i"
        // This is not 100% true, as the /infer ALWAYS creates
        // a multilattice, whereas if nothing is specified then
        // intervals are isntantiated WITHOUT being embedded in
        // a multilattice
                                          + @"
                   <flags> are as follows (missing <flags> means all)
                   i = intervals
                   c = constant propagation
                   d = dynamic type
                   n = nullness
                   p = polyhedra for linear inequalities
                   t = trivial bottom/top lattice (cannot be combined with
                       other domains)
                   j = stronger intervals (cannot be combined with other
                       domains)
                or the following (which denote options, not domains):
                   s = debug statistics
                0..9 = number of iterations before applying a widen (default=0)
  /noinfer      turn off the default inference, and overrides the /infer
                switch on its left
  /checkInfer   instrument inferred invariants as asserts to be checked by
                theorem prover
  /interprocInfer
                perform interprocedural inference (deprecated, not supported)
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
  /log[:method] Print debug output during translation

  /break        launch and break into debugger

  ---- CIVL options ----------------------------------------------------------

  /trustAtomicityTypes
                do not verify atomic action declarations
  /trustNonInterference
                do not perform noninterference checks
  /trustLayersUpto:<n>
                do not verify layers <n> and below
  /trustLayersDownto:<n>
                do not verify layers <n> and above
  /CivlDesugaredFile:<file>
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
  /vc:<variety> n = nested block (default for /prover:Simplify),
                m = nested block reach,
                b = flat block, r = flat block reach,
                s = structured, l = local,
                d = dag (default, except with /prover:Simplify)
                doomed = doomed
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
  /lazyInline:1
                Use the lazy inlining algorithm
  /stratifiedInline:1
                Use the stratified inlining algorithm
  /fixedPointEngine:<engine>
                Use the specified fixed point engine for inference
  /recursionBound:<n>
                Set the recursion bound for stratified inlining to
                be n (default 500)
  /inferLeastForUnsat:<str>
                Infer the least number of constants (whose names
                are prefixed by <str>) that need to be set to
                true for the program to be correct. This turns
                on stratified inlining.
  /smoke        Soundness Smoke Test: try to stick assert false; in some
                places in the BPL and see if we can still prove it
  /smokeTimeout:<n>
                Timeout, in seconds, for a single theorem prover
                invocation during smoke test, defaults to 10.
  /causalImplies
                Translate Boogie's A ==> B into prover's A ==> A && B.
  /typeEncoding:<m>
                how to encode types when sending VC to theorem prover
                   n = none (unsound)
                   p = predicates (default)
                   a = arguments
                   m = monomorphic
  /monomorphize   
                Do not abstract map types in the encoding (this is an
                experimental feature that will not do the right thing if
                the program uses polymorphism)
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
                   0 - no (default with non-/prover:Simplify),
                   1 - yes (default with /prover:Simplify)
  /prover:<tp>  use theorem prover <tp>, where <tp> is either the name of
                a DLL containing the prover interface located in the
                Boogie directory, or a full path to a DLL containing such
                an interface. The standard interfaces shipped include:
                    SMTLib (default, uses the SMTLib2 format and calls Z3)
                    Z3 (uses Z3 with the Simplify format)
                    Simplify
                    ContractInference (uses Z3)
                    Z3api (Z3 using Managed .NET API)
  /proverOpt:KEY[=VALUE]
                Provide a prover-specific option (short form /p).
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
  /proverMemoryLimit:<num>
                Limit on the virtual memory for prover before
                restart in MB (default:100MB)
  /restartProver
                Restart the prover after each query
  /proverShutdownLimit<num>
                Time between closing the stream to the prover and
                killing the prover process (default: 0s)
  /platform:<ptype>,<location>
                ptype = v11,v2,cli1
                location = platform libraries directory

  Simplify specific options:
  /simplifyMatchDepth:<num>
                Set Simplify prover's matching depth limit

  Z3 specific options:
  /z3opt:<arg>  specify additional Z3 options
  /z3multipleErrors
                report multiple counterexamples for each error
  /useArrayTheory
                use Z3's native theory (as opposed to axioms).  Currently
                implies /monomorphize.
  /useSmtOutputFormat
                Z3 outputs a model in the SMTLIB2 format.
  /z3types      generate multi-sorted VC that make use of Z3 types
  /z3lets:<n>   0 - no LETs, 1 - only LET TERM, 2 - only LET FORMULA,
                3 - (default) any
  /z3exe:<path>
                path to Z3 executable

  CVC4 specific options:
  /cvc4exe:<path>
                path to CVC4 executable
");
    }
  }
}
