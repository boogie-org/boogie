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
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie {
  public class CommandLineOptions {
    public static string/*!*/ VersionNumber {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return cce.NonNull(cce.NonNull(System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly().Location)).FileVersion);
      }
    }
    public const string ToolNameBoogie = "Boogie program verifier";
    public const string ToolNameSpecSharp = "Spec# program verifier";
    public const string ToolNameDafny = "Dafny program verifier";
    public static string/*!*/ VersionSuffix {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return " version " + VersionNumber + ", Copyright (c) 2003-2010, Microsoft.";
      }
    }
    public string/*!*/ InputFileExtension {
      set {
        Contract.Requires(value != null);
        //modifies _toolname, _version;
        switch (value) {
          case ".bpl":
            _toolname = ToolNameBoogie;
            break;
          case ".dfy":
            _toolname = ToolNameDafny;
            break;
          default:
            _toolname = ToolNameSpecSharp;
            break;
        }
        _version = _toolname + VersionSuffix;
      }
    }
    string/*!*/ _toolname = ToolNameBoogie;
    string/*!*/ _version = ToolNameBoogie + VersionSuffix;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(_toolname != null);
      Contract.Invariant(_version != null);
      Contract.Invariant(Clo != null);
      Contract.Invariant(Environment != null);
      Contract.Invariant(FileName != null);
      Contract.Invariant(cce.NonNullElements(Files));
      Contract.Invariant(cce.NonNullElements(ContractAssemblies));
      Contract.Invariant(FileTimestamp != null);
    }

    public string/*!*/ ToolName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return _toolname;
      }
    }
    public string/*!*/ Version {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return _version;
      }
    }

    public static CommandLineOptions/*!*/ Clo = new CommandLineOptions();  // singleton to access all global data

    public string/*!*/ Environment = "";
    public string/*!*/ FileName = "unknown";

    public const long Megabyte = 1048576;

    // Flags and arguments

    public bool RunningBoogieFromCommandLine = false;  // "false" means running Boogie from the plug-in
    public bool RunningBoogieOnSsc = true; // "true" means running Boogie on ssc input while false means running it on bpl input

    public bool AttrHelpRequested = false;

    [Peer]
    public List<string/*!*/>/*!*/ Files = new List<string/*!*/>();
    public List<string/*!*/>/*!*/ ContractAssemblies = new List<string/*!*/>();

    public string/*!*/ FileTimestamp = cce.NonNull(DateTime.Now.ToString("o")).Replace(':', '.');
    public void ExpandFilename(ref string pattern) {
      if (pattern != null) {
        pattern = pattern.Replace("@PREFIX@", LogPrefix).Replace("@TIME@", FileTimestamp);
        string fn = Files.Count == 0 ? "" : Files[Files.Count - 1];
        fn = fn.Replace('/', '-').Replace('\\', '-');
        pattern = pattern.Replace("@FILE@", fn);
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant2() {
      Contract.Invariant(LogPrefix != null);
      Contract.Invariant(0 <= PrintUnstructured && PrintUnstructured < 3);  // 0 = print only structured,  1 = both structured and unstructured,  2 = only unstructured

    }

    public string PrintFile = null;
    public int PrintUnstructured = 0;

    public bool PrintDesugarings = false;
    public string SimplifyLogFilePath = null;
    public string/*!*/ LogPrefix = "";
    public bool PrintInstrumented = false;
    public bool InstrumentWithAsserts = false;
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
    public bool NoResolve = false;
    public bool NoTypecheck = false;
    public bool OverlookBoogieTypeErrors = false;
    public bool Verify = true;
    public bool TraceVerify = false;
    public int /*(0:3)*/ ErrorTrace = 1;
    public bool IntraproceduralInfer = true;
    public bool ContractInfer = false;
    public bool UseUncheckedContracts = false;
    public bool SimplifyLogFileAppend = false;
    public bool SoundnessSmokeTest = false;

    private bool noConsistencyChecks = false;
    public bool NoConsistencyChecks {
      get {
        return !Verify ? true : noConsistencyChecks;
      }
      set
        //modifies noConsistencyChecks;
        {
        noConsistencyChecks = value;
      }
    }

    public string DafnyPrelude = null;
    public string DafnyPrintFile = null;
    public bool Compile = true;

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
    [ContractInvariantMethod]
    void ObjectInvariant3() {
      Contract.Invariant(0 <= CheckingLevel && CheckingLevel < 3);
      Contract.Invariant(0 <= OrderStrength && OrderStrength < 2);
      Contract.Invariant(0 <= SummationAxiomStrength && SummationAxiomStrength < 2);
      Contract.Invariant(0 <= InductiveMinMax && InductiveMinMax < 6);
      Contract.Invariant(0 <= FCOStrength && FCOStrength < 6);
      Contract.Invariant(-1 <= LoopFrameConditions && LoopFrameConditions < 3);
      Contract.Invariant(0 <= ModifiesDefault && ModifiesDefault < 7);
      Contract.Invariant((0 <= PrintErrorModel && PrintErrorModel <= 2) || PrintErrorModel == 4);
      Contract.Invariant(0 <= EnhancedErrorMessages && EnhancedErrorMessages < 2);
      Contract.Invariant(0 <= StepsBeforeWidening && StepsBeforeWidening <= 9);
      Contract.Invariant(-1 <= BracketIdsInVC && BracketIdsInVC <= 1);
      Contract.Invariant(cce.NonNullElements(ProverOptions));






    }

    public int CheckingLevel = 2;
    public enum Methodology {
      Boogie,
      VisibleState
    }
    public Methodology MethodologySelection = Methodology.Boogie;
    public int OrderStrength = 0;
    public bool UseArithDistributionAxioms = false;
    public int SummationAxiomStrength = 1;
    public int InductiveMinMax = 0;
    public int FCOStrength = 5;
    public int LoopUnrollCount = -1;  // -1 means don't unroll loops
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
    public bool ForceBplErrors = false; // if true, boogie error is shown even if "msg" attribute is present
    public enum BvHandling {
      None,
      Z3Native,
      ToInt
    }
    public BvHandling Bitvectors = BvHandling.Z3Native;
    public bool UseArrayTheory = false;
    public bool MonomorphicArrays {
      get {
        return UseArrayTheory || TypeEncodingMethod == TypeEncoding.Monomorphic;
      }
    }
    public bool ExpandLambdas = true; // not useful from command line, only to be set to false programatically
    public bool DoModSetAnalysis = false;
    public bool UseAbstractInterpretation = true;          // true iff the user want to use abstract interpretation
    public int  /*0..9*/StepsBeforeWidening = 0;           // The number of steps that must be done before applying a widen operator


    public enum VCVariety {
      Structured,
      Block,
      Local,
      BlockNested,
      BlockReach,
      BlockNestedReach,
      Dag,
      Doomed,
      Unspecified
    }
    public VCVariety vcVariety = VCVariety.Unspecified;  // will not be Unspecified after command line has been parsed
    public bool useDoomDebug = false; // Will use doomed analysis to search for errors if set

    public bool RemoveEmptyBlocks = true;
    public bool CoalesceBlocks = true;

    [Rep]
    public ProverFactory TheProverFactory;
    public string ProverName;
    [Peer]
    public List<string/*!*/>/*!*/ ProverOptions = new List<string/*!*/>();

    public int BracketIdsInVC = -1;  // -1 - not specified, 0 - no, 1 - yes
    public bool CausalImplies = false;

    public int SimplifyProverMatchDepth = -1;  // -1 means not specified
    public int ProverKillTime = -1;  // -1 means not specified
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

    public bool houdiniEnabled = false;
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
      Contract.Invariant(cce.NonNullElements(Z3Options));
      Contract.Invariant(0 <= Z3lets && Z3lets < 4);
    }

    [Peer]
    public List<string/*!*/>/*!*/ Z3Options = new List<string/*!*/>();
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
    public int LazyInlining = 0;
    public int StratifiedInlining = 0;
    public int StratifiedInliningOption = 0;
    public bool UseUnsatCoreForInlining = false;
    public int RecursionBound = 500;
    public string inferLeastForUnsat = null;
    public string CoverageReporterPath = null;
    public Process coverageReporter = null; // used internally for debugging

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
        TraceListenerCollection/*!*/ dbl = Debug.Listeners;
        Contract.Assert(dbl != null);
        Contract.Assume(cce.IsPeerConsistent(dbl));  // hangs off static field
#if WHIDBEY
        dbl.Add(new ConsoleTraceListener());
#else
        dbl.Add(new DefaultTraceListener());
#endif
      }
    }

    private string methodToLog = null;
    private string methodToBreakOn = null;
    [ContractInvariantMethod]
    void ObjectInvariant5() {
      Contract.Invariant(cce.NonNullElements(procsToCheck, true));
      Contract.Invariant(cce.NonNullElements(methodsToTranslateClass, true));
      Contract.Invariant(cce.NonNullElements(methodsToTranslateClassQualified, true));
      Contract.Invariant(cce.NonNullElements(methodsToTranslateExclude));
      Contract.Invariant(cce.NonNullElements(methodsToTranslateFile, true));
      Contract.Invariant(cce.NonNullElements(methodsToTranslateMethod, true));
      Contract.Invariant(cce.NonNullElements(methodsToTranslateMethodQualified, true));
      Contract.Invariant(cce.NonNullElements(methodsToTranslateSubstring, true));
      Contract.Invariant(Ai != null);
      Contract.Invariant(houdiniFlags != null);
    }

    [Rep]
    private List<string/*!*/> procsToCheck = null;  // null means "no restriction"
    [Rep]
    private List<string/*!*/> methodsToTranslateSubstring = null;  // null means "no restriction"
    [Rep]
    private List<string/*!*/> methodsToTranslateMethod = null;  // null means "no restriction"
    [Rep]
    private List<string/*!*/> methodsToTranslateMethodQualified = null;  // null means "no restriction"
    [Rep]
    private List<string/*!*/> methodsToTranslateClass = null;  // null means "no restriction"
    [Rep]
    private List<string/*!*/> methodsToTranslateClassQualified = null;  // null means "no restriction"
    [Rep]
    private List<string/*!*/> methodsToTranslateFile = null;  // null means "no restriction"
    [Rep]
    private List<string/*!*/>/*!*/ methodsToTranslateExclude = new List<string/*!*/>();

    public class AiFlags {
      public bool Intervals = false;
      public bool Constant = false;
      public bool DynamicType = false;
      public bool Nullness = false;
      public bool Polyhedra = false;
      public bool DebugStatistics = false;

      public bool AnySet {
        get {
          return Intervals
              || Constant
              || DynamicType
              || Nullness
              || Polyhedra;
        }
      }
    }
    public AiFlags/*!*/ Ai = new AiFlags();

    public class HoudiniFlags {
      public bool continueAtError = false;
      public bool incremental = false;
    }

    public HoudiniFlags/*!*/ houdiniFlags = new HoudiniFlags();

    [Verify(false)]
    public CommandLineOptions() {
      // this is just to suppress verification. 
    }


    /// <summary>
    /// Parses the command-line arguments "args" into the global flag variables.  The possible result
    /// values are:
    /// -2: an error occurred and help was requested
    /// -1: no error occurred and help was requested
    ///  1: no error occurred and help was not requested
    ///  2: an error occurred and help was not requested
    /// </summary>
    /// <param name="args">Consumed ("captured" and possibly modified) by the method.</param>
    [Verify(false)]
    public int Parse([Captured] string[]/*!*/ args) {
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(TheProverFactory != null);
      Contract.Ensures(vcVariety != VCVariety.Unspecified);
      Contract.Ensures(-2 <= Contract.Result<int>() && Contract.Result<int>() <= 2 && Contract.Result<int>() != 0);
      // save the command line options for the log files
      Environment += "Command Line Options:";
      foreach (string s in args)
        Environment += " " + s;
      args = cce.NonNull((string[])args.Clone());  // the operations performed may mutate the array, so make a copy
      CommandLineParseState/*!*/ ps = new CommandLineParseState(args);
      Contract.Assert(ps != null);
      int res = 1;  // the result value

      while (ps.i < args.Length) {
        cce.LoopInvariant(cce.IsPeerConsistent(ps));
        cce.LoopInvariant(ps.args == args);
        ps.s = args[ps.i];
        Contract.Assert(ps.s != null);
        ps.s = ps.s.Trim();

        int colonIndex = ps.s.IndexOf(':');
        if (colonIndex >= 0 && (ps.s.StartsWith("-") || ps.s.StartsWith("/"))) {
          ps.hasColonArgument = true;
          args[ps.i] = ps.s.Substring(colonIndex + 1);
          ps.s = ps.s.Substring(0, colonIndex);
        } else {
          cce.BeginExpose(ps);
          {
            ps.i++;
          }
          cce.EndExpose();
          ps.hasColonArgument = false;
        }
        ps.nextIndex = ps.i;


        switch (ps.s) {
          case "-help":
          case "/help":
          case "-?":
          case "/?":
            if (ps.ConfirmArgumentCount(0)) {
              res = -1;  // help requested
            }
            break;

          case "-attrHelp":
          case "/attrHelp":
            if (ps.ConfirmArgumentCount(0)) {
              AttrHelpRequested = true;
            }
            break;

          case "-infer":
          case "/infer":
            if (ps.ConfirmArgumentCount(1)) {
              foreach (char c in cce.NonNull(args[ps.i])) {
                switch (c) {
                  case 'i':
                    Ai.Intervals = true;
                    UseAbstractInterpretation = true;
                    break;
                  case 'c':
                    Ai.Constant = true;
                    UseAbstractInterpretation = true;
                    break;
                  case 'd':
                    Ai.DynamicType = true;
                    UseAbstractInterpretation = true;
                    break;
                  case 'n':
                    Ai.Nullness = true;
                    UseAbstractInterpretation = true;
                    break;
                  case 'p':
                    Ai.Polyhedra = true;
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
            break;

          case "-noinfer":
          case "/noinfer":
            if (ps.ConfirmArgumentCount(0)) {
              UseAbstractInterpretation = false;
            }
            break;

          case "-log":
          case "/log":
            if (ps.hasColonArgument) {
              methodToLog = args[ps.i];
              ps.nextIndex = ps.i + 1;
            } else {
              methodToLog = "*";
            }
            break;

          case "-logInfer":
          case "/logInfer":
            Microsoft.AbstractInterpretationFramework.Lattice.LogSwitch = true;
            break;

          case "-break":
          case "/break":
            if (ps.hasColonArgument) {
              methodToBreakOn = args[ps.i];
              ps.nextIndex = ps.i + 1;
            } else {
              System.Diagnostics.Debugger.Break();
            }
            break;

          case "-launch":
          case "/launch":
            System.Diagnostics.Debugger.Launch();
            break;

          case "-proc":
          case "/proc":
            if (procsToCheck == null) {
              procsToCheck = new List<string/*!*/>();
            }
            if (ps.ConfirmArgumentCount(1)) {
              procsToCheck.Add(cce.NonNull(args[ps.i]));
            }
            break;

          case "-translate":
          case "/translate":
            if (methodsToTranslateSubstring == null) {
              methodsToTranslateSubstring = new List<string/*!*/>();
            }
            if (ps.ConfirmArgumentCount(1)) {
              methodsToTranslateSubstring.Add(cce.NonNull(args[ps.i]));
            }
            break;

          case "-trMethod":
          case "/trMethod":
            if (ps.ConfirmArgumentCount(1)) {
              string m = cce.NonNull(args[ps.i]);
              if (0 <= m.IndexOf('.')) {
                if (methodsToTranslateMethodQualified == null) {
                  methodsToTranslateMethodQualified = new List<string/*!*/>();
                }
                methodsToTranslateMethodQualified.Add(m);
              } else {
                if (methodsToTranslateMethod == null) {
                  methodsToTranslateMethod = new List<string/*!*/>();
                }
                methodsToTranslateMethod.Add(m);
              }
            }
            break;

          case "-trClass":
          case "/trClass":
            if (ps.ConfirmArgumentCount(1)) {
              string m = cce.NonNull(args[ps.i]);
              if (0 <= m.IndexOf('.')) {
                if (methodsToTranslateClassQualified == null) {
                  methodsToTranslateClassQualified = new List<string/*!*/>();
                }
                methodsToTranslateClassQualified.Add(m);
              } else {
                if (methodsToTranslateClass == null) {
                  methodsToTranslateClass = new List<string/*!*/>();
                }
                methodsToTranslateClass.Add(m);
              }
            }
            break;

          case "-trFile":
          case "/trFile":
            if (methodsToTranslateFile == null) {
              methodsToTranslateFile = new List<string/*!*/>();
            }
            if (ps.ConfirmArgumentCount(1)) {
              methodsToTranslateFile.Add(cce.NonNull(args[ps.i]));
            }
            break;

          case "-trExclude":
          case "/trExclude":
            if (ps.ConfirmArgumentCount(1)) {
              methodsToTranslateExclude.Add(cce.NonNull(args[ps.i]));
            }
            break;

          case "-xml":
          case "/xml":
            if (ps.ConfirmArgumentCount(1)) {
              XmlSinkFilename = args[ps.i];
            }
            break;

          case "-print":
          case "/print":
            if (ps.ConfirmArgumentCount(1)) {
              PrintFile = args[ps.i];
            }
            break;

          case "-dprelude":
          case "/dprelude":
            if (ps.ConfirmArgumentCount(1))
            {
                DafnyPrelude = args[ps.i];
            }
            break;

          case "-dprint":
          case "/dprint":
            if (ps.ConfirmArgumentCount(1)) {
              DafnyPrintFile = args[ps.i];
            }
            break;

          case "-compile":
          case "/compile": {
              int compile = 0;
              if (ps.GetNumericArgument(ref compile, 2)) {
                Compile = compile == 1;
              }
              break;
            }

          case "-contracts":
          case "/contracts":
          case "-c":
          case "/c":
            if (ps.ConfirmArgumentCount(1)) {
              ContractAssemblies.Add(cce.NonNull(args[ps.i]));
            }
            break;

          case "-proverLog":
          case "/proverLog":
            if (ps.ConfirmArgumentCount(1)) {
              SimplifyLogFilePath = args[ps.i];
            }
            break;

          case "-logPrefix":
          case "/logPrefix":
            if (ps.ConfirmArgumentCount(1)) {
              string s = cce.NonNull(args[ps.i]);
              LogPrefix += s.Replace('/', '-').Replace('\\', '-');
            }
            break;

          case "-proverShutdownLimit":
          case "/proverShutdownLimit":
            ps.GetNumericArgument(ref ProverShutdownLimit);
            break;

          case "-errorTrace":
          case "/errorTrace":
            ps.GetNumericArgument(ref ErrorTrace, 3);
            break;

          case "-level":
          case "/level":
            ps.GetNumericArgument(ref CheckingLevel, 3);
            break;

          case "-methodology":
          case "/methodology":
            if (ps.ConfirmArgumentCount(1)) {
              switch (args[ps.i]) {
                case "b":
                case "Boogie":
                case "boogie":
                  MethodologySelection = Methodology.Boogie;
                  break;
                case "vs":
                case "visible-state":
                  MethodologySelection = Methodology.VisibleState;
                  break;
                default:
                  ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                  break;
              }
            }
            break;

          case "-proverWarnings":
          case "/proverWarnings": {
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
              break;
            }

          case "-env":
          case "/env": {
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
              break;
            }

          case "-loopUnroll":
          case "/loopUnroll":
            ps.GetNumericArgument(ref LoopUnrollCount);
            break;

          case "-modifiesOnLoop":
          case "/modifiesOnLoop":
            ps.GetNumericArgument(ref LoopFrameConditions, 3);
            break;

          case "-modifiesDefault":
          case "/modifiesDefault":
            ps.GetNumericArgument(ref ModifiesDefault, 7);
            break;

          case "-localModifiesChecks":
          case "/localModifiesChecks": {
              int localChecks = 0;
              ps.GetNumericArgument(ref localChecks, 2);
              LocalModifiesChecks = (localChecks != 0);
            }
            break;

          case "-orderStrength":
          case "/orderStrength":
            ps.GetNumericArgument(ref OrderStrength, 2);
            break;

          case "-summationStrength":
          case "/summationStrength":
            ps.GetNumericArgument(ref SummationAxiomStrength, 2);
            break;

          case "-inductiveMinMax":
          case "/inductiveMinMax":
            ps.GetNumericArgument(ref InductiveMinMax, 6);
            break;

          case "-fcoStrength":
          case "/fcoStrength":
            ps.GetNumericArgument(ref FCOStrength, 6);
            break;

          case "-ownerModelEncoding":
          case "/ownerModelEncoding":
            if (ps.ConfirmArgumentCount(1)) {
              switch (args[ps.i]) {
                case "s":
                case "standard":
                  OwnershipModelEncoding = OwnershipModelOption.Standard;
                  break;
                case "e":
                case "experimental":
                  OwnershipModelEncoding = OwnershipModelOption.Experimental;
                  break;
                case "t":
                case "trivial":
                  OwnershipModelEncoding = OwnershipModelOption.Trivial;
                  break;
                default:
                  ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                  break;
              }
            }
            break;

          case "-printModel":
          case "/printModel":
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
            break;


          case "-mv":
          case "/mv":
            if (ps.ConfirmArgumentCount(1)) {
              ModelViewFile = args[ps.i];
            }
            break;

          case "-printModelToFile":
          case "/printModelToFile":
            if (ps.ConfirmArgumentCount(1)) {
              PrintErrorModelFile = args[ps.i];
            }
            break;


          case "-enhancedErrorMessages":
          case "/enhancedErrorMessages":
            ps.GetNumericArgument(ref EnhancedErrorMessages, 2);
            break;

          case "-forceBplErrors":
          case "/forceBplErrors":
            ForceBplErrors = true;
            break;

          case "-bv":
          case "/bv":
            if (ps.ConfirmArgumentCount(1)) {
              if (TheProverFactory == null) {
                TheProverFactory = ProverFactory.Load("Z3");
                ProverName = "Z3".ToUpper();
              }

              switch (args[ps.i]) {
                case "n":
                  Bitvectors = BvHandling.None;
                  break;
                case "z":
                  Bitvectors = BvHandling.Z3Native;
                  break;
                case "i":
                  Bitvectors = BvHandling.ToInt;
                  break;
                default:
                  ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                  break;
              }
            }
            break;

          case "-contractInfer":
          case "/contractInfer":
            ContractInfer = true;
            TheProverFactory = ProverFactory.Load("ContractInference");
            ProverName = "ContractInference".ToUpper();
            break;

          case "-subsumption":
          case "/subsumption": {
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
              break;
            }

          case "-liveVariableAnalysis":
          case "/liveVariableAnalysis": {
              int lva = 0;
              if (ps.GetNumericArgument(ref lva, 3)) {
                LiveVariableAnalysis = lva;
              }
              break;
            }

          case "-removeEmptyBlocks":
          case "/removeEmptyBlocks": {
              int reb = 0;
              if (ps.GetNumericArgument(ref reb, 2)) {
                RemoveEmptyBlocks = reb == 1;
              }
              break;
            }

          case "-coalesceBlocks":
          case "/coalesceBlocks": {
              int cb = 0;
              if (ps.GetNumericArgument(ref cb, 2)) {
                CoalesceBlocks = cb == 1;
              }
              break;
            }

          case "/DoomDebug":
            vcVariety = VCVariety.Doomed;
            useDoomDebug = true;
            break;

          case "-vc":
          case "/vc":
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
                case "doomed":
                  vcVariety = VCVariety.Doomed;
                  break;
                default:
                  ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                  break;
              }
            }
            break;

          case "-prover":
          case "/prover":
            if (ps.ConfirmArgumentCount(1)) {
              TheProverFactory = ProverFactory.Load(cce.NonNull(args[ps.i]));
              ProverName = cce.NonNull(args[ps.i]).ToUpper();
            }
            break;

          case "-proverOpt":
          case "/proverOpt":
            if (ps.ConfirmArgumentCount(1)) {
              ProverOptions.Add(cce.NonNull(args[ps.i]));
            }
            break;

          case "-extractLoops":
          case "/extractLoops":
            if (ps.ConfirmArgumentCount(0)) {
              ExtractLoops = true;
            }
            break;
          case "-inline":
          case "/inline":
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
            break;
          case "-lazyInline":
          case "/lazyInline":
            if (ps.ConfirmArgumentCount(1)) {
              switch (args[ps.i]) {
                case "0":
                  LazyInlining = 0;
                  break;
                case "1":
                  LazyInlining = 1;
                  break;
                case "2":
                  LazyInlining = 2;
                  break;
                default:
                  ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                  break;
              }
            }
            break;
          case "-stratifiedInline":
          case "/stratifiedInline":
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
            break;
          case "-recursionBound":
          case "/recursionBound": 
            if(ps.ConfirmArgumentCount(1)){
              RecursionBound = Int32.Parse(cce.NonNull(args[ps.i]));
            }
            break;
          case "-coverageReporter":
          case "/coverageReporter":
            if (ps.ConfirmArgumentCount(1)) {
              CoverageReporterPath = args[ps.i];
            }
            break;
          case "-stratifiedInlineOption":
          case "/stratifiedInlineOption":
            if (ps.ConfirmArgumentCount(1)) {
              StratifiedInliningOption=Int32.Parse(cce.NonNull(args[ps.i]));
            }
            break;
          case "-useUnsatCoreForInlining":
          case "/useUnsatCoreForInlining":
            UseUnsatCoreForInlining = true;
            break;
          case "-inferLeastForUnsat":
          case "/inferLeastForUnsat":
            if (ps.ConfirmArgumentCount(1))
            {
                inferLeastForUnsat = args[ps.i];
            }
            break;
          case "-typeEncoding":
          case "/typeEncoding":
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
            break;

          case "-instrumentInfer":
          case "/instrumentInfer":
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
            break;

          case "-vcBrackets":
          case "/vcBrackets":
            ps.GetNumericArgument(ref BracketIdsInVC, 2);
            break;

          case "-proverMemoryLimit":
          case "/proverMemoryLimit": {
              int d = 0;
              if (ps.GetNumericArgument(ref d)) {
                MaxProverMemory = d * Megabyte;
              }
              break;
            }

          case "-vcsMaxCost":
          case "/vcsMaxCost":
            ps.GetNumericArgument(ref VcsMaxCost);
            break;

          case "-vcsPathJoinMult":
          case "/vcsPathJoinMult":
            ps.GetNumericArgument(ref VcsPathJoinMult);
            break;

          case "-vcsPathCostMult":
          case "/vcsPathCostMult":
            ps.GetNumericArgument(ref VcsPathCostMult);
            break;

          case "-vcsAssumeMult":
          case "/vcsAssumeMult":
            ps.GetNumericArgument(ref VcsAssumeMult);
            break;

          case "-vcsPathSplitMult":
          case "/vcsPathSplitMult":
            ps.GetNumericArgument(ref VcsPathSplitMult);
            break;

          case "-vcsMaxSplits":
          case "/vcsMaxSplits":
            ps.GetNumericArgument(ref VcsMaxSplits);
            break;

          case "-vcsMaxKeepGoingSplits":
          case "/vcsMaxKeepGoingSplits":
            ps.GetNumericArgument(ref VcsMaxKeepGoingSplits);
            break;

          case "-vcsFinalAssertTimeout":
          case "/vcsFinalAssertTimeout":
            ps.GetNumericArgument(ref VcsFinalAssertTimeout);
            break;

          case "-vcsKeepGoingTimeout":
          case "/vcsKeepGoingTimeout":
            ps.GetNumericArgument(ref VcsKeepGoingTimeout);
            break;

          case "-vcsCores":
          case "/vcsCores":
            ps.GetNumericArgument(ref VcsCores);
            break;

          case "-simplifyMatchDepth":
          case "/simplifyMatchDepth":
            ps.GetNumericArgument(ref SimplifyProverMatchDepth);
            break;

          case "-timeLimit":
          case "/timeLimit":
            ps.GetNumericArgument(ref ProverKillTime);
            break;

          case "-smokeTimeout":
          case "/smokeTimeout":
            ps.GetNumericArgument(ref SmokeTimeout);
            break;

          case "-errorLimit":
          case "/errorLimit":
            ps.GetNumericArgument(ref ProverCCLimit);
            break;

          case "-z3opt":
          case "/z3opt":
            if (ps.ConfirmArgumentCount(1)) {
              Z3Options.Add(cce.NonNull(args[ps.i]));
            }
            break;

          case "-z3lets":
          case "/z3lets":
            ps.GetNumericArgument(ref Z3lets, 4);
            break;

          case "-platform":
          case "/platform":
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
            break;

          case "-stdlib":
          case "/stdlib":
            if (ps.ConfirmArgumentCount(1)) {
              this.StandardLibraryLocation = args[ps.i];
            }
            break;

          case "-Houdini":
          case "/Houdini":
            this.houdiniEnabled = true;
            if (ps.hasColonArgument) {
              if (ps.ConfirmArgumentCount(1)) {
                foreach (char c in cce.NonNull(args[ps.i])) {
                  switch (c) {
                    case 'c':
                      houdiniFlags.continueAtError = true;
                      break;
                    case 'i':
                      houdiniFlags.incremental = true;
                      break;
                    default:
                      ps.Error("Unknown houdini flag: " + c + "\n");
                      break;
                  }
                }
              }
            }
            break;

          default:
            Contract.Assume(true);
            bool option = false;
            if (ps.CheckBooleanFlag("printUnstructured", ref option)) {
              cce.BeginExpose(this);
              {
                PrintUnstructured = option ? 1 : 0;
              }
              cce.EndExpose();
            } else if (
              ps.CheckBooleanFlag("printDesugared", ref PrintDesugarings) ||
              ps.CheckBooleanFlag("printInstrumented", ref PrintInstrumented) ||
              ps.CheckBooleanFlag("printWithUniqueIds", ref PrintWithUniqueASTIds) ||
              ps.CheckBooleanFlag("wait", ref Wait) ||
              ps.CheckBooleanFlag("trace", ref Trace) ||
              ps.CheckBooleanFlag("traceTimes", ref TraceTimes) ||
              ps.CheckBooleanFlag("noResolve", ref NoResolve) ||
              ps.CheckBooleanFlag("noTypecheck", ref NoTypecheck) ||
              ps.CheckBooleanFlag("overlookTypeErrors", ref OverlookBoogieTypeErrors) ||
              ps.CheckBooleanFlag("noVerify", ref Verify, false) ||
              ps.CheckBooleanFlag("traceverify", ref TraceVerify) ||
              ps.CheckBooleanFlag("noConsistencyChecks", ref noConsistencyChecks, true) ||
              ps.CheckBooleanFlag("alwaysAssumeFreeLoopInvariants", ref AlwaysAssumeFreeLoopInvariants, true) ||
              ps.CheckBooleanFlag("nologo", ref DontShowLogo) ||
              ps.CheckBooleanFlag("noVerifyByDefault", ref NoVerifyByDefault) ||
              ps.CheckBooleanFlag("useUncheckedContracts", ref UseUncheckedContracts) ||
              ps.CheckBooleanFlag("proverLogAppend", ref SimplifyLogFileAppend) ||
              ps.CheckBooleanFlag("checkInfer", ref InstrumentWithAsserts) ||
              ps.CheckBooleanFlag("interprocInfer", ref IntraproceduralInfer, false) ||
              ps.CheckBooleanFlag("restartProver", ref RestartProverPerVC) ||
              ps.CheckBooleanFlag("printInlined", ref PrintInlined) ||
              ps.CheckBooleanFlag("arithDistributionAxioms", ref UseArithDistributionAxioms) ||
              ps.CheckBooleanFlag("smoke", ref SoundnessSmokeTest) ||
              ps.CheckBooleanFlag("vcsDumpSplits", ref VcsDumpSplits) ||
              ps.CheckBooleanFlag("dbgRefuted", ref DebugRefuted) ||
              ps.CheckBooleanFlag("causalImplies", ref CausalImplies) ||
              ps.CheckBooleanFlag("reflectAdd", ref ReflectAdd) ||
              ps.CheckBooleanFlag("z3types", ref Z3types) ||
              ps.CheckBooleanFlag("z3multipleErrors", ref z3AtFlag, false) ||
              ps.CheckBooleanFlag("monomorphize", ref Monomorphize) ||
              ps.CheckBooleanFlag("useArrayTheory", ref UseArrayTheory) ||
              ps.CheckBooleanFlag("doModSetAnalysis", ref DoModSetAnalysis)
              ) {
              // one of the boolean flags matched
            } else if (ps.s.StartsWith("-") || ps.s.StartsWith("/")) {
              ps.Error("unknown switch: {0}", ps.s);
            } else if (ps.ConfirmArgumentCount(0)) {
              string filename = ps.s;
              string extension = Path.GetExtension(filename);
              if (extension != null) {
                InputFileExtension = extension.ToLower();
              }
              Files.Add(filename);
              FileName = filename;
            }
            break;
        }
        cce.BeginExpose(ps);
        ps.i = ps.nextIndex;
        cce.EndExpose();
      }

      Contract.Assume(true);
      if (ps.encounteredErrors)
        res *= 2;
      if (res < 0) {  // help requested
        Usage();
      } else if (AttrHelpRequested) {
        AttributeUsage();
      } else if (ps.encounteredErrors) {
        Console.WriteLine("Use /help for available options");
      }

      SetProverOptions();

      if (Trace) {
        BoogieDebug.DoPrinting = true;
      } // reuse the -trace option for debug printing
      return res;
    }

    private void SetProverOptions() {
      //modifies this.*;
      Contract.Ensures(TheProverFactory != null);
      Contract.Ensures(vcVariety != VCVariety.Unspecified);
      // expand macros in filenames, now that LogPrefix is fully determined
      ExpandFilename(ref XmlSinkFilename);
      ExpandFilename(ref PrintFile);
      ExpandFilename(ref DafnyPrelude);
      ExpandFilename(ref DafnyPrintFile);
      ExpandFilename(ref SimplifyLogFilePath);
      ExpandFilename(ref PrintErrorModelFile);

      Contract.Assume(XmlSink == null);  // XmlSink is to be set here
      if (XmlSinkFilename != null) {
        XmlSink = new XmlSink(XmlSinkFilename);
      }

      if (TheProverFactory == null) {
        cce.BeginExpose(this);
        {
          TheProverFactory = ProverFactory.Load("Z3");
          ProverName = "Z3".ToUpper();
        }
        cce.EndExpose();
      }

      if (vcVariety == VCVariety.Unspecified) {
        vcVariety = TheProverFactory.DefaultVCVariety;
      }

      if (LoopFrameConditions == -1) {
        // /modifiesOnLoop not specified.  Set its default depending on /localModifiesChecks
        if (LocalModifiesChecks) {
          LoopFrameConditions = 1;
        } else {
          LoopFrameConditions = 2;
        }
      }

      switch (InductiveMinMax) {
        case 1:
        case 2:
        case 4:
        case 5:
          ReflectAdd = true;  // these InductiveMinMax modes imply ReflectAdd
          break;
        default:
          break;
      }

      if (MethodologySelection == Methodology.VisibleState) {
        OwnershipModelEncoding = OwnershipModelOption.Trivial;
      }

      if (UseArrayTheory) {
        Monomorphize = true;
      }

      if (LazyInlining > 0) {
        TypeEncodingMethod = TypeEncoding.Monomorphic;
        UseArrayTheory = true;
        UseAbstractInterpretation = false;
      }

      if (inferLeastForUnsat != null)
      {
          StratifiedInlining = 1;
      }

      if (StratifiedInlining > 0) {
        TypeEncodingMethod = TypeEncoding.Monomorphic;
        UseArrayTheory = true;
        UseAbstractInterpretation = false;
        if (ProverName == "Z3API")
        {
            ProverCCLimit = 1;
        }
      }
    }



    public bool UserWantsMethodLogging(string methodFullName) {
      Contract.Requires(methodFullName != null);
      if (methodToLog == null) {
        return false;
      }
      return methodToLog == "*" || methodFullName.IndexOf(methodToLog) >= 0;
    }

    public bool UserWantsToBreak(string methodFullName) {
      Contract.Requires(methodFullName != null);
      if (methodToBreakOn == null) {
        return false;
      }
      return methodFullName.IndexOf(methodToBreakOn) >= 0;
    }

    public bool UserWantsToCheckRoutine(string methodFullname) {
      Contract.Requires(methodFullname != null);
      if (procsToCheck == null) {
        // no preference
        return true;
      }
      return Contract.Exists(procsToCheck, s => 0 <= methodFullname.IndexOf(s));
    }

#if CCI
    public bool UserWantsToTranslateRoutine(Cci.Method method, string methodFullname) {
      Contract.Requires(methodFullname != null);
      Contract.Requires(method != null);
      return UserWantsToTranslateRoutineInclude(method, methodFullname) &&
        !Contract.Exists(methodsToTranslateExclude, s => 0 <= methodFullname.IndexOf(s));
    }

    public bool UserWantsToTranslateRoutineInclude(Cci.Method method, string methodFullname) {
      Contract.Requires(methodFullname != null);
      Contract.Requires(method != null);
      if (methodsToTranslateSubstring == null &&
          methodsToTranslateClass == null &&
          methodsToTranslateClassQualified == null &&
          methodsToTranslateFile == null &&
          methodsToTranslateMethod == null &&
          methodsToTranslateMethodQualified == null) {
        // no preference
        return true;
      }
      if (methodsToTranslateSubstring != null) {
        if (Contract.Exists(methodsToTranslateSubstring, s => 0 <= methodFullname.IndexOf(s))) {
          return true;
        }
      }
      if (methodsToTranslateMethod != null) {
        string methodName = method.Name.Name;
        Contract.Assert(methodsToTranslateMethod != null);
        if (methodsToTranslateMethod.Contains(methodName)) {
          return true;
        }
      }
      if (methodsToTranslateMethodQualified != null && method.DeclaringType != null) {
        string methodName = method.DeclaringType.Name.Name + "." + method.Name.Name;
        Contract.Assert(methodsToTranslateMethodQualified != null);
        if (methodsToTranslateMethodQualified.Contains(methodName)) {
          return true;
        }
      }
      if (method.DeclaringType != null) {
        if (methodsToTranslateClass != null) {
          string className = method.DeclaringType.Name.Name;
          if (methodsToTranslateClass.Contains(className)) {
            return true;
          }
        }
        if (methodsToTranslateClassQualified != null) {
          string className = method.DeclaringType.FullName;
          if (className != null) {
            className = className.Replace('+', '.');
            if (methodsToTranslateClassQualified.Contains(className)) {
              return true;
            }
          }
        }
      }
      if (methodsToTranslateFile != null) {
        string methodFilename = GetSourceDocument(method);
        if (methodFilename != null) {
          string path = methodFilename;
          if (path != null) {
            string filename = Path.GetFileName(path);
            if (methodsToTranslateFile.Contains(filename)) {
              return true;
            }
          }
        }
      }
      // the method is not among the desired routines
      return false;
    }

    /// <summary>
    /// Returns the file containing "method".  Returns null f that information is not available.
    /// </summary>
    static string GetSourceDocument(Cci.Method method) {
      Contract.Requires(method != null);
      // Start by looking for a source context in the method itself.  However, if the program
      // was read from a binary, then there is no source location for the method.  If so, there
      // some other ways we might find a source location.
      if (method.SourceContext.Document != null) {
        return method.SourceContext.Document.Name;
      }
      // Try to find a source location in the method's contract
      if (method.Contract != null) {
        if (method.Contract.Requires != null) {
          foreach (Cci.Requires c in method.Contract.Requires) {
            if (c != null && c.SourceContext.Document != null) {
              return c.SourceContext.Document.Name;
            }
          }
        }
        if (method.Contract.Modifies != null) {
          foreach (Cci.Expression c in method.Contract.Modifies) {
            if (c != null && c.SourceContext.Document != null) {
              return c.SourceContext.Document.Name;
            }
          }
        }
        if (method.Contract.Ensures != null) {
          foreach (Cci.Ensures c in method.Contract.Ensures) {
            if (c != null && c.SourceContext.Document != null) {
              return c.SourceContext.Document.Name;
            }
          }
        }
      }
      // As a last attempt, look for a source location among the statements
      if (method.Body != null) {
        return GetSourceDocumentFromStatements(method.Body.Statements);
      }
      return null;  // no source location found
    }

    [Pure]
    static string GetSourceDocumentFromStatements(Cci.StatementList list) {
      if (list != null) {
        foreach (Cci.Statement c in list) {
          if (c != null && c.SourceContext.Document != null) {
            return c.SourceContext.Document.Name;
          }
          if (c is Cci.Block) {
            Cci.Block b = (Cci.Block)c;
            string n = GetSourceDocumentFromStatements(b.Statements);
            if (n != null) {
              return n;
            }
          }
        }
      }
      return null;
    }
#endif

    class CommandLineParseState {
      public string s;
      public bool hasColonArgument;
      public readonly string[]/*!*/ args;
      public int i;
      public int nextIndex;
      public bool encounteredErrors;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(args != null);
        Contract.Invariant(0 <= i && i <= args.Length);
        Contract.Invariant(0 <= nextIndex && nextIndex <= args.Length);

      }



      public CommandLineParseState(string[] args) {
        Contract.Requires(args != null);
        Contract.Requires(Contract.ForAll(0, args.Length, i => args[i] != null));
        Contract.Ensures(this.args == args);
        this.s = null;  // set later by client
        this.hasColonArgument = false;  // set later by client
        this.args = args;
        this.i = 0;
        this.nextIndex = 0;  // set later by client
        this.encounteredErrors = false;
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
        if (this.ConfirmArgumentCount(1)) {
          try {
            Contract.Assume(args[i] != null);
            Contract.Assert(args[i] is string);  // needed to prove args[i].IsPeerConsistent
            int d = Convert.ToInt32(this.args[this.i]);
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

      /// <summary>
      /// If there is one argument and it is a non-negative integer less than "limit",
      /// then set "arg" to that number and return "true".
      /// Otherwise, emit error message, leave "arg" unchanged, and return "false".
      /// </summary>
      public bool GetNumericArgument(ref int arg, int limit) {
        Contract.Requires(this.i < args.Length);
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
        Console.Error.WriteLine("Boogie: Error: " + String.Format(message, args));
        encounteredErrors = true;
      }
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

    public static void AttributeUsage() {
      Console.WriteLine(
@"Boogie: The following attributes are supported by this implementation.

  ---- On axioms -------------------------------------------------------------

    {:inline true}
      Works on axiom of the form: 
        (forall VARS :: f(VARS) = expr(VARS))
      Makes Boogie replace f(VARS) with expr(VARS) everywhere just before
      doing VC generation.

    {:ignore ""p,q..""}
      Exclude the axiom when generating VC for a prover supporting any
      of the features 'p', 'q', ...
      All the provers support the feature 'all'.
      Simplify supports 'simplify' and 'simplifyLike'.
      Z3 supports 'z3', 'simplifyLike' and either 'bvInt' (if the /bv:i
      option is passed) or 'bvDefSem' (for /bv:z).

  ---- On implementations and procedures -------------------------------------

     {:inline N}
       Inline given procedure (can be also used on implementation). 
       N should be a non-negative number and represents the inlining depth. 
       With /inline:assume call is replaced with ""assume false"" once inlining depth is reached.
       With /inline:assert call is replaced with ""assert false"" once inlining depth is reached.
       With /inline:spec call is left as is once inlining depth is reached.
       With the above three options, methods with the attribute {:inline N} are not verified.
       With /inline:none the entire attribute is ignored. 
       
     {:verify false}
       Skip verification of an implementation.
       
     {:forceBvZ3Native true}
       Verify the given implementation with the native Z3 bitvector
       handling. Only works if /bv:i (or /bv:z, but then it does not do
       anything) is given on the command line.
       
     {:forceBvInt true}
       Use int translation for the given implementation. Only work with
       /bv:z (or /bv:i).
       
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

  ---- On functions ----------------------------------------------------------

     {:bvbuiltin ""spec""}
       Z3 specific, used only with /bv:z.
       
     {:bvint ""fn""}
       With /bv:i rewrite the function to function symbol 'fn', except if
       the 'fn' is 'id', in which case just strip the function altogether.

     {:never_pattern true}
       Terms starting with this function symbol will never be
       automatically selected as patterns. It does not prevent them
       from being used inside the triggers, and does not affect explicit
       trigger annotations. Internally it works by adding {:nopats ...}
       annotations to quantifiers.

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
       
  ---- The end ---------------------------------------------------------------
");
    }

    private static bool printedHelp = false;

    public static void Usage() {
      // Ensure that we only print the help message once,
      // no matter how many enabling conditions for printing
      // help were triggered.
      if (printedHelp) {
        return;
      }
      printedHelp = true;

      Console.WriteLine(@"Boogie: usage:  Boogie [ option ... ] [ filename ... ]
  where <option> is one of

  ---- General options -------------------------------------------------------

  /help          : this message
  /attrHelp      : print a message about declaration attributes supported by
                   this implementation
  /nologo        : suppress printing of version number, copyright message
  /env:<n>       : print command line arguments
                   0 - never, 1 (default) - during BPL print and prover log,
                   2 - like 1 and also to standard output
  /wait          : await Enter from keyboard before terminating program
  /xml:<file>    : also produce output in XML format to <file>

  ---- Spec# options ---------------------------------------------------------

  If any of the following switches is included, only those methods specified
  by some switch are translated into Boogie.  Furthermore, a method is
  not translated if a [Verify(false)] attribute applies to it or if the
  flag /trExclude applies (see below).
  /translate:<str> : include method if its full name contains substring <str>
  /trMethod:<method> : include method if its name is <method>
                       Format:  Name or Class.Name
  /trClass:<class>   : include method if the enclosing class is <class>
                       Format:  Name or Qualification.Name
  /trFile:<filename> : include method if it is contained in file <filename>
                       Format:  Filename.ssc

  /trExclude:<str> : exclude method it its full name contains substring <str>

  /c[ontracts]:<file>
                 : apply the contracts from <file> to
                   the referenced assemblies of the input assembly.
                   Note: the contracts for Xyz must be in Xyz.Contracts
  /methodology:<m> : selects the specification and verification methodology
                   b = boogie (default)
                   vs = visible-state
  /level:<n>     : 0 - reduced checks,
                   1 - no modifies checking, 2 - full (default)
  /useUncheckedContracts : generate purity axioms even when the postconditions
                   could not be checked to be sound (this option only for
                   experts and dare devils)
  /modifiesDefault:<n> :
                   0 - just what is declared
                   1 - what is declared plus E.snapshot for every top-level
                       E.f, E.*, E.**, E[i], or E[*] in the modifies clause
                   2 - (1) but also for nested E's
                   3 - (1) plus this.snapshot
                   4 - (2) plus this.snapshot
                   5 - (default) (1) plus p.* for receiver parameter p not
                       occurring at the top-level of modifies clause as
                       p.f, p.*, p.**, p[i], p[*], or p.0
                   6 - (5) but for every parameter p
  /modifiesOnLoop:<n> : 0 - never, 1 - assume only (default),
                        2 - assume and check (default with
                            /localModifiesChecks:0)
  /localModifiesChecks: 0 - check modifies-clause as post-condition of a
                            procedure
                        1 - check violations of modifies-clause at each
                            assignment and method call (default)
  /loopUnroll:<n>  : unroll loops, following up to n back edges (and then some)
  /noVerifyByDefault : change the default to [Verify(false)]
  /orderStrength:<n> : 0 (default) - only few properties of subtyping
                                     axiomatized,
                       1 - full strength
  /summationStrength:<n> : 0 - less applicable triggers in the axioms
                           1 - (default) default set of axioms for summation-
                           like quantifiers;
  /arithDistributionAxioms : emit +/* distribution axioms
  /inductiveMinMax:<n> : 0 (default) - extreme axioms for min/max;
                         1 - inductive axioms for min/max;
                         2 - both extreme and inductive axioms for min/max
                         3,4,5 - like 0,1,2 but adding the plus-over-min/max
                             distribution axiom
                         Modes 1,2,4,5 imply /reflectAdd.
  /fcoStrength:<n> : adjusts the amount of information encoded about 'first
                     consistent owners'
                     0 - no FCO axiom, 1 - cheaper but weaker FCO axiom,
                     2 - pure-method FCO axiom,
                     3, 4, 5 (default) - like 0,1,2 plus more specific
                       FCO information on pure-method return
  /ownerModelEncoding:<enc> : s = standard (default)
                              e = experimental
                              t = trivial (implied by /methodology:vs)
  /printModel:<n> : 0 (default) - do not print Z3's error model
                    1 - print Z3's error model
                    2 - print Z3's error model plus reverse mappings         
                    4 - print Z3's error model in a more human readable way
  /printModelToFile:<file> : print model to <file> instead of console
  /mv:<n>           0 - model view off, 1 (default) - model view on
  /enhancedErrorMessages:<n> : 0 (default) - no enhanced error messages
                               1 - Z3 error model enhanced error messages

  ---- Dafny options ---------------------------------------------------------
  
  Multiple .dfy files supplied on the command line are concatenated into one
  Dafny program.

  /dprelude:<file> : choose Dafny prelude file
  /dprint:<file> : print Dafny program after parsing it
                   (use - as <file> to print to console)
  /compile:<n>   : 0 - do not compile Dafny program
                   1 (default) - upon successful verification of the Dafny
                       program, compile Dafny program to C# program out.cs

  ---- Boogie options --------------------------------------------------------

  Multiple .bpl files supplied on the command line are concatenated into one
  Boogie program.

  /proc:<p>      : limits which procedures to check
  /noResolve     : parse only
  /noTypecheck   : parse and resolve only

  /print:<file>  : print Boogie program after parsing it
                   (use - as <file> to print to console)
  /printWithUniqueIds : print augmented information that uniquely
                   identifies variables
  /printUnstructured : with /print option, desugars all structured statements
  /printDesugared : with /print option, desugars calls
  
  /overlookTypeErrors : skip any implementation with resolution or type
                        checking errors

  ---- Inference options -----------------------------------------------------

  /infer:<flags> : use abstract interpretation to infer invariants
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
                   s = debug statistics
                0..9 = number of iterations before applying a widen (default=0)
  /noinfer       : turn off the default inference, and overrides the /infer
                   switch on its left
  /checkInfer    : instrument inferred invariants as asserts to be checked by
                   theorem prover
  /interprocInfer : perform interprocedural inference (deprecated, not
                    supported)
  /contractInfer : perform procedure contract inference
  /logInfer      : print debug output during inference
  /instrumentInfer : h - instrument inferred invariants only at beginning of
                         loop headers (default)
                     e - instrument inferred invariants at beginning and end
                         of every block
  /printInstrumented : print Boogie program after it has been
                   instrumented with invariants
  /Houdini[:<flags>] : perform procedure Houdini
                     c = continue when an error found
                     i = use incremental queries
  /dbgRefuted    : log refuted Houdini candidates to XmlSink

  ---- Debugging and general tracing options ---------------------------------

  /trace         : blurt out various debug trace information
  /traceTimes    : output timing information at certain points in the pipeline
  /log[:method]  : Print debug output during translation

  /break[:method] : break into debugger

  ---- Verification-condition generation options -----------------------------
  
  /liveVariableAnalysis:<c> : 0 = do not perform live variable analysis 
                              1 = perform live variable analysis (default)
                              2 = perform interprocedural live variable analysis
  /noVerify      : skip VC generation and invocation of the theorem prover
  /removeEmptyBlocks:<c> : 0 - do not remove empty blocks during VC generation
                           1 - remove empty blocks (default)
  /coalesceBlocks:<c> : 0 = do not coalesce blocks
                        1 = coalesce blocks (default)
  /vc:<variety>  : n = nested block (default for non-/prover:z3),
                   m = nested block reach,
                   b = flat block, r = flat block reach,
                   s = structured, l = local, d = dag (default with /prover:z3)
                   doomed = doomed
  /DoomDebug     : Use Doom detection to debug (experimental)               
  /traceverify   : print debug output during verification condition generation
  /subsumption:<c> : apply subsumption to asserted conditions:
                    0 - never, 1 - not for quantifiers, 2 (default) - always
  /alwaysAssumeFreeLoopInvariants : usually, a free loop invariant (or assume
                   statement in that position) is ignored in checking contexts
                   (like other free things); this option includes these free
                   loop invariants as assumes in both contexts
  /bv:<bv>       : bitvector handling
                   n = none
                   z = native Z3 bitvectors (default)
                   i = unsoundly translate bitvectors to integers
  /inline:<i>    : use inlining strategy <i> for procedures with the :inline 
                   attribute, see /attrHelp for details:
                   none
                   assume (default)
                   assert
                   spec
  /printInlined  : print the implementation after inlining calls to 
                   procedures with the :inline attribute (works with /inline)
  /lazyInline:1  : Use the lazy inlining algorithm
  /stratifiedInline:1 : Use the stratified inlining algorithm
  /recursionBound:<n> : Set the recursion bound for stratified inlining to 
                        be n (default 500)
  /inferLeastForUnsat:<str> : Infer the least number of constants (whose names
                              are prefixed by <str>) that need to be set to 
                              true for the program to be correct. This turns
                              on stratified inlining.
  /smoke         : Soundness Smoke Test: try to stick assert false; in some 
                   places in the BPL and see if we can still prove it
  /smokeTimeout:<n> : Timeout, in seconds, for a single theorem prover 
                   invocation during smoke test, defaults to 10.
  /causalImplies : Translate Boogie's A ==> B into prover's A ==> A && B.
  /typeEncoding:<m> : how to encode types when sending VC to theorem prover
                   n = none (unsound)
                   p = predicates (default)
                   a = arguments
  /monomorphize    Do not abstract map types in the encoding (this is an
                   experimental feature that will not do the right thing if
                   the program uses polymorphism)
  /reflectAdd      In the VC, generate an auxiliary symbol, elsewhere defined
                   to be +, instead of +.

  ---- Verification-condition splitting --------------------------------------

  /vcsMaxCost:<f>   : VC will not be split unless the cost of a VC exceeds this
                      number, defaults to 2000.0. This does NOT apply in the
                      keep-going mode after first round of splitting.
  /vcsMaxSplits:<n> : Maximal number of VC generated per method. In keep 
                      going mode only applies to the first round.
                      Defaults to 1.
  /vcsMaxKeepGoingSplits:<n> : If set to more than 1, activates the keep 
                      going mode, where after the first round of splitting,
                      VCs that timed out are split into <n> pieces and retried
                      until we succeed proving them, or there is only one 
                      assertion on a single path and it timeouts (in which
                      case error is reported for that assertion). 
                      Defaults to 1.
  /vcsKeepGoingTimeout:<n> : Timeout in seconds for a single theorem prover
                      invocation in keep going mode, except for the final
                      single-assertion case. Defaults to 1s.
  /vcsFinalAssertTimeout:<n> : Timeout in seconds for the single last 
                      assertion in the keep going mode. Defaults to 30s.
  /vcsPathJoinMult:<f> : If more than one path join at a block, by how much
                      multiply the number of paths in that block, to accomodate
                      for the fact that the prover will learn something on one
                      paths, before proceeding to another. Defaults to 0.8.
  /vcsPathCostMult:<f1>
  /vcsAssumeMult:<f2> : The cost of a block is 
         (<assert-cost> + <f2>*<assume-cost>)*(1.0 + <f1>*<entering-paths>)
                      <f1> defaults to 1.0, <f2> defaults to 0.01.
                      The cost of a single assertion or assumption is 
                      currently always 1.0.
  /vcsPathSplitMult:<f> : If the best path split of a VC of cost A is into 
                      VCs of cost B and C, then the split is applied if
                      A >= <f>*(B+C), otherwise assertion splitting will be 
                      applied. Defaults to 0.5 (always do path splitting if 
                      possible), set to more to do less path splitting
                      and more assertion splitting.
  /vcsDumpSplits      For split #n dump split.n.dot and split.n.bpl. 
                      Warning: Affects error reporting.
  /vcsCores:<n>     : Try to verify <n> VCs at once. Defaults to 1.

  ---- Prover options --------------------------------------------------------

  /errorLimit:<num> : Limit the number of errors produced for each procedure
                      (default is 5, some provers may support only 1)
  /timeLimit:<num>  : Limit the number of seconds spent trying to verify
                      each procedure
  /errorTrace:<n> : 0 - no Trace labels in the error output,
                    1 (default) - include useful Trace labels in error output,
                    2 - include all Trace labels in the error output
  /vcBrackets:<b> : bracket odd-charactered identifier names with |'s.  <b> is:
                   0 - no (default with /prover:Z3), 
                   1 - yes (default with /prover:Simplify)
  /prover:<tp>   : use theorem prover <tp>, where <tp> is either the name of
                   a DLL containing the prover interface located in the 
                   Boogie directory, or a full path to a DLL containing such
                   an interface. The standard interfaces shipped include:
                   Z3 (default)
                   Simplify
                   SMTLib (only writes to a file)
                   ContractInference (uses Z3)
                   Z3api (Z3 using Managed .NET API)
  /proverOpt:KEY[=VALUE] : Provide a prover-specific option.
  /proverLog:<file> : Log input for the theorem prover.  Like filenames
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
                   name of the procedure that the verification condition is
                   for.
  /logPrefix:<str> : Defines the expansion of the macro '@PREFIX@', which can
                   be used in various filenames specified by other options.
  /proverLogAppend : Append (not overwrite) the specified prover log file
  /proverWarnings : 0 (default) - don't print, 1 - print to stdout,
                    2 - print to stderr
  /proverMemoryLimit:<num>  : Limit on the virtual memory for prover before
                             restart in MB (default:100MB)
  /restartProver            : Restart the prover after each query
  /proverShutdownLimit<num> : Time between closing the stream to the prover and
                              killing the prover process (default: 0s)
  /platform:<ptype>,<location>
                 : ptype = v11,v2,cli1
                 : location = platform libraries directory

  Simplify specific options:
  /simplifyMatchDepth:<num> : Set Simplify prover's matching depth limit

  Z3 specific options:
  /z3opt:<arg>   : specify additional Z3 options
  /z3multipleErrors : report multiple counterexamples for each error
  /useArrayTheory : use Z3's native theory (as opposed to axioms).  Currently
                    implies /monomorphize.

  /z3types       : generate multi-sorted VC that make use of Z3 types
  /z3lets:<n>    : 0 - no LETs, 1 - only LET TERM, 2 - only LET FORMULA,
                   3 - (default) any
");
    }
  }
}
