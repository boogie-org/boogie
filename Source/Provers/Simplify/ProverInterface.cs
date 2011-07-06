//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Text;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie.Simplify;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.TypeErasure;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie.Simplify {
  public abstract class LogProverInterface : ProverInterface {
    [NotDelayed]
    protected LogProverInterface(ProverOptions options,
        string openComment, string closeComment,
        string openActivity, string closeActivity,
        VCExpressionGenerator gen) {
      Contract.Requires(options != null);
      Contract.Requires(openComment != null);
      Contract.Requires(closeComment != null);
      Contract.Requires(openActivity != null);
      Contract.Requires(closeActivity != null);
      Contract.Requires(gen != null);
      Contract.Ensures(this.gen == gen);
      if (options.SeparateLogFiles) {
        this.commonPrefix = new List<string>();
      } else {
        this.logFileWriter = options.OpenLog(null);
      }
      this.openCommentString = openComment;
      this.closeCommentString = closeComment;
      this.openActivityString = openActivity;
      this.closeActivityString = closeActivity;
      this.gen = gen;
      this.options = options;

      if (CommandLineOptions.Clo.ShowEnv != CommandLineOptions.ShowEnvironment.Never) {
        // Emit version comment in the log
        LogCommonComment(CommandLineOptions.Clo.Version);
        LogCommonComment(CommandLineOptions.Clo.Environment);
      }
    }

    [StrictReadonly]
    [Additive]
    protected readonly VCExpressionGenerator gen;

    private TextWriter/*?*/ logFileWriter;
    [StrictReadonly]
    private readonly string openCommentString;
    [StrictReadonly]
    private readonly string closeCommentString;
    [StrictReadonly]
    private readonly string openActivityString;
    [StrictReadonly]
    private readonly string closeActivityString;
    [StrictReadonly]
    protected readonly ProverOptions options;
    [StrictReadonly]
    private readonly List<string>/*?*/ commonPrefix;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(openCommentString != null);
      Contract.Invariant(closeCommentString != null);
      Contract.Invariant(openActivityString != null);
      Contract.Invariant(closeActivityString != null);
      Contract.Invariant(options != null);
      Contract.Invariant(commonPrefix == null || cce.NonNullElements(commonPrefix));
    }


    public void LogActivity(string s) {
      Contract.Requires(s != null);
      LogActivity(s, false);
    }

    public void LogCommon(string s) {
      Contract.Requires(s != null);
      LogActivity(s, true);
    }

    private void LogActivity(string s, bool common) {
      Contract.Requires(s != null);
      Contract.Assume(common || !options.SeparateLogFiles || logFileWriter != null);
      if (logFileWriter != null) {
        logFileWriter.Write(openActivityString);
        logFileWriter.Write(s);
        logFileWriter.WriteLine(closeActivityString);
        logFileWriter.Flush();
      }
      if (common && commonPrefix != null) {
        commonPrefix.Add(openActivityString + s + closeActivityString);
      }
    }

    /// <summary>
    /// Write "comment" to logfile, if any, formatted as a comment for the theorem prover at hand.
    /// Assumes that "comment" does not contain any characters that would prematurely terminate
    /// the comment (like, perhaps, a newline or "*/").
    /// </summary>
    public override void LogComment(string comment) {
      //Contract.Requires(comment != null);
      LogComment(comment, false);
    }

    public void LogCommonComment(string comment) {
      Contract.Requires(comment != null);
      LogComment(comment, true);
    }

    private void LogComment(string comment, bool common) {
      Contract.Requires(comment != null);
      Contract.Assume(common || !options.SeparateLogFiles || logFileWriter != null);
      if (logFileWriter != null) {
        logFileWriter.Write(openCommentString);
        logFileWriter.Write(comment);
        logFileWriter.WriteLine(closeCommentString);
        logFileWriter.Flush();
      }
      if (common && commonPrefix != null) {
        commonPrefix.Add(openCommentString + comment + closeCommentString);
      }
    }

    public virtual void NewProblem(string descName) {
      Contract.Requires(descName != null);
      if (commonPrefix != null) {
        if (logFileWriter != null) {
          logFileWriter.Close();
        }
        logFileWriter = options.OpenLog(descName);
        if (logFileWriter != null) {
          foreach (string s in commonPrefix) {
            Contract.Assert(s != null);
            logFileWriter.WriteLine(s);
          }
        }
      }
      LogComment("Proof obligation: " + descName);
    }

    public override void Close() {
      if (logFileWriter != null) {
        logFileWriter.Close();
        logFileWriter = null;
      }
    }

    public override VCExpressionGenerator VCExprGen {
      get {
        Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);
        return this.gen;
      }
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  [ContractClass(typeof(ProcessTheoremProverContracts))]
  public abstract class ProcessTheoremProver : LogProverInterface {
    private static string _proverPath;

    protected AxiomVCExprTranslator vcExprTranslator {
      get {
        Contract.Ensures(Contract.Result<AxiomVCExprTranslator>() != null);

        return cce.NonNull((AxiomVCExprTranslator)ctx.exprTranslator);
      }
    }

    protected abstract AxiomVCExprTranslator SpawnVCExprTranslator(ProverOptions p);

    // Return the number of axioms pushed to the theorem prover
    protected int FeedNewAxiomsDecls2Prover() {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      if (thmProver == null)
        return 0;
      int ret = 0;
      foreach (string s in vcExprTranslator.NewTypeDecls) {
        Contract.Assert(s != null);
        LogCommon(s);
        thmProver.Feed(s, 0);
      }
      foreach (string s in vcExprTranslator.NewAxioms) {
        Contract.Assert(s != null);
        LogBgPush(s);
        thmProver.AddAxioms(s);
        ret++;
      }
      return ret;
    }

    protected static string CodebaseString() {
      Contract.Ensures(Contract.Result<string>() != null);

      return Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location));
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullDictionaryAndValues(BackgroundPredicates));
      Contract.Invariant(BackgroundPredFilename != null);
      Contract.Invariant(ctx != null);
    }

    private static IDictionary<string/*!*/, string/*!>!*/> BackgroundPredicates =
      new Dictionary<string/*!*/, string/*!*/>();

    protected static string GetBackgroundPredicate(string filename) {
      Contract.Requires(filename != null);
      Contract.Ensures(Contract.Result<string>() != null);

      string res;
      if (!BackgroundPredicates.TryGetValue(filename, out res)) {
        // do we have to lock/synchronise anything?
        string univBackPredPath = Path.Combine(CodebaseString(), filename);
        using (StreamReader reader = new System.IO.StreamReader(univBackPredPath)) {
          res = reader.ReadToEnd();
        }
        BackgroundPredicates.Add(filename, res);
      }
      return cce.NonNull(res);
    }

    static void InitializeGlobalInformation(string proverExe)
      // throws ProverException, System.IO.FileNotFoundException;
    {
      Contract.Requires(proverExe != null);
      Contract.Ensures(_proverPath != null);

      if (CommandLineOptions.Clo.Z3ExecutablePath != null) {
        _proverPath = CommandLineOptions.Clo.Z3ExecutablePath;
      }

      if (_proverPath == null) {
        // Initialize '_proverPath'
        _proverPath = Path.Combine(CodebaseString(), proverExe);
        string firstTry = _proverPath;

        if (File.Exists(firstTry))
          return;

        string programFiles = Environment.GetEnvironmentVariable("ProgramFiles");
        Contract.Assert(programFiles != null);
        string programFilesX86 = Environment.GetEnvironmentVariable("ProgramFiles(x86)");
        if (programFiles.Equals(programFilesX86)) {
          // If both %ProgramFiles% and %ProgramFiles(x86)% point to "ProgramFiles (x86)", use %ProgramW6432% instead.
          programFiles = Environment.GetEnvironmentVariable("ProgramW6432");
        }


        List<string> z3Dirs = new List<string>();
        if (Directory.Exists(programFiles + @"\Microsoft Research\")) {
          string msrDir = programFiles + @"\Microsoft Research\";
          z3Dirs.AddRange(Directory.GetDirectories(msrDir, "Z3-*"));
        }
        if (Directory.Exists(programFilesX86 + @"\Microsoft Research\")) {
          string msrDir = programFilesX86 + @"\Microsoft Research\";
          z3Dirs.AddRange(Directory.GetDirectories(msrDir, "Z3-*"));
        }

        // Look for the most recent version of Z3.
        int minor = 0, major = 0;
        string winner = null;
        Regex r = new Regex(@"^Z3-(\d+)\.(\d+)$");
        foreach (string d in z3Dirs) {
          string name = new DirectoryInfo(d).Name;
          foreach (Match m in r.Matches(name)) {
            int ma, mi;
            ma = int.Parse(m.Groups[1].ToString());
            mi = int.Parse(m.Groups[2].ToString());
            if (major < ma || (major == ma && minor < mi)) {
              major = ma;
              minor = mi;
              winner = d;
            }
          }
        }

        if (major == 0 && minor == 0) {
          throw new ProverException("Cannot find executable: " + firstTry);
        }
        Contract.Assert(winner != null);

        _proverPath = Path.Combine(Path.Combine(winner, "bin"), proverExe);
        if (!File.Exists(_proverPath)) {
          throw new ProverException("Cannot find prover: " + _proverPath);
        }

        if (CommandLineOptions.Clo.Trace) {
          Console.WriteLine("[TRACE] Using prover: " + _proverPath);
        }
      }
    }

    [Rep]
    protected internal ProverProcess thmProver;
    bool currentProverHasBeenABadBoy = false;
    // invariant currentProverHasBeenABadBoy ==> thmProver != null;
    protected int restarts = 0;
    protected DeclFreeProverContext ctx;
    protected string BackgroundPredFilename;
    protected ConsoleCancelEventHandler cancelEvent;

    [NotDelayed]
    public ProcessTheoremProver(ProverOptions options, VCExpressionGenerator gen, DeclFreeProverContext ctx,
                                string proverExe, string backgroundPred)
      : base(options, "; ", "", "", "", gen) {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      Contract.Requires(proverExe != null);
      Contract.Requires(backgroundPred != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      BackgroundPredFilename = backgroundPred;
      InitializeGlobalInformation(proverExe);
      this.ctx = ctx;


      // ensure that a VCExprTranslator is available
      // if none exists so far, we have to create a new one
      // from scratch and feed the axioms to it
      if (ctx.exprTranslator == null) {
        AxiomVCExprTranslator tl = SpawnVCExprTranslator(options);
        ctx.exprTranslator = tl;
        tl.AddAxiom(tl.translate(ctx.Axioms, -1));
        // we clear the lists with new axioms and declarations;
        // they are not needed at this point
        List<string> x = tl.NewAxioms;
        //x = x;  // make the compiler happy: somebody uses the value of x
        x = tl.NewTypeDecls;
      }
    }

    /// <summary>
    /// MSchaef: Allows to Push a VCExpression as Axiom on the prover stack (beta)
    /// </summary>
    public override void PushVCExpression(VCExpr vc) {
      //Contract.Requires(vc != null);
      vcExprTranslator.AddAxiom(vcExprTranslator.translate(vc, 1));
    }

    public override string VCExpressionToString(VCExpr vc) {
      //Contract.Requires(vc != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return vcExprTranslator.translate(vc, 1);
    }

    // Number of axioms pushed since the last call to Check
    public override int NumAxiomsPushed() {
      return vcExprTranslator.NewAxiomsCount;
    }

    // Feed the axioms pushed since the last call to Check to the theorem prover
    public override int FlushAxiomsToTheoremProver() {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      return FeedNewAxiomsDecls2Prover();
    }

    public override void Pop() {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      Contract.Assert(thmProver != null);
      LogCommon("(BG_POP)");
      thmProver.PopAxioms();
    }

    [NoDefaultContract]  // important, since we have no idea what state the object might be in when this handler is invoked
    void ControlCHandler(object o, ConsoleCancelEventArgs a) {
      if (thmProver != null) {
        thmProver.Kill();
      }
    }

    public override void Close() {
      if (cancelEvent != null) {
        Console.CancelKeyPress -= cancelEvent;
        cancelEvent = null;
      }
      if (thmProver != null) {
        cce.BeginExpose(this);
        {
          thmProver.Close();
          thmProver = null;
          currentProverHasBeenABadBoy = false;
        }
        cce.EndExpose();
      }
      base.Close();
    }

    private UnexpectedProverOutputException proverException;

    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler) {
      //Contract.Requires(descriptiveName != null);
      //Contract.Requires(vc != null);
      //Contract.Requires(handler != null);
      this.NewProblem(descriptiveName);
      this.proverException = null;

      try {
        this.ResurrectProver();

        string vcString = vcExprTranslator.translate(vc, 1);

        Helpers.ExtraTraceInformation("Sending data to theorem prover");

        int num_axioms_pushed =
           FeedNewAxiomsDecls2Prover();

        LogActivity(vcString);

        Contract.Assert(thmProver != null);
        thmProver.BeginCheck(descriptiveName, vcString);

        if (CommandLineOptions.Clo.StratifiedInlining > 0) {
          // Pop all the axioms that were pushed by FeedNewAxiomsDecls2Prover
          for (int i = 0; i < num_axioms_pushed; i++) {
            LogBgPop();
            thmProver.PopAxioms();
          }
        }

        if (CommandLineOptions.Clo.RestartProverPerVC) {
          LogComment("Will restart the prover due to /restartProver option");
          currentProverHasBeenABadBoy = true;
        }
      } catch (UnexpectedProverOutputException e) {
        proverException = e;
      }
    }

    public override Outcome CheckOutcome(ErrorHandler handler) {
      //Contract.Requires(handler != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      if (this.thmProver == null) {
        return Outcome.Undetermined;
      }

      if (proverException == null) {
        try {
          ProverProcess.ProverOutcome result = thmProver.CheckOutcome(handler);

          if (options.ForceLogStatus) {
            switch (result) {
              case ProverProcess.ProverOutcome.Valid:
                LogActivity("DBG_WAS_VALID");
                break;
              case ProverProcess.ProverOutcome.NotValid:
                LogActivity("DBG_WAS_INVALID");
                break;
            }
          }

          switch (result) {
            case ProverProcess.ProverOutcome.Valid:
              return Outcome.Valid;
            case ProverProcess.ProverOutcome.TimeOut:
              return Outcome.TimeOut;
            case ProverProcess.ProverOutcome.OutOfMemory:
              return Outcome.OutOfMemory;
            case ProverProcess.ProverOutcome.Inconclusive:
              return Outcome.Undetermined;
            case ProverProcess.ProverOutcome.NotValid:
              return Outcome.Invalid;
          }
        } catch (UnexpectedProverOutputException e) {
          proverException = e;
        }
      }

      Contract.Assume(proverException != null);
      LogComment("***** Unexpected prover output");
      cce.BeginExpose(this);
      {
        currentProverHasBeenABadBoy = true;  // this will cause the next resurrect to restart the prover
      }
      cce.EndExpose();
      throw proverException;
    }

    protected virtual void ResurrectProver() {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      cce.BeginExpose(this);
      {
        if (thmProver != null) {
          if (thmProver.HasExited) {
            DateTime now = DateTime.Now;
            LogComment("***** Prover Crashed at or before " + now.ToString("G"));

          } else if (CommandLineOptions.Clo.MaxProverMemory > 0 &&
              thmProver.NumFormulasChecked > CommandLineOptions.Clo.MinNumOfProverCalls &&
              thmProver.PeakVirtualMemorySize > CommandLineOptions.Clo.MaxProverMemory) {
            LogComment("***** Exceeded memory limit.  Peak memory usage so far: " +
                thmProver.PeakVirtualMemorySize / CommandLineOptions.Megabyte + "MB");

          } else if (!currentProverHasBeenABadBoy) {
            // prover is ready to go
            return;
          }

          thmProver.Close();
          thmProver = null;
          currentProverHasBeenABadBoy = false;
          restarts++;

          if (CommandLineOptions.Clo.StratifiedInlining > 0)
          {
              Console.WriteLine("Warning: restarting theorem prover. Context could be lost");
          }
        }
          
        FireUpNewProver();
      }
      cce.EndExpose();
    }

    protected abstract ProverProcess CreateProverProcess(string proverPath);

    public void LogBgPush(string s) {
      Contract.Requires(s != null);
      LogCommon("(BG_PUSH ");
      LogCommon(s);
      LogCommon(")");
    }

    public void LogBgPop() {
      LogCommon("(BG_POP)");
    }

    [NoDefaultContract]
    private void FireUpNewProver()
    {
      Contract.Requires( cce.IsExposed(this));
      Contract.Requires( thmProver == null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      if (cancelEvent == null && CommandLineOptions.Clo.RunningBoogieFromCommandLine) {
        cancelEvent = new ConsoleCancelEventHandler(ControlCHandler);
        Console.CancelKeyPress += cancelEvent;
      }
      thmProver = CreateProverProcess(_proverPath);
      if (restarts == 0) {
        foreach (string s in thmProver.OptionComments().Split('\n')) {Contract.Assert(s != null);
          LogCommonComment(s);
        }
        foreach (string parmsetting in thmProver.ParameterSettings) {Contract.Assert(parmsetting != null);
          LogCommon(parmsetting);
        }
      }
      foreach (string parmsetting in thmProver.ParameterSettings) {Contract.Assert(parmsetting != null);
        thmProver.Feed(parmsetting, 0);
      }
      thmProver.Feed(GetBackgroundPredicate(BackgroundPredFilename), 3);

      if (restarts == 0) {
        // log the stuff before feeding it into the prover, so when it dies
        // and takes Boogie with it, we know what happened
        LogCommon(GetBackgroundPredicate(BackgroundPredFilename));

        foreach (string s in vcExprTranslator.AllTypeDecls){Contract.Assert(s != null);
          LogCommon(s);}
        foreach (string s in vcExprTranslator.AllAxioms){Contract.Assert(s != null);
          LogBgPush(s);}

        LogCommonComment("Initialized all axioms.");
      }

      foreach (string s in vcExprTranslator.AllTypeDecls){Contract.Assert(s != null);
        thmProver.Feed(s, 0);}
      foreach (string s in vcExprTranslator.AllAxioms){Contract.Assert(s != null);
        thmProver.AddAxioms(s);}

      // we have sent everything to the prover and can clear the lists with
      // new axioms and declarations
      List<string> x = vcExprTranslator.NewAxioms;
      //x = x;  // make the compiler happy: somebody uses the value of x
      x = vcExprTranslator.NewTypeDecls;
    }

    public override ProverContext Context {
      get {
        Contract.Ensures(Contract.Result<ProverContext>() != null);
        return this.ctx;
      }
    }
  }
  [ContractClassFor(typeof(ProcessTheoremProver))]
  public abstract class ProcessTheoremProverContracts :ProcessTheoremProver{
    protected override AxiomVCExprTranslator SpawnVCExprTranslator(ProverOptions p) {
      Contract.Requires(p != null);
      Contract.Ensures(Contract.Result<AxiomVCExprTranslator>() != null);
      throw new NotImplementedException();

    }
    protected override ProverProcess CreateProverProcess(string proverPath) {
      Contract.Requires(proverPath != null);
      Contract.Ensures(Contract.Result<ProverProcess>() != null);
      throw new NotImplementedException();
    }
    [NotDelayed]
    public ProcessTheoremProverContracts(ProverOptions options, VCExpressionGenerator gen, DeclFreeProverContext ctx,
                                string proverExe, string backgroundPred):base(options,gen,ctx,proverExe,backgroundPred)
       {throw new NotImplementedException();}
  }

  public class SimplifyTheoremProver : ProcessTheoremProver {
    [NotDelayed]
    public SimplifyTheoremProver(ProverOptions options, VCExpressionGenerator gen, DeclFreeProverContext ctx)
      : base(options, gen, ctx, "simplify.exe", "UnivBackPred2.sx") {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
    }

    protected override ProverProcess CreateProverProcess(string proverPath) {
      //Contract.Requires(proverPath != null);
      Contract.Ensures(Contract.Result<ProverProcess>() != null);

      return new SimplifyProverProcess(proverPath);
    }

    protected override AxiomVCExprTranslator SpawnVCExprTranslator(ProverOptions opts) {
      //Contract.Requires(opts!=null);
      Contract.Ensures(Contract.Result<AxiomVCExprTranslator>() != null);

      return new SimplifyVCExprTranslator(gen);
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public abstract class AxiomVCExprTranslator : VCExprTranslator {
    protected AxiomVCExprTranslator() {
      AllAxioms = new List<string> ();
      NewAxiomsAttr = new List<string> ();
      AllTypeDecls = new List<string> ();
      NewTypeDeclsAttr = new List<string> ();
    }

    protected AxiomVCExprTranslator(AxiomVCExprTranslator tl) {
      Contract.Requires(tl != null);
      AllAxioms = new List<string>(tl.AllAxioms);
      NewAxiomsAttr = new List<string>(tl.NewAxiomsAttr);
      AllTypeDecls = new List<string>(tl.AllTypeDecls);
      NewTypeDeclsAttr = new List<string>(tl.NewTypeDeclsAttr);
    }

    // we store all typing-related axioms that have been sent to the prover
    // so that the prover can be re-initialised in case it dies
    public readonly List<string/*!>!*/> AllAxioms;
    private List<string/*!>!*/> NewAxiomsAttr;

    // The length of the list NewAxiomsAttr
    public int NewAxiomsCount {
      get {
        return NewAxiomsAttr.Count;
      }
    }

    public List<string/*!>!*/> NewAxioms {
      get {
        Contract.Ensures(Contract.Result<List<string>>() != null);

        List<string/*!>!*/> res = NewAxiomsAttr;
        NewAxiomsAttr = new List<string>();
        return res;
      }
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(AllAxioms != null);
      Contract.Invariant(NewAxiomsAttr != null);
      Contract.Invariant(AllTypeDecls != null);
      Contract.Invariant(NewTypeDeclsAttr != null);
    }


    // similarly, a list of declarations that have been sent to the prover
    public readonly List<string/*!>!*/> AllTypeDecls;
    private List<string/*!>!*/> NewTypeDeclsAttr;

    public List<string>/*!>!*/ NewTypeDecls {
      get {
        List<string/*!>!*/> res = NewTypeDeclsAttr;
        NewTypeDeclsAttr = new List<string/*!*/>();
        return res;
      }
    }

    public void AddAxiom(string axiom) {
      Contract.Requires(axiom != null);
      AllAxioms.Add(axiom);
      NewAxiomsAttr.Add(axiom);
    }

    public void AddTypeDecl(string typeDecl) {
      Contract.Requires(typeDecl != null);
      AllTypeDecls.Add(typeDecl);
      NewTypeDeclsAttr.Add(typeDecl);
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public class SimplifyVCExprTranslator : AxiomVCExprTranslator {
    public SimplifyVCExprTranslator(VCExpressionGenerator gen) {
      Contract.Requires(gen != null);
      Gen = gen;
      TypeAxiomBuilder axBuilder;
      switch (CommandLineOptions.Clo.TypeEncodingMethod) {
        case CommandLineOptions.TypeEncoding.Arguments:
          axBuilder = new TypeAxiomBuilderArguments(gen);
          break;
        default:
          axBuilder = new TypeAxiomBuilderPremisses(gen);
          break;
      }
      axBuilder.Setup();
      AxBuilder = axBuilder;
      Namer = new UniqueNamer();
      LitAbstracter = new BigLiteralAbstracter(gen);
    }

    private SimplifyVCExprTranslator(SimplifyVCExprTranslator tl)
      : base(tl) {
      Contract.Requires(tl != null);
      Gen = tl.Gen;
      AxBuilder = (TypeAxiomBuilder)tl.AxBuilder.Clone();
      Namer = (UniqueNamer)tl.Namer.Clone();
      LitAbstracter = (BigLiteralAbstracter)tl.LitAbstracter.Clone();
    }

    public override Object Clone() {
      Contract.Ensures(Contract.Result<object>() != null);

      return new SimplifyVCExprTranslator(this);
    }

    private readonly VCExpressionGenerator Gen;
    private readonly TypeAxiomBuilder AxBuilder;
    private readonly UniqueNamer Namer;
    private readonly BigLiteralAbstracter LitAbstracter;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Gen != null);
      Contract.Invariant(AxBuilder != null);
      Contract.Invariant(Namer != null);
      Contract.Invariant(LitAbstracter != null);
    }


    public override string Lookup(VCExprVar var) {
      //Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<string>() != null);

      VCExprVar v = AxBuilder.TryTyped2Untyped(var);
      if (v != null) {
        var = v;
      }
      return Namer.Lookup(var);
    }

    public override string translate(VCExpr expr, int polarity) {
      //Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<string>() != null);

      Let2ImpliesMutator letImplier = new Let2ImpliesMutator(Gen);
      Contract.Assert(letImplier != null);

      // handle the types in the VCExpr
      TypeEraser eraser;
      switch (CommandLineOptions.Clo.TypeEncodingMethod) {
        case CommandLineOptions.TypeEncoding.Arguments:
          eraser = new TypeEraserArguments((TypeAxiomBuilderArguments)AxBuilder, Gen);
          break;
        case CommandLineOptions.TypeEncoding.Monomorphic:
          eraser = null;
          break;
        default:
          eraser = new TypeEraserPremisses((TypeAxiomBuilderPremisses)AxBuilder, Gen);
          break;
      }
      VCExpr exprWithoutTypes = eraser != null ? eraser.Erase(expr, polarity) : expr;
      Contract.Assert(exprWithoutTypes != null);

      TermFormulaFlattener flattener = new TermFormulaFlattener(Gen);
      Contract.Assert(flattener != null);
      VCExpr exprWithLet = flattener.Flatten(exprWithoutTypes);
      Contract.Assert(exprWithLet != null);
      VCExpr exprWithoutLet = letImplier.Mutate(exprWithLet);
      Contract.Assert(exprWithoutLet != null);

      // big integer literals
      VCExpr exprWithoutBigLits = LitAbstracter.Abstract(exprWithoutLet);
      Contract.Assert(exprWithoutBigLits != null);
      AddAxiom(SimplifyLikeExprLineariser.ToSimplifyString(LitAbstracter.GetNewAxioms(),
                                                           Namer));

      // type axioms
      VCExpr axiomsWithLet = flattener.Flatten(AxBuilder.GetNewAxioms());
      Contract.Assert(axiomsWithLet != null);
      VCExpr axiomsWithoutLet = letImplier.Mutate(axiomsWithLet);
      Contract.Assert(axiomsWithoutLet != null);

      AddAxiom(SimplifyLikeExprLineariser.ToSimplifyString(axiomsWithoutLet, Namer));
      return SimplifyLikeExprLineariser.ToSimplifyString(exprWithoutBigLits, Namer);
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public class Factory : ProverFactory {
    public override object SpawnProver(ProverOptions options, object ctxt) {
      //Contract.Requires(options != null);
      //Contract.Requires(ctxt != null);
      Contract.Ensures(Contract.Result<object>() != null);

      return new SimplifyTheoremProver(options,
                                       cce.NonNull((DeclFreeProverContext)ctxt).ExprGen,
                                       cce.NonNull((DeclFreeProverContext)ctxt));
    }

    public override object NewProverContext(ProverOptions options) {
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      if (CommandLineOptions.Clo.BracketIdsInVC < 0) {
        CommandLineOptions.Clo.BracketIdsInVC = 1;
      }
      VCExpressionGenerator gen = new VCExpressionGenerator();
      Contract.Assert(gen != null);
      List<string>/*!>!*/ proverCommands = new List<string> ();
      Contract.Assert(cce.NonNullElements(proverCommands));
      proverCommands.Add("all");
      proverCommands.Add("simplify");
      proverCommands.Add("simplifyLike");
      return new DeclFreeProverContext(gen, new VCGenerationOptions(proverCommands));
    }

    public override CommandLineOptions.VCVariety DefaultVCVariety {
      get {
        return CommandLineOptions.VCVariety.BlockNested;
      }
    }

    // needed to make test7 pass
    public override bool SupportsDags {
      get {
        return true;
      }
    }
  }
}
