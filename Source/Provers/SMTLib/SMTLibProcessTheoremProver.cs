using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.TypeErasure;
using System.Text;
using System.Numerics;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibProcessTheoremProver : ProverInterface
  {
    private readonly SMTLibOptions libOptions;
    private readonly SMTLibProverContext ctx;
    private VCExpressionGenerator gen;
    protected readonly SMTLibProverOptions options;
    private bool usingUnsatCore;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(ctx != null);
      Contract.Invariant(Namer != null);
      Contract.Invariant(DeclCollector != null);
      Contract.Invariant(cce.NonNullElements(Axioms));
      Contract.Invariant(cce.NonNullElements(TypeDecls));
      Contract.Invariant(_backgroundPredicates != null);
    }

    [NotDelayed]
    public SMTLibProcessTheoremProver(SMTLibOptions libOptions, ProverOptions options, VCExpressionGenerator gen,
      SMTLibProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);


      this.options = (SMTLibProverOptions) options;
      this.libOptions = libOptions;
      this.ctx = ctx;
      this.gen = gen;
      usingUnsatCore = false;

      InitializeGlobalInformation();
      SetupAxiomBuilder(gen);

      Namer = (RandomSeed: options.RandomSeed, libOptions.NormalizeNames) switch
      {
        (null, true) => new NormalizeNamer(),
        (null, false) => new KeepOriginalNamer(),
        _ => new RandomiseNamer(new Random(options.RandomSeed.Value))
      };

      ctx.parent = this;
      DeclCollector = new TypeDeclCollector(libOptions, Namer);

      SetupProcess();

      if (libOptions.ImmediatelyAcceptCommands)
      {
        // Prepare for ApiChecker usage
        if (options.LogFilename != null && currentLogFile == null)
        {
          currentLogFile = OpenOutputFile("");
        }

        PrepareCommon();
      }
    }
    
    private ScopedNamer ResetNamer(ScopedNamer namer) {
      return (RandomSeed: options.RandomSeed, libOptions.NormalizeNames) switch
      {
        (null, true) => new NormalizeNamer(namer), 
        (null, false) => new KeepOriginalNamer(namer),
        _ => new RandomiseNamer(namer, new Random(options.RandomSeed.Value))
      }; 
    }

    public override void AssertNamed(VCExpr vc, bool polarity, string name)
    {
      string vcString;
      if (polarity)
      {
        vcString = VCExpr2String(vc, 1);
      }
      else
      {
        vcString = "(not " + VCExpr2String(vc, 1) + ")";
      }

      AssertAxioms();
      SendThisVC(string.Format("(assert (! {0} :named {1}))", vcString, name));
    }

    private void SetupAxiomBuilder(VCExpressionGenerator gen)
    {
      switch (libOptions.TypeEncodingMethod)
      {
        case CommandLineOptions.TypeEncoding.Arguments:
          AxBuilder = new TypeAxiomBuilderArguments(gen);
          AxBuilder.Setup();
          break;
        case CommandLineOptions.TypeEncoding.Monomorphic:
          AxBuilder = null;
          break;
        default:
          AxBuilder = new TypeAxiomBuilderPremisses(gen);
          AxBuilder.Setup();
          break;
      }
    }

    void SetupProcess()
    {
      Process?.Close();
      Process = options.Solver == SolverKind.NoOpWithZ3Options ? new NoopSolver() : new SMTLibProcess(libOptions, options);
      Process.ErrorHandler += HandleProverError;
    }

    void PossiblyRestart()
    {
      if (Process != null && ProcessNeedsRestart) {
        ProcessNeedsRestart = false;
        SetupProcess();
        Process.Send(common.ToString());
      }
    }

    public override ProverContext Context
    {
      get
      {
        Contract.Ensures(Contract.Result<ProverContext>() != null);
        return ctx;
      }
    }

    internal TypeAxiomBuilder AxBuilder { get; private set; }
    private TypeAxiomBuilder CachedAxBuilder;
    private ScopedNamer CachedNamer;
    internal ScopedNamer Namer { get; private set; }
    readonly TypeDeclCollector DeclCollector;
    protected SMTLibSolver Process;
    private bool ProcessNeedsRestart;
    readonly List<string> proverErrors = new List<string>();
    readonly List<string> proverWarnings = new List<string>();
    StringBuilder common = new StringBuilder();
    private string CachedCommon = null;
    protected TextWriter currentLogFile;
    protected volatile ErrorHandler currentErrorHandler;

    private void FeedTypeDeclsToProver()
    {
      foreach (string s in DeclCollector.GetNewDeclarations())
      {
        Contract.Assert(s != null);
        AddTypeDecl(s);
      }
    }

    private string Sanitize(string msg)
    {
      var idx = msg.IndexOf('\n');
      if (idx > 0)
      {
        msg = msg.Replace("\r", "").Replace("\n", "\r\n");
      }

      return msg;
    }

    public override void LogComment(string comment)
    {
      SendCommon("; " + comment);
    }

    private void SendCommon(string s)
    {
      Send(s, true);
    }

    protected void SendThisVC(string s)
    {
      Send(s, false);
    }

    private void Send(string s, bool isCommon)
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

    private void FindDependentTypes(Type type, List<DatatypeTypeCtorDecl> dependentTypes)
    {
      DeclCollector.TypeToStringReg(type);
      if (type.IsSeq)
      {
        FindDependentTypes(type.AsCtor.Arguments[0], dependentTypes);
      }
      MapType mapType = type as MapType;
      if (mapType != null)
      {
        foreach (Type t in mapType.Arguments)
        {
          FindDependentTypes(t, dependentTypes);
        }
        FindDependentTypes(mapType.Result, dependentTypes);
      }
      if (type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl &&
          ctx.KnownDatatypes.Contains(datatypeTypeCtorDecl))
      {
        dependentTypes.Add(datatypeTypeCtorDecl);
      }
    }

    private void PrepareDataTypes()
    {
      if (ctx.KnownDatatypes.Count > 0)
      {
        GraphUtil.Graph<DatatypeTypeCtorDecl> dependencyGraph = new GraphUtil.Graph<DatatypeTypeCtorDecl>();
        foreach (var datatype in ctx.KnownDatatypes)
        {
          dependencyGraph.AddSource(datatype);
          foreach (Function f in datatype.Constructors)
          {
            var dependentTypes = new List<DatatypeTypeCtorDecl>();
            foreach (Variable v in f.InParams)
            {
              FindDependentTypes(v.TypedIdent.Type, dependentTypes);
            }
            foreach (var result in dependentTypes)
            {
              dependencyGraph.AddEdge(datatype, result);
            }
          }
        }

        GraphUtil.StronglyConnectedComponents<DatatypeTypeCtorDecl> sccs =
          new GraphUtil.StronglyConnectedComponents<DatatypeTypeCtorDecl>(dependencyGraph.Nodes, dependencyGraph.Predecessors,
            dependencyGraph.Successors);
        sccs.Compute();
        foreach (GraphUtil.SCC<DatatypeTypeCtorDecl> scc in sccs)
        {
          string datatypesString = "";
          string datatypeConstructorsString = "";
          foreach (var datatype in scc)
          {
            datatypesString += "(" + new SMTLibExprLineariser(libOptions).TypeToString(new CtorType(Token.NoToken, datatype, new List<Type>())) + " 0)";
            string datatypeConstructorString = "";
            foreach (Function f in datatype.Constructors)
            {
              string quotedConstructorName = Namer.GetQuotedName(f, f.Name);
              datatypeConstructorString += "(" + quotedConstructorName + " ";
              foreach (Variable v in f.InParams)
              {
                string quotedSelectorName = Namer.GetQuotedName(v, v.Name + "#" + f.Name);
                datatypeConstructorString += "(" + quotedSelectorName + " " +
                                             DeclCollector.TypeToStringReg(v.TypedIdent.Type) + ") ";
              }

              datatypeConstructorString += ") ";
            }

            datatypeConstructorsString += "(" + datatypeConstructorString + ") ";
          }

          List<string> decls = DeclCollector.GetNewDeclarations();
          foreach (string decl in decls)
          {
            SendCommon(decl);
          }

          SendCommon("(declare-datatypes (" + datatypesString + ") (" + datatypeConstructorsString + "))");
        }
      }
    }

    private void PrepareFunctionDefinitions()
    {
      // Collect all function definitions to be processed
      Stack<Function> functionDefs = new Stack<Function>();
      foreach (Function f in ctx.DefinedFunctions.Keys)
      {
        DeclCollector.AddKnownFunction(f); // add func to knows funcs so that it does not get declared later on
        functionDefs.Push(f);
      }

      // Process each definition, but also be sure to process dependencies first in case one
      // definition calls another.
      // Also check for definition cycles.
      List<string> generatedFuncDefs = new List<string>();
      FunctionDependencyCollector collector = new FunctionDependencyCollector();
      HashSet<Function> definitionAdded = new HashSet<Function>(); // whether definition has been fully processed
      HashSet<Function>
        dependenciesComputed = new HashSet<Function>(); // whether dependencies have already been computed
      while (functionDefs.Count > 0)
      {
        Function f = functionDefs.Peek();
        if (definitionAdded.Contains(f))
        {
          // This definition was already processed (as a dependency of another definition)
          functionDefs.Pop();
          continue;
        }

        // Grab the definition and then compute the dependencies.
        Contract.Assert(ctx.DefinedFunctions.ContainsKey(f));
        VCExprNAry defBody = ctx.DefinedFunctions[f];
        List<Function> dependencies = collector.Collect(defBody[1]);
        bool hasDependencies = false;
        foreach (Function fdep in dependencies)
        {
          if (ctx.DefinedFunctions.ContainsKey(fdep) && !definitionAdded.Contains(fdep))
          {
            // Handle dependencies first
            functionDefs.Push(fdep);
            hasDependencies = true;
          }
        }

        if (!hasDependencies)
        {
          // No dependencies: go ahead and process this definition.
          string funcDef = "(define-fun ";
          var funCall = defBody[0] as VCExprNAry;
          Contract.Assert(funCall != null);
          VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp) funCall.Op;
          Contract.Assert(op != null);
          funcDef += Namer.GetQuotedName(op.Func, op.Func.Name);

          funcDef += " (";
          foreach (var v in funCall.UniformArguments)
          {
            VCExprVar varExpr = v as VCExprVar;
            Contract.Assert(varExpr != null);
            DeclCollector.AddKnownVariable(varExpr); // add var to knows vars so that it does not get declared later on
            string printedName = Namer.GetQuotedLocalName(varExpr, varExpr.Name);
            Contract.Assert(printedName != null);
            funcDef += "(" + printedName + " " + new SMTLibExprLineariser(libOptions).TypeToString(varExpr.Type) + ") ";
          }

          funcDef += ") ";

          funcDef += new SMTLibExprLineariser(libOptions).TypeToString(defBody[0].Type) + " ";
          funcDef += VCExpr2String(defBody[1], -1);
          funcDef += ")";
          generatedFuncDefs.Add(funcDef);
          definitionAdded.Add(f);
          functionDefs.Pop();
        }
        else
        {
          dependenciesComputed.Add(f);
        }
      }

      FlushAxioms(); // Flush all dependencies before flushing function definitions
      generatedFuncDefs.Iter(SendCommon); // Flush function definitions
    }

    private void PrepareCommon()
    {
      if (common.Length == 0)
      {
        SendCommon("(set-option :print-success false)");
        SendCommon("(set-info :smt-lib-version 2.6)");
        if (libOptions.ProduceModel)
        {
          SendCommon("(set-option :produce-models true)");
        }

        foreach (var opt in options.SmtOptions)
        {
          SendCommon("(set-option :" + opt.Option + " " + opt.Value + ")");
        }

        if (!string.IsNullOrEmpty(options.Logic))
        {
          SendCommon("(set-logic " + options.Logic + ")");
        }

        // Set produce-unsat-cores last. It seems there's a bug in Z3 where if we set it earlier its value
        // gets reset by other set-option commands ( https://z3.codeplex.com/workitem/188 )
        if (libOptions.ProduceUnsatCores)
        {
          SendCommon("(set-option :produce-unsat-cores true)");
          this.usingUnsatCore = true;
        }

        SendCommon("; done setting options\n");
        SendCommon(_backgroundPredicates);

        if (options.UseTickleBool)
        {
          SendCommon("(declare-fun tickleBool (Bool) Bool)");
          SendCommon("(assert (and (tickleBool true) (tickleBool false)))");
        }

        if (libOptions.RunDiagnosticsOnTimeout)
        {
          SendCommon("(declare-fun timeoutDiagnostics (Int) Bool)");
        }

        PrepareDataTypes();

        if (libOptions.ProverPreamble != null)
        {
          SendCommon("(include \"" + libOptions.ProverPreamble + "\")");
        }

        PrepareFunctionDefinitions();
      }

      if (!AxiomsAreSetup)
      {
        var axioms = ctx.Axioms;
        var nary = axioms as VCExprNAry;
        if (nary != null && nary.Op == VCExpressionGenerator.AndOp)
        {
          foreach (var expr in nary.UniformArguments)
          {
            var str = VCExpr2String(expr, -1);
            if (str != "true")
            {
              AddAxiom(str);
            }
          }
        }
        else
        {
          AddAxiom(VCExpr2String(axioms, -1));
        }

        AxiomsAreSetup = true;
        CachedAxBuilder = AxBuilder;
        CachedNamer = Namer;
      }
    }

    public override int FlushAxiomsToTheoremProver()
    {
      // we feed the axioms when BeginCheck is called.
      return 0;
    }

    private void FlushAndCacheCommons()
    {
      FlushAxioms();
      if (CachedCommon == null)
      {
        CachedCommon = common.ToString();
      }
    }

    private void FlushAxioms()
    {
      TypeDecls.Iter(SendCommon);
      TypeDecls.Clear();
      foreach (string s in Axioms)
      {
        Contract.Assert(s != null);
        if (s != "true")
        {
          SendCommon("(assert " + s + ")");
        }
      }

      Axioms.Clear();
      //FlushPushedAssertions();
    }

    private void CloseLogFile()
    {
      if (currentLogFile != null)
      {
        currentLogFile.Close();
        currentLogFile = null;
      }
    }

    private void FlushLogFile()
    {
      if (currentLogFile != null)
      {
        currentLogFile.Flush();
      }
    }

    public override void Close()
    {
      base.Close();
      CloseLogFile();
      if (Process != null)
      {
        Process.Close();
      }
    }

    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
    {
      //Contract.Requires(descriptiveName != null);
      //Contract.Requires(vc != null);
      //Contract.Requires(handler != null);

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

      if (HasReset)
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
      if (this.libOptions.EmitDebugInformation) {
        SendThisVC("(set-info :boogie-vc-id " + SmtLibNameUtils.QuoteId(descriptiveName) + ")");
      }
      if (options.Solver == SolverKind.Z3 || options.Solver == SolverKind.NoOpWithZ3Options)
      {
        SendThisVC("(set-option :" + Z3.TimeoutOption + " " + options.TimeLimit + ")");
        SendThisVC("(set-option :" + Z3.RlimitOption + " " + options.ResourceLimit + ")");
        if (options.RandomSeed != null) {
          SendThisVC("(set-option :" + Z3.SmtRandomSeed + " " + options.RandomSeed.Value + ")");
          SendThisVC("(set-option :" + Z3.SatRandomSeed + " " + options.RandomSeed.Value + ")");
        }
      }
      SendThisVC(vcString);

      SendOptimizationRequests();

      FlushLogFile();

      if (Process != null)
      {
        Process.PingPong(); // flush any errors
        Process.NewProblem(descriptiveName);
      }

      if (HasReset)
      {
        DeclCollector.Pop();
        common = new StringBuilder(CachedCommon);
        HasReset = false;
      }

      SendCheckSat();
      FlushLogFile();
    }

    private void SendOptimizationRequests()
    {
      if (options.Solver == SolverKind.Z3 && 0 < OptimizationRequests.Count)
      {
        foreach (var r in OptimizationRequests)
        {
          SendThisVC(r);
        }
      }
    }

    public override void Reset(VCExpressionGenerator gen)
    {
      if (options.Solver == SolverKind.Z3)
      {
        this.gen = gen;
        SendThisVC("(reset)");
        RecoverIfProverCrashedAfterReset();
        SendThisVC("(set-option :" + Z3.RlimitOption + " 0)");

        if (0 < common.Length)
        {
          var c = common.ToString();
          Process.Send(c);
          if (currentLogFile != null)
          {
            currentLogFile.WriteLine(c);
          }
        }

        HasReset = true;
      }
    }

    private void RecoverIfProverCrashedAfterReset()
    {
      if (Process.GetExceptionIfProverDied() is Exception e)
      {
        // We recover the process but don't issue the `(reset)` command that fails.
        SetupProcess();
      }
    }

    public override void FullReset(VCExpressionGenerator gen)
    {
      if (options.Solver == SolverKind.Z3)
      {
        this.gen = gen;
        SendThisVC("(reset)");
        SendThisVC("(set-option :" + Z3.RlimitOption + " 0)");
        Namer.Reset();
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

    private class BadExprFromProver : Exception
    {
    }

    class MyFileParser : SExpr.Parser
    {
      SMTLibProcessTheoremProver parent;

      public MyFileParser(System.IO.StreamReader _sr, SMTLibProcessTheoremProver _parent)
        : base(_sr)
      {
        parent = _parent;
      }

      public override void ParseError(string msg)
      {
        parent.HandleProverError("Error in conjecture file from prover: " + msg);
      }
    }

    private static HashSet<string> usedLogNames = new HashSet<string>();

    private TextWriter OpenOutputFile(string descriptiveName)
    {
      Contract.Requires(descriptiveName != null);
      Contract.Ensures(Contract.Result<TextWriter>() != null);

      string filename = options.LogFilename;
      filename = Helpers.SubstituteAtPROC(descriptiveName, cce.NonNull(filename));
      var curFilename = filename;

      lock (usedLogNames)
      {
        int n = 1;
        while (usedLogNames.Contains(curFilename))
        {
          curFilename = filename + "." + n++;
        }

        usedLogNames.Add(curFilename);
      }

      return new StreamWriter(curFilename, false);
    }

    private void FlushProverWarnings()
    {
      var handler = currentErrorHandler;
      if (handler != null)
      {
        lock (proverWarnings)
        {
          proverWarnings.Iter(handler.OnProverWarning);
          proverWarnings.Clear();
        }
      }
    }

    private void ReportProverError(string err)
    {
      var handler = currentErrorHandler;
      if (handler != null)
      {
        handler.OnProverError(err);
      }
    }

    protected void HandleProverError(string s)
    {
      // Trying to match prover warnings of the form:
      // - for Z3: WARNING: warning_message
      // - for CVC5: query.smt2:222.24: warning: warning_message
      // All other lines are considered to be errors.

      s = s.Replace("\r", "");
      const string ProverWarning = "WARNING: ";
      string errors = "";

      lock (proverWarnings)
      {
        foreach (var line in s.Split('\n'))
        {
          int idx = line.IndexOf(ProverWarning, StringComparison.OrdinalIgnoreCase);
          if (idx >= 0)
          {
            string warn = line.Substring(idx + ProverWarning.Length);
            proverWarnings.Add(warn);
          }
          else
          {
            errors += (line + "\n");
          }
        }
      }

      FlushProverWarnings();

      if (errors == "")
      {
        return;
      }

      lock (proverErrors)
      {
        proverErrors.Add(errors);
        Console.WriteLine("Prover error: " + errors);
      }

      ReportProverError(errors);
    }

    [NoDefaultContract]
    public override Outcome CheckOutcome(ErrorHandler handler, int errorLimit)
    {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var result = CheckOutcomeCore(handler, errorLimit);
      SendThisVC("(pop 1)");
      FlushLogFile();

      return result;
    }

    [NoDefaultContract]
    public override Outcome CheckOutcomeCore(ErrorHandler handler, int errorLimit)
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

        int errorsDiscovered = 0;

        var globalResult = Outcome.Undetermined;

        while (true)
        {
          string[] labels = null;
          bool popLater = false;

          try
          {
            errorsDiscovered++;

            result = GetResponse();

            var reporter = handler as VC.VCGen.ErrorReporter;
            // TODO(wuestholz): Is the reporter ever null?
            if (usingUnsatCore && result == Outcome.Valid && reporter != null && 0 < NamedAssumes.Count)
            {
              if (usingUnsatCore)
              {
                UsedNamedAssumes = new HashSet<string>();
                SendThisVC("(get-unsat-core)");
                var resp = Process.GetProverResponse();
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
              result = RunTimeoutDiagnostics(handler, result, ref popLater);
            }

            if (globalResult == Outcome.Undetermined)
            {
              globalResult = result;
            }

            if (result == Outcome.Invalid)
            {
              Model model = GetErrorModel();
              if (libOptions.SIBoolControlVC)
              {
                labels = new string[0];
              }
              else
              {
                labels = CalculatePath(handler.StartingProcId());
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

          string source = labels[^2];
          string target = labels[^1];
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

    private Outcome RunTimeoutDiagnostics(ErrorHandler handler, Outcome result, ref bool popLater)
    {
      if (libOptions.TraceDiagnosticsOnTimeout) {
        Console.Out.WriteLine("Starting timeout diagnostics with initial time limit {0}.", options.TimeLimit);
      }

      SendThisVC("; begin timeout diagnostics");

      var start = DateTime.UtcNow;
      var unverified = new SortedSet<int>(ctx.TimeoutDiagnosticIDToAssertion.Keys);
      var timedOut = new SortedSet<int>();
      int frac = 2;
      int queries = 0;
      uint timeLimitPerAssertion = 0 < options.TimeLimit
        ? (options.TimeLimit / 100) * libOptions.TimeLimitPerAssertionInPercent
        : 1000;
      while (true) {
        int rem = unverified.Count;
        if (rem == 0) {
          if (0 < timedOut.Count) {
            result = CheckSplit(timedOut, ref popLater, options.TimeLimit, timeLimitPerAssertion, ref queries);
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
        var splitRes = CheckSplit(split, ref popLater, timeLimitPerAssertion, timeLimitPerAssertion,
          ref queries);
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

        string filename = "unknown";
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

      return result;
    }

    private Outcome CheckSplit(SortedSet<int> split, ref bool popLater, uint timeLimit, uint timeLimitPerAssertion,
      ref int queries)
    {
      uint tla = (uint)(timeLimitPerAssertion * split.Count);

      if (popLater)
      {
        SendThisVC("(pop 1)");
      }

      SendThisVC("(push 1)");
      // FIXME: Gross. Timeout should be set in one place! This is also Z3 specific!
      uint newTimeout = (0 < tla && tla < timeLimit) ? tla : timeLimit;
      if (newTimeout > 0)
      {
        SendThisVC(string.Format("(set-option :{0} {1})", Z3.TimeoutOption, newTimeout));
      }

      popLater = true;

      SendThisVC(string.Format("; checking split VC with {0} unverified assertions", split.Count));
      var expr = VCExpressionGenerator.True;
      foreach (var i in ctx.TimeoutDiagnosticIDToAssertion.Keys)
      {
        var lit = VCExprGen.Function(VCExpressionGenerator.TimeoutDiagnosticsOp,
          VCExprGen.Integer(Microsoft.BaseTypes.BigNum.FromInt(i)));
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
      return GetResponse();
    }

    public override string[] CalculatePath(int controlFlowConstant)
    {
      SendThisVC("(get-value ((ControlFlow " + controlFlowConstant + " 0)))");
      var path = new List<string>();
      while (true)
      {
        var response = Process.GetProverResponse();
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


    private class SMTErrorModelConverter
    {
      private List<SExpr> ErrorModelTodo;
      private SMTLibProcessTheoremProver Parent;
      private StringBuilder ErrorModel = new StringBuilder();
      private HashSet<SExpr> TopLevelProcessed = new HashSet<SExpr>();
      private int NumNewArrays = 0;
      private Dictionary<string, int> SortSet = new Dictionary<string, int>();

      private Dictionary<string, Dictionary<string, List<SExpr>>> DataTypes =
        new Dictionary<string, Dictionary<string, List<SExpr>>>();

      private Dictionary<string, SExpr> Functions = new Dictionary<string, SExpr>();

      public SMTErrorModelConverter(SExpr _ErrorModel, SMTLibProcessTheoremProver _Parent)
      {
        ErrorModelTodo = _ErrorModel.Arguments.ToList();
        Parent = _Parent;
      }

      public string Convert()
      {
        ConvertErrorModel(ErrorModel);
        return ErrorModel.ToString();
      }

      bool IsConstArray(SExpr element, SExpr type)
      {
        if (type.Name != "Array")
        {
          return false;
        }

        if (element.Name == "__array_store_all__")
        {
          return true;
        }
        else if (element.Name == "" && element[0].Name == "as" &&
                 element[0][0].Name == "const")
        {
          return true;
        }

        return false;
      }

      SExpr GetConstArrayElement(SExpr element)
      {
        if (element.Name == "__array_store_all__")
        {
          return element[1];
        }
        else if (element.Name == "" && element[0].Name == "as" &&
                 element[0][0].Name == "const")
        {
          return element[1];
        }

        Parent.HandleProverError("Unexpected value: " + element);
        throw new BadExprFromProver();
      }

      void ConstructComplexValue(SExpr element, SExpr type, StringBuilder m)
      {
        if (type.Name == "Array")
        {
          if (element.Name == "store" || IsConstArray(element, type))
          {
            NumNewArrays++;
            m.Append("as-array[k!" + NumNewArrays + ']');
            SExpr[] args = {new SExpr("k!" + NumNewArrays), new SExpr(""), type, element};
            var newElement = new SExpr("define-fun", args);
            TopLevelProcessed.Add(newElement);
            ErrorModelTodo.Add(newElement);
            return;
          }
        }

        ConstructSimpleValue(element, type, m);
      }

      void ConstructSimpleValue(SExpr element, SExpr type, StringBuilder m)
      {
        if (type.Name == "Bool" && element.ArgCount == 0)
        {
          m.Append(element.ToString());
          return;
        }

        if (type.Name == "Int")
        {
          if (element.ArgCount == 0)
          {
            m.Append(element.ToString());
            return;
          }
          else if (element.Name == "-" && element.ArgCount == 1)
          {
            m.Append(element.ToString());
            return;
          }
        }

        if (type.Name == "_" && type.ArgCount == 2 && type[0].Name == "BitVec")
        {
          if (element.Name == "_" && element.ArgCount == 2 &&
              element[0].Name.StartsWith("bv") && element[0].ArgCount == 0 &&
              element[1].Name == type.Arguments[1].Name && element[1].ArgCount == 0)
          {
            m.Append(element[0].Name + '[' + element[1].Name + ']');
            return;
          }
        }

        if (type.Name == "Array")
        {
          while (element.Name == "store")
          {
            ConstructComplexValue(element[1], type[0], m);
            m.Append(" -> ");
            ConstructComplexValue(element[2], type[1], m);
            m.Append("\n  ");
            if (element[0].Name != "store")
            {
              m.Append("else -> ");
            }

            element = element[0];
          }

          if (IsConstArray(element, type))
          {
            ConstructComplexValue(GetConstArrayElement(element), type[1], m);
            return;
          }
          else if (element.Name == "_" && element.ArgCount == 2 &&
                   element[0].Name == "as-array")
          {
            m.Append("as-array[" + element[1].Name + ']');
            return;
          }
        }

        if (type.Name == "Seq")
        {
          if (element.Name == "as")
          {
            m.Append(element[0]);
            return;
          }
        }
        
        if (SortSet.ContainsKey(type.Name) && SortSet[type.Name] == 0)
        {
          var prefix = "@uc_T@" + type.Name.Substring(2) + "_";
          var elementName =  element.Name;
          if (elementName == "as")
          {
            elementName = element[0].Name;
          }
          if (elementName.StartsWith(prefix))
          {
            m.Append(type.Name + "!val!" + elementName.Substring(prefix.Length));
            return;
          }
        }

        if (Functions.ContainsKey(element.Name) &&
            type.Name == Functions[element.Name].Name)
        {
          m.Append(element.Name);
          return;
        }

        if (DataTypes.ContainsKey(type.Name) &&
            DataTypes[type.Name].ContainsKey(element.Name) &&
            element.ArgCount == DataTypes[type.Name][element.Name].Count)
        {
          m.Append("(" + element.Name);
          for (int i = 0; i < element.ArgCount; ++i)
          {
            m.Append(" ");
            ConstructComplexValue(element[i], DataTypes[type.Name][element.Name][i], m);
          }

          m.Append(")");
          return;
        }

        Parent.HandleProverError("Unexpected value: " + element);
        throw new BadExprFromProver();
      }

      void ConstructFunctionArguments(SExpr arguments, List<SExpr> argTypes, StringBuilder[] argValues)
      {
        if (arguments.Name == "and")
        {
          ConstructFunctionArguments(arguments[0], argTypes, argValues);
          ConstructFunctionArguments(arguments[1], argTypes, argValues);
        }
        else if (arguments.Name == "=" &&
                 (arguments[0].Name.StartsWith("_ufmt_") || arguments[0].Name.StartsWith("x!") ||
                  arguments[0].Name.StartsWith("_arg_")))
        {
          int argNum;
          if (arguments[0].Name.StartsWith("_ufmt_"))
          {
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("_uftm_".Length)) - 1;
          }
          else if (arguments[0].Name.StartsWith("_arg_"))
          {
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("_arg_".Length)) - 1;
          }
          else /* if (arguments[0].Name.StartsWith("x!")) */
          {
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("x!".Length)) - 1;
          }

          if (argNum < 0 || argNum >= argTypes.Count)
          {
            Parent.HandleProverError("Unexpected function argument: " + arguments[0]);
            throw new BadExprFromProver();
          }

          if (argValues[argNum] != null)
          {
            Parent.HandleProverError("Function argument defined multiple times: " + arguments[0]);
            throw new BadExprFromProver();
          }

          argValues[argNum] = new StringBuilder();
          ConstructComplexValue(arguments[1], argTypes[argNum], argValues[argNum]);
        }
        else
        {
          Parent.HandleProverError("Unexpected function argument: " + arguments);
          throw new BadExprFromProver();
        }
      }

      void ConstructFunctionElements(SExpr element, List<SExpr> argTypes, SExpr outType, StringBuilder m)
      {
        while (element.Name == "ite")
        {
          StringBuilder[] argValues = new StringBuilder[argTypes.Count];
          ConstructFunctionArguments(element[0], argTypes, argValues);
          foreach (var s in argValues)
          {
            m.Append(s + " ");
          }

          m.Append("-> ");
          ConstructComplexValue(element[1], outType, m);
          m.Append("\n  ");
          if (element[2].Name != "ite")
          {
            m.Append("else -> ");
          }

          element = element[2];
        }

        ConstructComplexValue(element, outType, m);
      }

      void ConstructFunction(SExpr element, SExpr inType, SExpr outType, StringBuilder m)
      {
        List<SExpr> argTypes = new List<SExpr>();

        for (int i = 0; i < inType.ArgCount; ++i)
        {
          if (inType[i].Name != "_ufmt_" + (i + 1) && inType[i].Name != "x!" + (i + 1) &&
              !inType[i].Name.StartsWith("BOUND_VARIABLE_") && inType[i].Name != "_arg_" + (i + 1))
          {
            Parent.HandleProverError("Unexpected function argument: " + inType[i].Name);
            throw new BadExprFromProver();
          }

          argTypes.Add(inType[i][0]);
        }

        ConstructFunctionElements(element, argTypes, outType, m);
      }

      void ConstructDefine(SExpr element, StringBuilder m)
      {
        Debug.Assert(element.Name == "define-fun");

        if (element[1].ArgCount != 0)
        {
          TopLevelProcessed.Add(element);
        }

        m.Append(element[0] + " -> ");
        if (TopLevelProcessed.Contains(element))
        {
          m.Append("{\n  ");
        }

        if (element[1].ArgCount == 0 && element[2].Name == "Array" && !TopLevelProcessed.Contains(element))
        {
          ConstructComplexValue(element[3], element[2], m);
        }
        else if (element[1].ArgCount == 0)
        {
          ConstructSimpleValue(element[3], element[2], m);
        }
        else
        {
          ConstructFunction(element[3], element[1], element[2], m);
        }

        if (TopLevelProcessed.Contains(element))
        {
          m.Append("\n}");
        }

        m.Append("\n");
      }

      void ExtractDataType(SExpr datatypes)
      {
        Debug.Assert(datatypes.Name == "declare-datatypes");

        if (datatypes[0].Name != "" || datatypes[1].Name != "" || datatypes[0].ArgCount != datatypes[1].ArgCount)
        {
          Parent.HandleProverError("Unexpected datatype: " + datatypes);
          throw new BadExprFromProver();
        }

        for (int typeIndex = 0; typeIndex < datatypes[1].ArgCount; typeIndex++)
        {
          SExpr typeDef = datatypes[1][typeIndex];
          Dictionary<string, List<SExpr>> dataTypeConstructors = new Dictionary<string, List<SExpr>>();
          for (int j = 0; j < typeDef.ArgCount; ++j)
          {
            var argumentTypes = new List<SExpr>();
            for (int i = 0; i < typeDef[j].ArgCount; ++i)
            {
              if (typeDef[j][i].ArgCount != 1)
              {
                Parent.HandleProverError("Unexpected datatype constructor: " + typeDef[j]);
                throw new BadExprFromProver();
              }
              argumentTypes.Add(typeDef[j][i][0]);
            }
            dataTypeConstructors[typeDef[j].Name] = argumentTypes;
          }
          DataTypes[datatypes[0][typeIndex].Name] = dataTypeConstructors;
        }
      }

      private void ConvertErrorModel(StringBuilder m)
      {
        if (Parent.options.Solver == SolverKind.Z3 || Parent.options.Solver == SolverKind.CVC5)
        {
          // Datatype declarations are not returned by Z3 or CVC5, so parse common
          // instead. This is not very efficient, but currently not an issue for interfacing
          // with Z3 as this not the normal way of interfacing with Z3.
          var ms = new MemoryStream(Encoding.ASCII.GetBytes(Parent.common.ToString()));
          var sr = new StreamReader(ms);
          SExpr.Parser p = new MyFileParser(sr, null);
          var sexprs = p.ParseSExprs(false);
          foreach (var e in sexprs)
          {
            switch (e.Name)
            {
              case "declare-sort":
                SortSet[e[0].Name] = System.Convert.ToInt32(e[1].Name);
                break;
              case "declare-datatypes":
                ExtractDataType(e);
                break;
            }
          }
        }

        while (ErrorModelTodo.Count > 0)
        {
          var e = ErrorModelTodo[0];
          ErrorModelTodo.RemoveAt(0);

          switch (e.Name)
          {
            case "define-fun":
              ConstructDefine(e, m);
              break;
            case "declare-sort":
              SortSet[e[0].Name] = System.Convert.ToInt32(e[1].Name);
              break;
            case "declare-datatypes":
              ExtractDataType(e);
              break;
            case "declare-fun":
              if (e[1].Name != "" || e[1].ArgCount > 0 || e[2].ArgCount > 0 ||
                  e[2].Name == "Bool" || e[2].Name == "Int")
              {
                Parent.HandleProverError("Unexpected top level model element: " + e.Name);
                throw new BadExprFromProver();
              }
              Functions[e[0].Name] = e[2];
              break;
            case "forall":
              // ignore
              break;
            default:
              Parent.HandleProverError("Unexpected top level model element: " + e.Name);
              throw new BadExprFromProver();
          }
        }
      }
    }

    private Model GetErrorModel()
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
        var resp = Process.GetProverResponse();
        if (resp == null || Process.IsPong(resp))
        {
          break;
        }

        if (theModel != null)
        {
          HandleProverError("Expecting only one model but got many");
        }

        string modelStr = null;
        if (resp.ArgCount >= 1)
        {
          var converter = new SMTErrorModelConverter(resp, this);
          modelStr = converter.Convert();
        }
        else if (resp.ArgCount == 0 && resp.Name.Contains("->"))
        {
          modelStr = resp.Name;
        }
        else
        {
          HandleProverError("Unexpected prover response getting model: " + resp.ToString());
        }

        List<Model> models = null;
        try
        {
          switch (options.Solver)
          {
            case SolverKind.Z3:
            case SolverKind.CVC5:
              models = Model.ParseModels(new StringReader("Error model: \n" + modelStr), Namer.GetOriginalName);
              break;
            default:
              Debug.Assert(false);
              return null;
          }
        }
        catch (ArgumentException exn)
        {
          HandleProverError("Model parsing error: " + exn.Message);
        }

        if (models == null)
        {
          HandleProverError("Could not parse any models");
        }
        else if (models.Count == 0)
        {
          HandleProverError("Could not parse any models");
        }
        else if (models.Count > 1)
        {
          HandleProverError("Expecting only one model but got many");
        }
        else
        {
          theModel = models[0];
        }
      }

      return theModel;
    }

    private Outcome GetResponse()
    {
      var result = Outcome.Undetermined;
      var wasUnknown = false;

      Process.Ping();

      while (true)
      {
        var resp = Process.GetProverResponse();
        if (resp == null || Process.IsPong(resp))
        {
          break;
        }

        switch (resp.Name)
        {
          case "unsat":
            result = Outcome.Valid;
            break;
          case "sat":
            result = Outcome.Invalid;
            break;
          case "unknown":
            result = Outcome.Invalid;
            wasUnknown = true;
            break;
          case "objectives":
            // We ignore this.
            break;
          case "error":
            if (resp.Arguments.Length == 1 && resp.Arguments[0].IsId &&
                (resp.Arguments[0].Name.Contains("max. resource limit exceeded")
                 || resp.Arguments[0].Name.Contains("resource limits reached")))
            {
              currentErrorHandler.OnResourceExceeded("max resource limit");
              result = Outcome.OutOfResource;
            }
            else
            {
              HandleProverError("Unexpected prover response: " + resp.ToString());
            }

            break;
          default:
            HandleProverError("Unexpected prover response: " + resp.ToString());
            break;
        }
      }

      if (wasUnknown)
      {
        SendThisVC("(get-info :reason-unknown)");
        Process.Ping();
        while (true)
        {
          var resp = Process.GetProverResponse();
          if (resp == null || Process.IsPong(resp))
          {
            break;
          }

          if (resp.ArgCount == 1 && resp.Name == ":reason-unknown")
          {
            switch (resp[0].Name)
            {
              case "incomplete":
              case "(incomplete quantifiers)":
              case "(incomplete (theory arithmetic))":
              case "smt tactic failed to show goal to be sat/unsat (incomplete (theory arithmetic))":
                break;
              case "memout":
                currentErrorHandler.OnResourceExceeded("memory");
                result = Outcome.OutOfMemory;
                ProcessNeedsRestart = true;
                break;
              case "timeout":
                currentErrorHandler.OnResourceExceeded("timeout");
                result = Outcome.TimeOut;
                break;
              case "canceled":
                // both timeout and max resource limit are reported as
                // canceled in version 4.4.1 
                if (this.options.TimeLimit > 0)
                {
                  currentErrorHandler.OnResourceExceeded("timeout");
                  result = Outcome.TimeOut;
                }
                else
                {
                  currentErrorHandler.OnResourceExceeded("max resource limit");
                  result = Outcome.OutOfResource;
                }

                break;
              case "max. resource limit exceeded":
              case "resource limits reached":
              case "(resource limits reached)":
                currentErrorHandler.OnResourceExceeded("max resource limit");
                result = Outcome.OutOfResource;
                break;
              default:
                result = Outcome.Undetermined;
                HandleProverError("Unexpected prover response (getting info about 'unknown' response): " + resp.ToString());
                break;
            }
          }
          else
          {
            result = Outcome.Undetermined;
            HandleProverError("Unexpected prover response (getting info about 'unknown' response): " + resp.ToString());
          }
        }
      }

      return result;
    }

    readonly IList<string> OptimizationRequests = new List<string>();

    protected string VCExpr2String(VCExpr expr, int polarity)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<string>() != null);

      lock (gen)
      {
        DateTime start = DateTime.UtcNow;

        // handle the types in the VCExpr
        VCExpr exprWithoutTypes;
        switch (libOptions.TypeEncodingMethod)
        {
          case CommandLineOptions.TypeEncoding.Arguments:
          {
            TypeEraser eraser = new TypeEraserArguments((TypeAxiomBuilderArguments) AxBuilder, gen);
            exprWithoutTypes = AxBuilder.Cast(eraser.Erase(expr, polarity), Type.Bool);
            break;
          }
          case CommandLineOptions.TypeEncoding.Monomorphic:
          {
            exprWithoutTypes = expr;
            break;
          }
          default:
          {
            TypeEraser eraser = new TypeEraserPremisses((TypeAxiomBuilderPremisses) AxBuilder, gen);
            exprWithoutTypes =  AxBuilder.Cast(eraser.Erase(expr, polarity), Type.Bool);
            break;
          }
        }
        Contract.Assert(exprWithoutTypes != null);

        LetBindingSorter letSorter = new LetBindingSorter(gen);
        Contract.Assert(letSorter != null);

        VCExpr sortedExpr = letSorter.Mutate(exprWithoutTypes, true);
        Contract.Assert(sortedExpr != null);
        DeclCollector.Collect(sortedExpr);
        FeedTypeDeclsToProver();

        if (AxBuilder != null)
        {
          VCExpr sortedAxioms = letSorter.Mutate(AxBuilder.GetNewAxioms(), true);
          Contract.Assert(sortedAxioms != null);
          DeclCollector.Collect(sortedAxioms);
          FeedTypeDeclsToProver();
          AddAxiom(SMTLibExprLineariser.ToString(sortedAxioms, Namer, libOptions, options, namedAssumes: NamedAssumes));
        }

        string res = SMTLibExprLineariser.ToString(sortedExpr, Namer, libOptions, options, NamedAssumes, OptimizationRequests);
        Contract.Assert(res != null);

        if (libOptions.Trace)
        {
          DateTime end = DateTime.UtcNow;
          TimeSpan elapsed = end - start;
          if (elapsed.TotalSeconds > 0.5)
          {
            Console.WriteLine("Linearising   [{0} s]", elapsed.TotalSeconds);
          }
        }

        return res;
      }
    }

    // the list of all known axioms, where have to be included in each
    // verification condition
    private readonly List<string /*!>!*/> Axioms = new List<string /*!*/>();
    private bool AxiomsAreSetup = false;
    private bool HasReset = false;


    // similarly, a list of function/predicate declarations
    private readonly List<string /*!>!*/> TypeDecls = new List<string /*!*/>();

    protected void AddAxiom(string axiom)
    {
      Contract.Requires(axiom != null);
      Axioms.Add(axiom);
      //      if (thmProver != null) {
      //        LogActivity(":assume " + axiom);
      //        thmProver.AddAxioms(axiom);
      //      }
    }

    protected void AddTypeDecl(string decl)
    {
      Contract.Requires(decl != null);
      TypeDecls.Add(decl);
      //     if (thmProver != null) {
      //       LogActivity(decl);
      //       thmProver.Feed(decl, 0);
      //     }
    }

    ////////////////////////////////////////////////////////////////////////////

    private static string _backgroundPredicates;

    void InitializeGlobalInformation()
    {
      Contract.Ensures(_backgroundPredicates != null);
      //throws ProverException, System.IO.FileNotFoundException;
      if (_backgroundPredicates == null)
      {
        if (libOptions.TypeEncodingMethod == CommandLineOptions.TypeEncoding.Monomorphic)
        {
          _backgroundPredicates = "";
        }
        else
        {
          _backgroundPredicates = @"
(set-info :category ""industrial"")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)";
        }
      }
    }

    public override VCExpressionGenerator VCExprGen
    {
      get { return this.gen; }
    }

    //// Push/pop interface

    //List<string> pushedAssertions = new List<string>();
    //int numRealPushes;
    public override string VCExpressionToString(VCExpr vc)
    {
      return VCExpr2String(vc, 1);
    }

    public override void PushVCExpression(VCExpr vc)
    {
      throw new NotImplementedException();
    }

    public override void Pop()
    {
      SendThisVC("(pop 1)");
      DeclCollector.Pop();
    }

    public override int NumAxiomsPushed()
    {
      throw new NotImplementedException();
      //return numRealPushes + pushedAssertions.Count;
    }

    private void FlushPushedAssertions()
    {
      throw new NotImplementedException();
    }

    public override void Assert(VCExpr vc, bool polarity, bool isSoft = false, int weight = 1, string name = null)
    {
      OptimizationRequests.Clear();
      string assert = "assert";
      if (options.Solver == SolverKind.Z3 && isSoft)
      {
        assert += "-soft";
      }

      var expr = polarity ? VCExpr2String(vc, 1) : "(not\n" + VCExpr2String(vc, 1) + "\n)";
      if (options.Solver == SolverKind.Z3 && isSoft)
      {
        expr += " :weight " + weight;
      }

      if (name != null)
      {
        expr = "(! " + expr + ":named " + name + ")";
      }

      AssertAxioms();
      SendThisVC("(" + assert + " " + expr + ")");
      SendOptimizationRequests();
    }

    public override List<string> UnsatCore()
    {
      SendThisVC("(get-unsat-core)");
      var resp = Process.GetProverResponse().ToString();
      if (resp == "" || resp == "()")
      {
        return null;
      }

      if (resp[0] == '(')
      {
        resp = resp.Substring(1, resp.Length - 2);
      }

      var ucore = resp.Split(' ').ToList();
      return ucore;
    }

    public override void DefineMacro(Macro f, VCExpr vc)
    {
      DeclCollector.AddKnownFunction(f);
      string printedName = Namer.GetQuotedName(f, f.Name);
      var argTypes = f.InParams.Cast<Variable>().MapConcat(p => DeclCollector.TypeToStringReg(p.TypedIdent.Type), " ");
      string decl = "(define-fun " + printedName + " (" + argTypes + ") " +
                    DeclCollector.TypeToStringReg(f.OutParams[0].TypedIdent.Type) + " " + VCExpr2String(vc, 1) + ")";
      AssertAxioms();
      SendThisVC(decl);
    }

    public override void AssertAxioms()
    {
      FlushAxioms();
    }

    public override void Check()
    {
      PrepareCommon();
      SendCheckSat();
      FlushLogFile();
    }

    public void SendCheckSat()
    {
      UsedNamedAssumes = null;
      SendThisVC("(check-sat)");
    }

    public override void SetTimeout(uint ms)
    {
      options.TimeLimit = ms;
    }

    public override void SetRlimit(uint limit)
    {
      options.ResourceLimit = limit;
    }

    public override int GetRCount() 
    {
      SendThisVC("(get-info :rlimit)");
      var resp = Process.GetProverResponse();
      try
      {
        return int.Parse(resp[0].Name);
      }
      catch
      {
        // If anything goes wrong with parsing the response from the solver,
        // it's better to be able to continue, even with uninformative data.
        lock (proverWarnings)
        {
          proverWarnings.Add($"Failed to parse resource count from solver. Got: {resp.ToString()}");
        }
        return -1;
      }
    }

    object ParseValueFromProver(SExpr expr)
    {
      return expr.ToString().Replace(" ", "").Replace("(", "").Replace(")", "");
    }

    SExpr ReduceLet(SExpr expr)
    {
      if (expr.Name != "let")
      {
        return expr;
      }

      var bindings = expr.Arguments[0].Arguments;
      var subexpr = expr.Arguments[1];

      var dict = new Dictionary<string, SExpr>();
      foreach (var binding in bindings)
      {
        Contract.Assert(binding.ArgCount == 1);
        dict.Add(binding.Name, binding.Arguments[0]);
      }

      Contract.Assert(!dict.ContainsKey(subexpr.Name));

      var workList = new Stack<SExpr>();
      workList.Push(subexpr);
      while (workList.Count > 0)
      {
        var curr = workList.Pop();
        for (int i = 0; i < curr.ArgCount; i++)
        {
          var arg = curr.Arguments[i];
          if (dict.ContainsKey(arg.Name))
          {
            curr.Arguments[i] = dict[arg.Name];
          }
          else
          {
            workList.Push(arg);
          }
        }
      }

      return subexpr;
    }

    object GetArrayFromProverResponse(SExpr resp)
    {
      resp = ReduceLet(resp);
      var dict = GetArrayFromArrayExpr(resp);
      if (dict == null)
      {
        dict = GetArrayFromProverLambdaExpr(resp);
      }

      if (dict == null)
      {
        return null;
      }

      var str = new StringWriter();
      str.Write("{");
      foreach (var entry in dict)
      {
        if (entry.Key != "*")
        {
          str.Write("\"{0}\":{1},", entry.Key, entry.Value);
        }
      }

      if (dict.ContainsKey("*"))
      {
        str.Write("\"*\":{0}", dict["*"]);
      }

      str.Write("}");
      return str.ToString();
    }

    Dictionary<string, object> GetArrayFromProverLambdaExpr(SExpr resp)
    {
      var dict = new Dictionary<string, object>();
      if (resp.Name == "lambda" && resp.ArgCount == 2)
      {
        // TODO: multiple indices, as (lambda (() (x!1 Int) (x!2 Int)) ...)
        var indexVar = resp.Arguments[0].Arguments[0].Name;

        var cases = resp.Arguments[1];
        while (cases != null)
        {
          if (cases.Name == "ite")
          {
            var condition = cases.Arguments[0];
            var positive = cases.Arguments[1];
            var negative = cases.Arguments[2];

            // TODO: multiple index conditions, as (and (= x!1 5) (= x!2 3))
            // TODO: nested arrays, as (ite (...) (_ as-array k!5) (_ as-array k!3))

            if (condition.Name != "=")
            {
              throw new VCExprEvaluationException();
            }

            if (condition.Arguments[0].Name != indexVar)
            {
              throw new VCExprEvaluationException();
            }

            var index = ParseValueFromProver(condition.Arguments[1]);
            var value = ParseValueFromProver(positive);

            dict.Add(index.ToString(), value);

            cases = negative;
          }
          else if (cases.IsId)
          {
            var value = ParseValueFromProver(cases);
            dict.Add("*", value);
            cases = null;
          }
          else
          {
            throw new VCExprEvaluationException();
          }
        }
      }

      return dict.Count > 0 ? dict : null;
    }

    Dictionary<string, object> GetArrayFromArrayExpr(SExpr resp)
    {
      var dict = new Dictionary<string, object>();
      var curr = resp;
      while (curr != null)
      {
        if (curr.Name == "store")
        {
          var ary = curr.Arguments[0];
          var indices = curr.Arguments.Skip(1).Take(curr.ArgCount - 2).Select(ParseValueFromProver).ToArray();
          var val = curr.Arguments[curr.ArgCount - 1];
          dict.Add(String.Join(",", indices), ParseValueFromProver(val));
          curr = ary;
        }
        else if (curr.Name == "" && curr.ArgCount == 2 && curr.Arguments[0].Name == "as")
        {
          var val = curr.Arguments[1];
          dict.Add("*", ParseValueFromProver(val));
          curr = null;
        }
        else
        {
          return null;
        }
      }

      return dict.Count > 0 ? dict : null;
    }

    public override object Evaluate(VCExpr expr)
    {
      string vcString = VCExpr2String(expr, 1);
      SendThisVC("(get-value (" + vcString + "))");
      var resp = Process.GetProverResponse();
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

      var ary = GetArrayFromProverResponse(resp);
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

    /// <summary>
    /// Extra state for ApiChecker (used by stratifiedInlining)
    /// </summary>
    static int nameCounter = 0;

    public override Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore, ErrorHandler handler)
    {
      unsatCore = new List<int>();

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

      var outcome = CheckOutcomeCore(handler, libOptions.ErrorLimit);

      if (outcome != Outcome.Valid)
      {
        Pop();
        return outcome;
      }

      Contract.Assert(usingUnsatCore, "SMTLib prover not setup for computing unsat cores");
      SendThisVC("(get-unsat-core)");
      var resp = Process.GetProverResponse();
      unsatCore = new List<int>();
      if (resp.Name != "")
      {
        unsatCore.Add(nameToAssumption[resp.Name]);
      }

      foreach (var s in resp.Arguments)
      {
        unsatCore.Add(nameToAssumption[s.Name]);
      }

      FlushLogFile();
      Pop();
      return outcome;
    }

    public override void Push()
    {
      SendThisVC("(push 1)");
      DeclCollector.Push();
    }

    public override Outcome CheckAssumptions(List<VCExpr> hardAssumptions, List<VCExpr> softAssumptions,
      out List<int> unsatisfiedSoftAssumptions, ErrorHandler handler)
    {
      unsatisfiedSoftAssumptions = new List<int>();

      // First, convert both hard and soft assumptions to SMTLIB strings
      List<string> hardAssumptionStrings = new List<string>();
      foreach (var a in hardAssumptions)
      {
        hardAssumptionStrings.Add(VCExpr2String(a, 1));
      }

      List<string> currAssumptionStrings = new List<string>();
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
      Outcome outcome = GetResponse();
      if (outcome != Outcome.Invalid)
      {
        Pop();
        return outcome;
      }

      int k = 0;
      List<string> relaxVars = new List<string>();
      while (true)
      {
        Push();
        foreach (var a in currAssumptionStrings)
        {
          SendThisVC("(assert " + a + ")");
        }

        Check();
        outcome = CheckOutcomeCore(handler, libOptions.ErrorLimit);
        if (outcome != Outcome.Valid)
        {
          break;
        }

        Pop();
        string relaxVar = "relax_" + k;
        relaxVars.Add(relaxVar);
        SendThisVC("(declare-fun " + relaxVar + " () Int)");
        List<string> nextAssumptionStrings = new List<string>();
        for (int i = 0; i < currAssumptionStrings.Count; i++)
        {
          string constraint = "(= " + relaxVar + " " + i + ")";
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
          var resp = Process.GetProverResponse();
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
      return outcome;
    }
  }
  
  public class SMTLibProverContext : DeclFreeProverContext
  {
    internal SMTLibProcessTheoremProver parent;
    
    public readonly HashSet<DatatypeTypeCtorDecl> KnownDatatypes = new HashSet<DatatypeTypeCtorDecl>();
    
    public readonly Dictionary<Function, VCExprNAry> DefinedFunctions = new Dictionary<Function, VCExprNAry>();

    public SMTLibProverContext(VCExpressionGenerator gen,
      VCGenerationOptions genOptions)
      : base(gen, genOptions)
    {
    }

    protected SMTLibProverContext(SMTLibProverContext par)
      : base(par)
    {
    }

    public override object Clone()
    {
      return new SMTLibProverContext(this);
    }

    public override string Lookup(VCExprVar var)
    {
      VCExprVar v = parent.AxBuilder?.TryTyped2Untyped(var);
      if (v != null)
      {
        var = v;
      }

      return parent.Namer.GetOriginalName(parent.Namer.Lookup(var));
    }

    public override void DeclareFunction(Function f, string attributes)
    {
      if (f.DefinitionBody != null)
      {
        DefinedFunctions.Add(f, (VCExprNAry) translator.Translate(f.DefinitionBody));
      }

      base.DeclareFunction(f, attributes);
    }

    public override void DeclareType(TypeCtorDecl t, string attributes)
    {
      if (t is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        if (datatypeTypeCtorDecl.Arity > 0)
        {
          throw new ProverException("Polymorphic datatypes are not supported");
        }
        KnownDatatypes.Add(datatypeTypeCtorDecl);
      }
      base.DeclareType(t, attributes);
    }

    // Return the datatype of the given name if there is one, null otherwise.
    public DatatypeTypeCtorDecl LookupDatatype(string name)
    {
      foreach (var datatype in KnownDatatypes)
      {
        if (name == datatype.ToString())
        {
          return datatype;
        }
      }

      return null;
    }
  }

  public class Factory : ProverFactory
  {
    public override object SpawnProver(SMTLibOptions libOptions, ProverOptions options, object ctxt)
    {
      //Contract.Requires(ctxt != null);
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      return this.SpawnProver(libOptions, options,
        cce.NonNull((SMTLibProverContext) ctxt).ExprGen,
        cce.NonNull((SMTLibProverContext) ctxt));
    }

    public override object NewProverContext(ProverOptions options)
    {
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      VCExpressionGenerator gen = new VCExpressionGenerator();
      List<string> /*!>!*/
        proverCommands = new List<string /*!*/>();
      proverCommands.Add("smtlib");
      var opts = (SMTLibProverOptions) options;
      if (opts.Solver == SolverKind.Z3)
      {
        proverCommands.Add("z3");
      }
      else
      {
        proverCommands.Add("external");
      }

      VCGenerationOptions genOptions = new VCGenerationOptions(proverCommands);
      return new SMTLibProverContext(gen, genOptions);
    }

    public override ProverOptions BlankProverOptions()
    {
      return new SMTLibProverOptions();
    }

    protected virtual SMTLibProcessTheoremProver SpawnProver(SMTLibOptions libOptions, ProverOptions options,
      VCExpressionGenerator gen,
      SMTLibProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      Contract.Ensures(Contract.Result<SMTLibProcessTheoremProver>() != null);
      return new SMTLibProcessTheoremProver(libOptions, options, gen, ctx);
    }
  }
}
