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
//using ExternalProver;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.Clustering;
using Microsoft.Boogie.TypeErasure;
using System.Text;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibProcessTheoremProver : ProverInterface
  {
    private readonly SMTLibProverContext ctx;
    private readonly VCExpressionGenerator gen;
    private readonly SMTLibProverOptions options;
    private bool usingUnsatCore;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(ctx != null);
      Contract.Invariant(AxBuilder != null);
      Contract.Invariant(Namer != null);
      Contract.Invariant(DeclCollector != null);
      Contract.Invariant(cce.NonNullElements(Axioms));
      Contract.Invariant(cce.NonNullElements(TypeDecls));
      Contract.Invariant(_backgroundPredicates != null);

    }


    [NotDelayed]
    public SMTLibProcessTheoremProver(ProverOptions options, VCExpressionGenerator gen,
                                      SMTLibProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      InitializeGlobalInformation("UnivBackPred2.smt2");

      this.options = (SMTLibProverOptions)options;
      this.ctx = ctx;
      this.gen = gen;
      this.usingUnsatCore = false;

      TypeAxiomBuilder axBuilder;
      switch (CommandLineOptions.Clo.TypeEncodingMethod) {
        case CommandLineOptions.TypeEncoding.Arguments:
          axBuilder = new TypeAxiomBuilderArguments(gen);
          axBuilder.Setup();
          break;
        case CommandLineOptions.TypeEncoding.Monomorphic:
          axBuilder = new TypeAxiomBuilderPremisses(gen);
          break;
        default:
          axBuilder = new TypeAxiomBuilderPremisses(gen);
          axBuilder.Setup();
          break;
      }

      AxBuilder = axBuilder;
      Namer = new SMTLibNamer();
      ctx.parent = this;
      this.DeclCollector = new TypeDeclCollector((SMTLibProverOptions)options, Namer);

      SetupProcess();

      if (CommandLineOptions.Clo.StratifiedInlining > 0)
      {
          // Prepare for ApiChecker usage
          if (options.LogFilename != null && currentLogFile == null)
          {
              currentLogFile = OpenOutputFile("");
          }
          if (CommandLineOptions.Clo.ProcedureCopyBound > 0 || CommandLineOptions.Clo.UseUnsatCoreForInlining)
          {
              SendThisVC("(set-option :produce-unsat-cores true)");
              this.usingUnsatCore = true;
          }
          PrepareCommon();
      }
    }

    void SetupProcess()
    {
      if (!this.options.UseZ3)
        return;

      if (Process != null) return;

      var path = this.options.ProverPath;
      if (path == null)
        path = Z3.ExecutablePath();
      var psi = SMTLibProcess.ComputerProcessStartInfo(path, "AUTO_CONFIG=false -smt2 -in");
      Process = new SMTLibProcess(psi, this.options);
      Process.ErrorHandler += this.HandleProverError;
    }


    void PossiblyRestart()
    {
      if (Process != null && Process.NeedsRestart) {
        Process.Close();
        Process = null;
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

    internal readonly TypeAxiomBuilder AxBuilder;
    internal readonly UniqueNamer Namer;
    readonly TypeDeclCollector DeclCollector;
    SMTLibProcess Process;
    readonly List<string> proverErrors = new List<string>();
    readonly List<string> proverWarnings = new List<string>();
    readonly StringBuilder common = new StringBuilder();
    TextWriter currentLogFile;
    volatile ErrorHandler currentErrorHandler;

    private void FeedTypeDeclsToProver()
    {
      foreach (string s in DeclCollector.GetNewDeclarations()) {
        Contract.Assert(s != null);
        AddTypeDecl(s);
      }
    }

    private string Sanitize(string msg)
    {
      var idx = msg.IndexOf('\n');
      if (idx > 0)
        msg = msg.Replace("\r", "").Replace("\n", "\r\n");
      return msg;
    }

    private void SendCommon(string s)
    {
      Send(s, true);
    }

    private void SendThisVC(string s)
    {
      Send(s, false);
    }

    private void Send(string s, bool isCommon)
    {
      s = Sanitize(s);

      if (isCommon)
        common.Append(s).Append("\r\n");

      if (Process != null)
        Process.Send(s);
      if (currentLogFile != null)
        currentLogFile.WriteLine(s);
    }

    private void PrepareCommon()
    {
      if (common.Length == 0) {
        SendCommon("(set-option :print-success false)");
        SendCommon("(set-info :smt-lib-version 2.0)");
        if (options.ProduceModel())
          SendCommon("(set-option :produce-models true)");
        foreach (var opt in options.SmtOptions) {
          SendCommon("(set-option :" + opt.Option + " " + opt.Value + ")");
        }

        if (!string.IsNullOrEmpty(options.Logic)) {
          SendCommon("(set-logic " + options.Logic + ")");
        }

        SendCommon("; done setting options\n");
        SendCommon(_backgroundPredicates);

        
        if (ctx.KnownDatatypeConstructors.Count > 0) {
          string datatypeString = "";
          foreach (CtorType datatype in ctx.KnownDatatypeConstructors.Keys) {
            datatypeString += "(" + SMTLibExprLineariser.TypeToString(datatype) + " ";
            foreach (Function f in ctx.KnownDatatypeConstructors[datatype]) {
              string quotedConstructorName = Namer.GetQuotedName(f, f.Name);
              if (f.InParams.Length == 0) {
                datatypeString += quotedConstructorName + " ";
              }
              else {
                datatypeString += "(" + quotedConstructorName + " ";
                foreach (Variable v in f.InParams) {
                  string quotedSelectorName = Namer.GetQuotedName(v, v.Name + "#" + f.Name);
                  datatypeString += "(" + quotedSelectorName + " " + DeclCollector.TypeToStringReg(v.TypedIdent.Type) + ") ";
                }
                datatypeString += ") ";
              }
            }
            datatypeString += ") ";
          }
          List<string> decls = DeclCollector.GetNewDeclarations();
          foreach (string decl in decls) {
            SendCommon(decl);
          }
          SendCommon("(declare-datatypes () (" + datatypeString + "))");
        }
      }

      if (!AxiomsAreSetup) {
        var axioms = ctx.Axioms;
        var nary = axioms as VCExprNAry;
        if (nary != null && nary.Op == VCExpressionGenerator.AndOp)
          foreach (var expr in nary.UniformArguments) {
            var str = VCExpr2String(expr, -1);
            if (str != "true")
              AddAxiom(str);
          } else
          AddAxiom(VCExpr2String(axioms, -1));
        AxiomsAreSetup = true;
      }
    }

    public override int FlushAxiomsToTheoremProver()
    {
      // we feed the axioms when begincheck is called.
      return 0;
    }

    private void FlushAxioms()
    {
      TypeDecls.Iter(SendCommon);
      TypeDecls.Clear();
      foreach (string s in Axioms) {
        Contract.Assert(s != null);
        if (s != "true")
          SendCommon("(assert " + s + ")");
      }
      Axioms.Clear();
      //FlushPushedAssertions();
    }

    private void CloseLogFile()
    {
      if (currentLogFile != null) {
        currentLogFile.Close();
        currentLogFile = null;
      }
    }

    private void FlushLogFile()
    {
      if (currentLogFile != null) {
        currentLogFile.Flush();
      }
    }

    public override void Close()
    {
      base.Close();
      CloseLogFile();
      if (Process != null)
        Process.Close();
    }

    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
    {
      //Contract.Requires(descriptiveName != null);
      //Contract.Requires(vc != null);
      //Contract.Requires(handler != null);

      if (options.SeparateLogFiles) CloseLogFile(); // shouldn't really happen

      if (options.LogFilename != null && currentLogFile == null) {
        currentLogFile = OpenOutputFile(descriptiveName);
        currentLogFile.Write(common.ToString());
      }

      PrepareCommon();
      string vcString = "(assert (not\n" + VCExpr2String(vc, 1) + "\n))";
      FlushAxioms();

      PossiblyRestart();

      SendThisVC("(push 1)");
      SendThisVC("(set-info :boogie-vc-id " + SMTLibNamer.QuoteId(descriptiveName) + ")");
      SendThisVC(vcString);
      FlushLogFile();

      if (Process != null) {
        Process.PingPong(); // flush any errors

        if (Process.Inspector != null)
          Process.Inspector.NewProblem(descriptiveName, vc, handler);
      }

      SendThisVC("(check-sat)");
      FlushLogFile();
    }

    private static HashSet<string> usedLogNames = new HashSet<string>();

    private TextWriter OpenOutputFile(string descriptiveName)
    {
      Contract.Requires(descriptiveName != null);
      Contract.Ensures(Contract.Result<TextWriter>() != null);

      string filename = options.LogFilename;
      filename = Helpers.SubstituteAtPROC(descriptiveName, cce.NonNull(filename));
      var curFilename = filename;

      lock (usedLogNames) {
        int n = 1;
        while (usedLogNames.Contains(curFilename)) {
          curFilename = filename + "." + n++;
        }
        usedLogNames.Add(curFilename);
      }

      return new StreamWriter(curFilename, false);
    }

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

    private void HandleProverError(string s)
    {
      s = s.Replace("\r", "");
      lock (proverWarnings) {
        while (s.StartsWith("WARNING: ")) {
          var idx = s.IndexOf('\n');
          var warn = s;
          if (idx > 0) {
            warn = s.Substring(0, idx);
            s = s.Substring(idx + 1);
          } else {
            s = "";
          }
          warn = warn.Substring(9);
          proverWarnings.Add(warn);
        }
      }

      FlushProverWarnings();

      if (s == "") return;

      lock (proverErrors) {
        proverErrors.Add(s);
        Console.WriteLine("Prover error: " + s);
      }
    }

    [NoDefaultContract]
    public override Outcome CheckOutcome(ErrorHandler handler)
    {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var result = CheckOutcomeCore(handler);
      SendThisVC("(pop 1)");
      FlushLogFile();

      return result;
    }

    [NoDefaultContract]
    public override Outcome CheckOutcomeCore(ErrorHandler handler)
    {  
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      
      var result = Outcome.Undetermined;

      if (Process == null)
        return result;

      try {
        currentErrorHandler = handler;
        FlushProverWarnings();

        var errorsLeft = CommandLineOptions.Clo.ProverCCLimit;
        if (errorsLeft < 1)
          errorsLeft = 1;

        var globalResult = Outcome.Undetermined;

        while (true) {
          errorsLeft--;
          string[] labels = null;

          result = GetResponse();
          if (globalResult == Outcome.Undetermined)
            globalResult = result;

          if (result == Outcome.Invalid) {
            IList<string> xlabels;
            if (CommandLineOptions.Clo.UseLabels) {
              labels = GetLabelsInfo();
              xlabels = labels.Select(a => a.Replace("@", "").Replace("+", "")).ToList();
            }
            else {
              labels = CalculatePath(0);
              xlabels = labels;
            }
            ErrorModel errorModel = GetErrorModel();
            handler.OnModel(xlabels, errorModel);
          }

          if (labels == null || errorsLeft == 0) break;

          if (CommandLineOptions.Clo.UseLabels) {
            var negLabels = labels.Where(l => l.StartsWith("@")).ToArray();
            var posLabels = labels.Where(l => !l.StartsWith("@"));
            Func<string, string> lbl = (s) => SMTLibNamer.QuoteId(SMTLibNamer.LabelVar(s));
            if (!options.MultiTraces)
              posLabels = Enumerable.Empty<string>();
            var conjuncts = posLabels.Select(s => "(not " + lbl(s) + ")").Concat(negLabels.Select(lbl)).ToArray();
            var expr = conjuncts.Length == 1 ? conjuncts[0] : ("(or " + conjuncts.Concat(" ") + ")");
            SendThisVC("(assert " + expr + ")");
            SendThisVC("(check-sat)");
          }
          else {
            string source = labels[labels.Length - 2];
            string target = labels[labels.Length - 1];
            SendThisVC("(assert (not (= (ControlFlow 0 " + source + ") (- " + target + "))))");
            SendThisVC("(check-sat)");
          }
        }

        FlushLogFile();

        if (CommandLineOptions.Clo.RestartProverPerVC && Process != null)
          Process.NeedsRestart = true;

        return globalResult;

      } finally {
        currentErrorHandler = null;
      }
    }

    public override string[] CalculatePath(int controlFlowConstant) {
      SendThisVC("(get-value ((ControlFlow " + controlFlowConstant + " 0)))");
      var path = new List<string>();
      while (true) {
        var resp = Process.GetProverResponse();
        if (resp == null) break;
        if (!(resp.Name == "" && resp.ArgCount == 1)) break;
        resp = resp.Arguments[0];
        if (!(resp.Name == "" && resp.ArgCount == 2)) break;
        resp = resp.Arguments[1];
        var v = resp.Name;
        if (v == "-" && resp.ArgCount == 1) {
          v = resp.Arguments[0].Name;
          path.Add(v);
          break;
        }
        else if (resp.ArgCount != 0)
          break;
        path.Add(v);
        SendThisVC("(get-value ((ControlFlow " + controlFlowConstant + " " + v + ")))");
      }
      return path.ToArray();
    }

    private ErrorModel GetErrorModel() {
      if (!options.ExpectingModel())
        return null;
      SendThisVC("(get-model)");
      Process.Ping();
      Model theModel = null;
      while (true) {
        var resp = Process.GetProverResponse();
        if (resp == null || Process.IsPong(resp))
          break;
        if (theModel != null)
          HandleProverError("Expecting only one model but got many");
        
        string modelStr = null;
        if (resp.Name == "model" && resp.ArgCount >= 1) {
          modelStr = resp[0].Name;
        }
        else if (resp.ArgCount == 0 && resp.Name.Contains("->")) {
          modelStr = resp.Name;
        }
        else {
          HandleProverError("Unexpected prover response getting model: " + resp.ToString());
        }
        List<Model> models = null;
        try {
          models = Model.ParseModels(new StringReader("Z3 error model: \n" + modelStr));
        }
        catch (ArgumentException exn) {
          HandleProverError("Model parsing error: " + exn.Message);
        }
        if (models == null)
          HandleProverError("Could not parse any models");
        else if (models.Count == 0)
          HandleProverError("Could not parse any models");
        else if (models.Count > 1)
          HandleProverError("Expecting only one model but got many");
        else
          theModel = models[0];
      }
      return new ErrorModel(theModel);
    }

    private string[] GetLabelsInfo()
    {
      SendThisVC("(labels)");
      Process.Ping();

      string[] res = null;
      while (true) {
        var resp = Process.GetProverResponse();
        if (resp == null || Process.IsPong(resp))
          break;
        if (res != null)
          HandleProverError("Expecting only one sequence of labels but got many");
        if (resp.Name == "labels" && resp.ArgCount >= 1) {
          res = resp.Arguments.Select(a => a.Name.Replace("|", "")).ToArray();
        }
        else {
          HandleProverError("Unexpected prover response getting labels: " + resp.ToString());
        }
      }
      return res;
    }

    private Outcome GetResponse()
    {
      var result = Outcome.Undetermined;
      var wasUnknown = false;

      Process.Ping();

      while (true) {
        var resp = Process.GetProverResponse();
        if (resp == null || Process.IsPong(resp))
          break;

        switch (resp.Name) {
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
          default:
            HandleProverError("Unexpected prover response: " + resp.ToString());
            break;
        }
      }

      if (wasUnknown) {
        SendThisVC("(get-info :reason-unknown)");
        Process.Ping();

        while (true) {
          var resp = Process.GetProverResponse();
          if (resp == null || Process.IsPong(resp))
            break;

          if (resp.ArgCount == 1 && resp.Name == ":reason-unknown") {
            switch (resp[0].Name) {
              case "memout":
                currentErrorHandler.OnResourceExceeded("memory");
                result = Outcome.OutOfMemory;
                Process.NeedsRestart = true;
                break;
              case "timeout":
                currentErrorHandler.OnResourceExceeded("timeout");
                result = Outcome.TimeOut;
                break;
              default:
                break;
            }
          } else {
            HandleProverError("Unexpected prover response (getting info about 'unknown' response): " + resp.ToString());
          }
        }

      }

      return result;
    }

    protected string VCExpr2String(VCExpr expr, int polarity)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<string>() != null);

      DateTime start = DateTime.UtcNow;
      //if (CommandLineOptions.Clo.Trace)
      //  Console.Write("Linearising ... ");

      // handle the types in the VCExpr
      TypeEraser eraser;
      switch (CommandLineOptions.Clo.TypeEncodingMethod) {
        case CommandLineOptions.TypeEncoding.Arguments:
          eraser = new TypeEraserArguments((TypeAxiomBuilderArguments)AxBuilder, gen);
          break;
        case CommandLineOptions.TypeEncoding.Monomorphic:
          eraser = null;
          break;
        default:
          eraser = new TypeEraserPremisses((TypeAxiomBuilderPremisses)AxBuilder, gen);
          break;
      }
      VCExpr exprWithoutTypes = eraser == null ? expr : eraser.Erase(expr, polarity);
      Contract.Assert(exprWithoutTypes != null);

      LetBindingSorter letSorter = new LetBindingSorter(gen);
      Contract.Assert(letSorter != null);
      VCExpr sortedExpr = letSorter.Mutate(exprWithoutTypes, true);
      Contract.Assert(sortedExpr != null);
      VCExpr sortedAxioms = letSorter.Mutate(AxBuilder.GetNewAxioms(), true);
      Contract.Assert(sortedAxioms != null);

      DeclCollector.Collect(sortedAxioms);
      DeclCollector.Collect(sortedExpr);
      FeedTypeDeclsToProver();

      

      AddAxiom(SMTLibExprLineariser.ToString(sortedAxioms, Namer, options));
      string res = SMTLibExprLineariser.ToString(sortedExpr, Namer, options);
      Contract.Assert(res != null);

      if (CommandLineOptions.Clo.Trace) {
        DateTime end = DateTime.UtcNow;
        TimeSpan elapsed = end - start;
        if (elapsed.TotalSeconds > 0.5)
          Console.WriteLine("Linearising   [{0} s]", elapsed.TotalSeconds);
      }
      return res;
    }

    // the list of all known axioms, where have to be included in each
    // verification condition
    private readonly List<string/*!>!*/> Axioms = new List<string/*!*/>();
    private bool AxiomsAreSetup = false;




    // similarly, a list of function/predicate declarations
    private readonly List<string/*!>!*/> TypeDecls = new List<string/*!*/>();

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

    static void InitializeGlobalInformation(string backgroundPred)
    {
      Contract.Requires(backgroundPred != null);
      Contract.Ensures(_backgroundPredicates != null);
      //throws ProverException, System.IO.FileNotFoundException;
      if (_backgroundPredicates == null) {
        string codebaseString =
          cce.NonNull(Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));

        // Initialize '_backgroundPredicates'
        string univBackPredPath = Path.Combine(codebaseString, backgroundPred);
        using (StreamReader reader = new System.IO.StreamReader(univBackPredPath)) {
          _backgroundPredicates = reader.ReadToEnd();
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

    public override void Assert(VCExpr vc, bool polarity)
    {
        string a = "";
        if (polarity)
        {
            a = "(assert " + VCExpr2String(vc, 1) + ")";
        }
        else
        {
            a = "(assert (not\n" + VCExpr2String(vc, 1) + "\n))";
        }
        AssertAxioms();
        SendThisVC(a);
    }

    public override void AssertAxioms()
    {
        FlushAxioms();
    }

    public override void Check()
    {
        PrepareCommon();
        SendThisVC("(check-sat)");
        FlushLogFile();
    }

    public override void SetTimeOut(int ms)
    {
        SendThisVC("(set-option :SOFT_TIMEOUT " + ms.ToString() + ")\n");
    }

    /// <summary>
    /// Extra state for ApiChecker (used by stratifiedInlining)
    /// </summary>
    static int nameCounter = 0;

    public override Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore, ErrorHandler handler)
    {
        unsatCore = new List<int>();

        // Name the assumptions
        var nameToAssumption = new Dictionary<string, int>();
        int i = 0;
        foreach (var vc in assumptions)
        {
            var name = "a" + nameCounter.ToString();
            nameCounter++;
            nameToAssumption.Add(name, i);

            SendThisVC(string.Format("(assert (! {0} :named {1}))", VCExpr2String(vc, 1), name));
            i++;
        }
        Check();

        var prevOutcome = CheckOutcomeCore(handler);
        
        if (prevOutcome != Outcome.Valid)
        {
            return prevOutcome;
        }

        Contract.Assert(usingUnsatCore, "SMTLib prover not setup for computing unsat cores");
        SendThisVC("(get-unsat-core)");
        var resp = Process.GetProverResponse();
        unsatCore = new List<int>();
        if(resp.Name != "") unsatCore.Add(nameToAssumption[resp.Name]);
        foreach (var s in resp.Arguments) unsatCore.Add(nameToAssumption[s.Name]);

        FlushLogFile();

        return prevOutcome;
    }

    public override void Push()
    {
        SendThisVC("(push 1)");
        DeclCollector.Push();
    }

  }

  public class SMTLibProverContext : DeclFreeProverContext
  {
    internal SMTLibProcessTheoremProver parent;

    public readonly Dictionary<CtorType, List<Function>> KnownDatatypeConstructors = new Dictionary<CtorType, List<Function>>();

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
      VCExprVar v = parent.AxBuilder.TryTyped2Untyped(var);
      if (v != null) {
        var = v;
      }
      return parent.Namer.Lookup(var);
    }

    public override void DeclareFunction(Function f, string attributes) {
      if (f is DatatypeConstructor) {
        CtorType datatype = (CtorType) f.OutParams[0].TypedIdent.Type;
        if (!KnownDatatypeConstructors.ContainsKey(datatype))
          KnownDatatypeConstructors[datatype] = new List<Function>();
        KnownDatatypeConstructors[datatype].Add(f);
      }
      base.DeclareFunction(f, attributes);
    }
  }

  public class Factory : ProverFactory
  {
    public override object SpawnProver(ProverOptions options, object ctxt)
    {
      //Contract.Requires(ctxt != null);
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      return this.SpawnProver(options,
                              cce.NonNull((SMTLibProverContext)ctxt).ExprGen,
                              cce.NonNull((SMTLibProverContext)ctxt));
    }

    public override object NewProverContext(ProverOptions options)
    {
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      VCExpressionGenerator gen = new VCExpressionGenerator();
      List<string>/*!>!*/ proverCommands = new List<string/*!*/>();
      proverCommands.Add("smtlib");
      var opts = (SMTLibProverOptions)options ;
      if (opts.UseZ3)
        proverCommands.Add("z3");
      else
        proverCommands.Add("external");
      VCGenerationOptions genOptions = new VCGenerationOptions(proverCommands);
      return new SMTLibProverContext(gen, genOptions);
    }

    public override ProverOptions BlankProverOptions()
    {
      return new SMTLibProverOptions();
    }

    protected virtual SMTLibProcessTheoremProver SpawnProver(ProverOptions options,
                                                              VCExpressionGenerator gen,
                                                              SMTLibProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      Contract.Ensures(Contract.Result<SMTLibProcessTheoremProver>() != null);

      return new SMTLibProcessTheoremProver(options, gen, ctx);
    }
  }
}
