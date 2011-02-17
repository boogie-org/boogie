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
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.Clustering;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.Simplify;
using System.Text;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibProverOptions : ProverOptions
  {
    public bool UseWeights = true;
    public bool UseLabels { get { return UseZ3; } }
    public bool UseZ3 = true;

    protected override bool Parse(string opt)
    {
      return
        ParseBool(opt, "USE_WEIGHTS", ref UseWeights) ||
        ParseBool(opt, "USE_Z3", ref UseZ3) ||
        base.Parse(opt);
    }

    public override string Help
    {
      get
      {
        return
@"
SMT-specific options:
~~~~~~~~~~~~~~~~~~~~~
USE_Z3=<bool>             Use z3.exe as the prover, and use Z3 extensions (default: true)
USE_WEIGHTS=<bool>        Pass :weight annotations on quantified formulas (default: true)
VERBOSITY=<int>           1 - print prover output (default: 0)
" + base.Help;
      }
    }
  }

  public class SMTLibProcessTheoremProver : ProverInterface
  {
    private readonly DeclFreeProverContext ctx;
    private readonly VCExpressionGenerator gen;
    private readonly SMTLibProverOptions options;

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
                                      DeclFreeProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      InitializeGlobalInformation("UnivBackPred2.smt2");

      this.options = (SMTLibProverOptions)options;
      this.ctx = ctx;
      this.gen = gen;

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
      this.DeclCollector = new TypeDeclCollector((SMTLibProverOptions)options, Namer);

      if (this.options.UseZ3) {
        var psi = SMTLibProcess.ComputerProcessStartInfo(Z3.Z3ExecutablePath(), "AUTO_CONFIG=false -smt2 -in");
        Process = new SMTLibProcess(psi, this.options);
        Process.ErrorHandler += this.HandleProverError;
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

    readonly TypeAxiomBuilder AxBuilder;
    readonly UniqueNamer Namer;
    readonly TypeDeclCollector DeclCollector;
    readonly SMTLibProcess Process;
    readonly List<string> proverErrors = new List<string>();
    readonly StringBuilder common = new StringBuilder();
    TextWriter currentLogFile;
    ErrorHandler currentErrorHandler;

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
      if (common.Length == 0)
        SendCommon(_backgroundPredicates);

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
    }

    private void CloseLogFile()
    {
      if (currentLogFile != null) {
        currentLogFile.Close();
        currentLogFile = null;
      }
    }

    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
    {
      //Contract.Requires(descriptiveName != null);
      //Contract.Requires(vc != null);
      //Contract.Requires(handler != null);

      currentErrorHandler = handler;

      if (options.SeparateLogFiles) CloseLogFile(); // shouldn't really happen

      if (options.LogFilename != null && currentLogFile == null) {
        currentLogFile = OpenOutputFile(descriptiveName);
        currentLogFile.Write(common.ToString());
      }

      PrepareCommon();
      string vcString = "(assert (not\n" + VCExpr2String(vc, 1) + "\n))";
      FlushAxioms();

      SendThisVC("(push)");
      SendThisVC("(set-info :boogie-vc-id " + SMTLibNamer.QuoteId(descriptiveName) + ")");
      SendThisVC(vcString);

      if (Process != null)
        Process.PingPong(); // flush any errors

      SendThisVC("(check-sat)");
      SendThisVC("(pop 1)");
    }

    private TextWriter OpenOutputFile(string descriptiveName)
    {
      Contract.Requires(descriptiveName != null);
      Contract.Ensures(Contract.Result<TextWriter>() != null);

      string filename = options.LogFilename;
      filename = Helpers.SubstituteAtPROC(descriptiveName, cce.NonNull(filename));
      return new StreamWriter(filename, false);
    }

    private void HandleProverError(string s)
    {
      lock (proverErrors) {
        proverErrors.Add(s);
        Console.Error.WriteLine("Prover error: " + s);
      }
    }

    [NoDefaultContract]
    public override Outcome CheckOutcome(ErrorHandler handler)
    {  //Contract.Requires(handler != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var result = Outcome.Undetermined;

      if (Process == null)
        return result;

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
          case "unknown":
            result = Outcome.Invalid;
            break;
          default:
            HandleProverError("Unexpected prover response: " + resp.ToString());
            break;
        }
      }

      return result;
    }

    protected string VCExpr2String(VCExpr expr, int polarity)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<string>() != null);

      DateTime start = DateTime.Now;
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
        DateTime end = DateTime.Now;
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
  }

  public class Factory : ProverFactory
  {

    public override object SpawnProver(ProverOptions options, object ctxt)
    {
      //Contract.Requires(ctxt != null);
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      return this.SpawnProver(options,
                              cce.NonNull((DeclFreeProverContext)ctxt).ExprGen,
                              cce.NonNull((DeclFreeProverContext)ctxt));
    }

    public override object NewProverContext(ProverOptions options)
    {
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      VCExpressionGenerator gen = new VCExpressionGenerator();
      List<string>/*!>!*/ proverCommands = new List<string/*!*/>();
      // TODO: what is supported?
      //      proverCommands.Add("all");
      //      proverCommands.Add("simplify");
      //      proverCommands.Add("simplifyLike");
      VCGenerationOptions genOptions = new VCGenerationOptions(proverCommands);
      Contract.Assert(genOptions != null);

      return new DeclFreeProverContext(gen, genOptions);
    }

    public override ProverOptions BlankProverOptions()
    {
      return new SMTLibProverOptions();
    }

    protected virtual SMTLibProcessTheoremProver SpawnProver(ProverOptions options,
                                                              VCExpressionGenerator gen,
                                                              DeclFreeProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      Contract.Ensures(Contract.Result<SMTLibProcessTheoremProver>() != null);

      return new SMTLibProcessTheoremProver(options, gen, ctx);
    }
  }
}
