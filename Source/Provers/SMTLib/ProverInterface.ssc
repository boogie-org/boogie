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
using ExternalProver;
using System.Diagnostics;
using Microsoft.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.Clustering;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.Simplify;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibProcessTheoremProver : LogProverInterface
  {
    private readonly DeclFreeProverContext! ctx;

    [NotDelayed]
    public SMTLibProcessTheoremProver(ProverOptions! options, VCExpressionGenerator! gen,
                                      DeclFreeProverContext! ctx)
    {
      InitializeGlobalInformation("UnivBackPred2.smt");

      this.ctx = ctx;

      TypeAxiomBuilder! axBuilder;
      switch (CommandLineOptions.Clo.TypeEncodingMethod) {
        case CommandLineOptions.TypeEncoding.Arguments:
          axBuilder = new TypeAxiomBuilderArguments (gen);
          break;
        default:
          axBuilder = new TypeAxiomBuilderPremisses (gen);
          break;
      }
      axBuilder.Setup();
      AxBuilder = axBuilder;
      UniqueNamer namer = new UniqueNamer ();
      Namer = namer;
      this.DeclCollector = new TypeDeclCollector (namer);
      base(options, "", "", "", "", gen);
    }
    
    public override ProverContext! Context { get {
      return ctx;
    } }

    private readonly TypeAxiomBuilder! AxBuilder;
    private readonly UniqueNamer! Namer;
    private readonly TypeDeclCollector! DeclCollector;

    private void FeedTypeDeclsToProver() {
      foreach (string! s in DeclCollector.GetNewDeclarations())
        AddTypeDecl(s);
    }

    public override void BeginCheck(string! descriptiveName, VCExpr! vc, ErrorHandler! handler) {
      TextWriter! output = OpenOutputFile(descriptiveName);

      string! name =
        MakeBenchmarkNameSafe(SMTLibExprLineariser.MakeIdPrintable(descriptiveName));
      WriteLineAndLog(output, "(benchmark " + name);
      WriteLineAndLog(output, _backgroundPredicates);

      if (!AxiomsAreSetup) {
        AddAxiom(VCExpr2String(ctx.Axioms, -1));
        AxiomsAreSetup = true;
      }

      string vcString = ":formula (not " + VCExpr2String(vc, 1) + ")";
      string! prelude = ctx.GetProverCommands(true);
      WriteLineAndLog(output, prelude);

      foreach (string! s in TypeDecls) {
        WriteLineAndLog(output, s);
      }
      foreach (string! s in Axioms) {
        WriteLineAndLog(output, ":assumption");
        WriteLineAndLog(output, s);
      }

      WriteLineAndLog(output, vcString);
      WriteLineAndLog(output, ")");

      output.Close();
    }

    // certain words that should not occur in the name of a benchmark
    // because some solvers don't like them
    private readonly static List<string!>! BadBenchmarkWords = new List<string!> ();
    static SMTLibProcessTheoremProver() {
      BadBenchmarkWords.Add("Array"); BadBenchmarkWords.Add("Arrray");
    }

    private string! MakeBenchmarkNameSafe(string! name) {
      for (int i = 0; i < BadBenchmarkWords.Count; i = i + 2)
        name = name.Replace(BadBenchmarkWords[i], BadBenchmarkWords[i+1]);
      return name;
    }

    private TextWriter! OpenOutputFile(string! descriptiveName) {
        string filename = CommandLineOptions.Clo.SMTLibOutputPath;
        filename = Helpers.SubstituteAtPROC(descriptiveName, (!)filename);
        return new StreamWriter(filename, false);
    }

    private void WriteLineAndLog(TextWriter! output, string! msg) {
      LogActivity(msg);
      output.WriteLine(msg);
    }

    [NoDefaultContract]
    public override Outcome CheckOutcome(ErrorHandler! handler)
      throws UnexpectedProverOutputException; {
      return Outcome.Undetermined;
    }

    protected string! VCExpr2String(VCExpr! expr, int polarity) {
      DateTime start = DateTime.Now;
      if (CommandLineOptions.Clo.Trace)
        Console.Write("Linearising ... ");

      // handle the types in the VCExpr
      TypeEraser! eraser;
      switch (CommandLineOptions.Clo.TypeEncodingMethod) {
        case CommandLineOptions.TypeEncoding.Arguments:
          eraser = new TypeEraserArguments((TypeAxiomBuilderArguments)AxBuilder, gen);
          break;
        default:
          eraser = new TypeEraserPremisses((TypeAxiomBuilderPremisses)AxBuilder, gen);
          break;
      }
      VCExpr! exprWithoutTypes = eraser.Erase(expr, polarity);

      LetBindingSorter! letSorter = new LetBindingSorter(gen);
      VCExpr! sortedExpr = letSorter.Mutate(exprWithoutTypes, true);
      VCExpr! sortedAxioms = letSorter.Mutate(AxBuilder.GetNewAxioms(), true);

      DeclCollector.Collect(sortedAxioms);
      DeclCollector.Collect(sortedExpr);
      FeedTypeDeclsToProver();

      AddAxiom(SMTLibExprLineariser.ToString(sortedAxioms, Namer));
      string! res = SMTLibExprLineariser.ToString(sortedExpr, Namer);

      if (CommandLineOptions.Clo.Trace) {
        DateTime end = DateTime.Now;
        TimeSpan elapsed = end - start;
        Console.WriteLine("finished   [{0} s]  ", elapsed.TotalSeconds);
      }
      return res;
    }

    // the list of all known axioms, where have to be included in each
    // verification condition
    private readonly List<string!>! Axioms = new List<string!> ();
    private bool AxiomsAreSetup = false;

    // similarly, a list of function/predicate declarations
    private readonly List<string!>! TypeDecls = new List<string!> ();

    protected void AddAxiom(string! axiom) {
      Axioms.Add(axiom);
//      if (thmProver != null) {
//        LogActivity(":assume " + axiom);
//        thmProver.AddAxioms(axiom);
//      }
    }

    protected void AddTypeDecl(string! decl) {
      TypeDecls.Add(decl);
 //     if (thmProver != null) {
 //       LogActivity(decl);
 //       thmProver.Feed(decl, 0);
 //     }
    }

    ////////////////////////////////////////////////////////////////////////////

    private static string! _backgroundPredicates;

    static void InitializeGlobalInformation(string! backgroundPred)
      ensures _backgroundPredicates != null;
      //throws ProverException, System.IO.FileNotFoundException;
    {
      if (_backgroundPredicates == null) {
        string! codebaseString =
          (!) Path.GetDirectoryName((!)System.Reflection.Assembly.GetExecutingAssembly().Location);

        // Initialize '_backgroundPredicates'
        string univBackPredPath = Path.Combine(codebaseString, backgroundPred);
        using (StreamReader reader = new System.IO.StreamReader(univBackPredPath))
        {
          _backgroundPredicates = reader.ReadToEnd();
        }
      }
    }
  }

  public class Factory : ProverFactory
  {

    public override object! SpawnProver(ProverOptions! options, object! ctxt)
    {
      return this.SpawnProver(options,
                              ((DeclFreeProverContext!)ctxt).ExprGen,
                              (DeclFreeProverContext!)ctxt);
    }

    public override object! NewProverContext(ProverOptions! options) {
      if (CommandLineOptions.Clo.BracketIdsInVC < 0) {
        CommandLineOptions.Clo.BracketIdsInVC = 0;
      }

      VCExpressionGenerator! gen = new VCExpressionGenerator ();
      List<string!>! proverCommands = new List<string!> ();
// TODO: what is supported?
//      proverCommands.Add("all");
//      proverCommands.Add("simplify");
//      proverCommands.Add("simplifyLike");
      VCGenerationOptions! genOptions = new VCGenerationOptions(proverCommands);

      return new DeclFreeProverContext(gen, genOptions);
    }

    protected virtual SMTLibProcessTheoremProver! SpawnProver(ProverOptions! options,
                                                              VCExpressionGenerator! gen,
                                                              DeclFreeProverContext! ctx) {
      return new SMTLibProcessTheoremProver(options, gen, ctx);
    }
  }
}
