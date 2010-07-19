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
using ExternalProver;
using System.Diagnostics;
using Microsoft.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.Clustering;
using Microsoft.Boogie.TypeErasure;
using Microsoft.Boogie.Z3;
using Microsoft.Boogie.Simplify;

namespace Microsoft.Boogie.Z3
{
  public class Z3ProcessTheoremProver : ProcessTheoremProver
  {
    private Z3InstanceOptions! opts;
    private Inspector inspector;

    [NotDelayed]
    public Z3ProcessTheoremProver(VCExpressionGenerator! gen,
                                  DeclFreeProverContext! ctx, Z3InstanceOptions! opts)
      throws UnexpectedProverOutputException;
    {
      this.opts = opts;
      string! backPred = opts.Typed ? "TypedUnivBackPred2.sx" : "UnivBackPred2.sx";
      base(opts, gen, ctx, opts.ExeName, backPred);
    }

    private void FireUpInspector()
    {
      if (inspector == null && opts.Inspector != null) {
        inspector = new Inspector(opts);
      }
    }
    
    protected override Microsoft.Boogie.Simplify.ProverProcess! CreateProverProcess(string! proverPath) {
      opts.ExeName = proverPath;
      FireUpInspector();
      if (inspector != null) {
        inspector.NewProver();
      }
      return new Z3ProverProcess(opts, inspector);
    }

    protected override AxiomVCExprTranslator! SpawnVCExprTranslator() {
      return new Z3VCExprTranslator(gen, opts);
    }

    public override void BeginCheck(string! descriptiveName, VCExpr! vc, ErrorHandler! handler)
    {
      FireUpInspector();
      if (inspector != null) {
        inspector.NewProblem(descriptiveName, vc, handler);
      }
      base.BeginCheck(descriptiveName, vc, handler);
    }
  }

  public class Z3InstanceOptions : ProverOptions
  {
    public int Timeout { get { return TimeLimit / 1000; } }
    public bool Typed {
      get { 
        return CommandLineOptions.Clo.Z3types || BitVectors == CommandLineOptions.BvHandling.Z3Native; 
      } 
    }
    public int Lets {
      get
        ensures 0 <= result && result < 4;
      {
        return CommandLineOptions.Clo.Z3lets;
      }
    }
    public bool V1 = false;
    public bool V2 = false; // default set in PostParse
    public bool DistZ3 = false;
    public string! ExeName = "z3.exe";
    public bool InverseImplies = false;
    public string? Inspector = null;

    protected override bool Parse(string! opt)
    {
      return ParseBool(opt, "V1", ref V1) ||
             ParseBool(opt, "V2", ref V2) ||
             ParseBool(opt, "REVERSE_IMPLIES", ref InverseImplies) ||
             ParseString(opt, "INSPECTOR", ref Inspector) ||
             ParseBool(opt, "DIST", ref DistZ3) ||
             base.Parse(opt);
    }

    protected override void PostParse()
    {
      base.PostParse();

      if (!V1 && !V2) {
        V2 = true; // default
      } else if (V1 && V2) {
        ReportError("V1 and V2 requested at the same time");
      } else if (V1 && DistZ3) {
        ReportError("V1 and DistZ3 requested at the same time");
      }
      if (V1) {
        ExeName = "z3-v1.3.exe";
      }
      if (DistZ3) {
        ExeName = "z3-dist.exe";
        CommandLineOptions.Clo.RestartProverPerVC = true;
      }
      
    }
  }

  internal class Z3LineariserOptions : LineariserOptions {
    private readonly Z3InstanceOptions! opts;

    public override CommandLineOptions.BvHandling Bitvectors { get {
      return opts.BitVectors;
    } }
 
    internal Z3LineariserOptions(bool asTerm, Z3InstanceOptions! opts, List<VCExprVar!>! letVariables) {
      base(asTerm);
      this.opts = opts;
      this.LetVariablesAttr = letVariables;
    }

    public override bool UseWeights { get {
      return opts.V2;
    } }

    public override bool UseTypes { get {
      return opts.Typed;
    } }

    public override bool QuantifierIds { get {
      return true;
    } }

    public override bool InverseImplies { get { 
      return opts.InverseImplies;
    } }

    public override LineariserOptions! SetAsTerm(bool newVal) {
      if (newVal == AsTerm)
        return this;
      return new Z3LineariserOptions(newVal, opts, LetVariables);
    }

    // variables representing formulas in let-bindings have to be
    // printed in a different way than other variables
    private readonly List<VCExprVar!>! LetVariablesAttr;
    public override List<VCExprVar!>! LetVariables { get {
      return LetVariablesAttr;
    } }

    public override LineariserOptions! AddLetVariable(VCExprVar! furtherVar) {
      List<VCExprVar!>! allVars = new List<VCExprVar!> ();
      allVars.AddRange(LetVariables);
      allVars.Add(furtherVar);
      return new Z3LineariserOptions(AsTerm, opts, allVars);
    }
    
    public override LineariserOptions! AddLetVariables(List<VCExprVar!>! furtherVars) {
      List<VCExprVar!>! allVars = new List<VCExprVar!> ();
      allVars.AddRange(LetVariables);
      allVars.AddRange(furtherVars);
      return new Z3LineariserOptions(AsTerm, opts, allVars);
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public class Z3VCExprTranslator : AxiomVCExprTranslator {
    public Z3VCExprTranslator(VCExpressionGenerator! gen, Z3InstanceOptions! opts) {
      Gen = gen;
      Opts = opts;
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
      this.DeclCollector =
        new TypeDeclCollector (namer, opts.BitVectors == CommandLineOptions.BvHandling.Z3Native);
    }

    private Z3VCExprTranslator(Z3VCExprTranslator! tl) {
      base(tl);
      Gen = tl.Gen;
      Opts = tl.Opts; // we assume that the options have not changed
      AxBuilder = (TypeAxiomBuilder)tl.AxBuilder.Clone();
      UniqueNamer namer = (UniqueNamer)tl.Namer.Clone();
      Namer = namer;
      DeclCollector = new TypeDeclCollector (namer, tl.DeclCollector);
    }

    public override Object! Clone() {
      return new Z3VCExprTranslator(this);
    }

    private readonly Z3InstanceOptions! Opts;
    private readonly VCExpressionGenerator! Gen;
    private readonly TypeAxiomBuilder! AxBuilder;
    private readonly UniqueNamer! Namer;
    private readonly TypeDeclCollector! DeclCollector;

    public override string! Lookup(VCExprVar! var)
    {
      return Namer.Lookup(var);
    }
    
    public override string! translate(VCExpr! expr, int polarity) {
      DateTime start = DateTime.Now;
      if (CommandLineOptions.Clo.Trace)
        Console.Write("Linearising ... ");

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
      VCExpr! exprWithoutTypes = eraser != null ? eraser.Erase(expr, polarity) : expr;
      
      LetBindingSorter! letSorter = new LetBindingSorter(Gen);
      VCExpr! sortedExpr = letSorter.Mutate(exprWithoutTypes, true);
      VCExpr! sortedAxioms = letSorter.Mutate(AxBuilder.GetNewAxioms(), true);

      if (Opts.Typed) {
        DeclCollector.Collect(sortedAxioms);
        DeclCollector.Collect(sortedExpr);
        FeedTypeDeclsToProver();
      } else {
        TermFormulaFlattener! flattener = new TermFormulaFlattener (Gen);
        sortedExpr = flattener.Flatten(sortedExpr);
        sortedAxioms = flattener.Flatten(sortedAxioms);
      }
      if (Opts.Lets != 3) {
        // replace let expressions with implies
        Let2ImpliesMutator letImplier = new Let2ImpliesMutator(Gen, Opts.Lets == 1, Opts.Lets == 2);
        sortedExpr = letImplier.Mutate(sortedExpr);
        sortedAxioms = letImplier.Mutate(sortedAxioms);
      }

      //////////////////////////////////////////////////////////////////////////
      //SubtermCollector! coll = new SubtermCollector (gen);
      //coll.Traverse(sortedExpr, true);
      //coll.Traverse(sortedAxioms, true);
      //coll.UnifyClusters();
      //Console.WriteLine(coll);
      //////////////////////////////////////////////////////////////////////////

      LineariserOptions linOptions = new Z3LineariserOptions(false, Opts, new List<VCExprVar!>());

      AddAxiom(SimplifyLikeExprLineariser.ToString(sortedAxioms, linOptions, Namer));

      string! res = SimplifyLikeExprLineariser.ToString(sortedExpr, linOptions, Namer);

      if (CommandLineOptions.Clo.Trace) {
        TimeSpan elapsed = DateTime.Now - start;
        Console.WriteLine("finished   [{0} s]  ", elapsed.TotalSeconds);
      }
      return res;
    }

    private void FeedTypeDeclsToProver() {
      foreach (string! s in DeclCollector.GetNewDeclarations())
        AddTypeDecl(s);
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public class Factory : ProverFactory
  {

    public override object! SpawnProver(ProverOptions! popts, object! ctxt)
    {
      Z3InstanceOptions opts = (Z3InstanceOptions!)popts;
      return this.SpawnProver(((DeclFreeProverContext!)ctxt).ExprGen,
                              (DeclFreeProverContext!)ctxt,
                              opts);
    }

    public override object! NewProverContext(ProverOptions! options) {
      if (CommandLineOptions.Clo.BracketIdsInVC < 0) {
        CommandLineOptions.Clo.BracketIdsInVC = 0;
      }

      Z3InstanceOptions opts = (Z3InstanceOptions!)options;
      VCExpressionGenerator! gen = new VCExpressionGenerator ();
      List<string!>! proverCommands = new List<string!> ();
      proverCommands.Add("all");
      proverCommands.Add("z3");
      proverCommands.Add("simplifyLike");
      if (opts.BitVectors == CommandLineOptions.BvHandling.Z3Native)
        proverCommands.Add("bvDefSem");
      if (opts.BitVectors == CommandLineOptions.BvHandling.ToInt)
        proverCommands.Add("bvInt");
      VCGenerationOptions! genOptions = new VCGenerationOptions(proverCommands);

      return new DeclFreeProverContext(gen, genOptions);
    }

    public override ProverOptions! BlankProverOptions()
    {
      return new Z3InstanceOptions();
    }

    protected virtual Z3ProcessTheoremProver! SpawnProver(VCExpressionGenerator! gen,
                                                          DeclFreeProverContext! ctx,
                                                          Z3InstanceOptions! opts) {
      return new Z3ProcessTheoremProver(gen, ctx, opts);
    }
  }
}
