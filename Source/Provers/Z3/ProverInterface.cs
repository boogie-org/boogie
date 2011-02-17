//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
//using System.Collections;
using System.Collections.Generic;
using System.Threading;
//using System.IO;
using System.Text;
//using ExternalProver;
using System.Diagnostics;
using System.Diagnostics.Contracts;
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
    private Z3InstanceOptions opts;
    private Inspector inspector;
    [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(opts!=null);
}


    [NotDelayed]
    public Z3ProcessTheoremProver(VCExpressionGenerator gen,
                                  DeclFreeProverContext ctx, Z3InstanceOptions opts):base(opts, gen, ctx, opts.ExeName,opts.Typed ? "TypedUnivBackPred2.sx" : "UnivBackPred2.sx")
    {
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      Contract.Requires(opts != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      this.opts = opts;
      
    }

    private void FireUpInspector()
    {
      if (inspector == null && opts.Inspector != null) {
        inspector = new Inspector(opts);
      }
    }
    
    protected override Microsoft.Boogie.Simplify.ProverProcess CreateProverProcess(string proverPath) {
    //Contract.Requires(proverPath!= null);
    Contract.Ensures(Contract.Result<Microsoft.Boogie.Simplify.ProverProcess>() != null);


      opts.ExeName = proverPath;
      FireUpInspector();
      if (inspector != null) {
        inspector.NewProver();
      }
      return new Z3ProverProcess(opts, inspector);
    }

    protected override AxiomVCExprTranslator SpawnVCExprTranslator(ProverOptions opts) {
      //Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<AxiomVCExprTranslator>() != null);

      return new Z3VCExprTranslator(gen, (Z3InstanceOptions) opts);
    }

    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
    {
      //Contract.Requires(descriptiveName != null);
      //Contract.Requires(vc != null);
      //Contract.Requires(handler != null);
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
        {
        Contract.Ensures(0 <= Contract.Result<int>() && Contract.Result<int>() < 4);
        return CommandLineOptions.Clo.Z3lets;
      }
    }
    public bool DistZ3 = false;
    public string ExeName = "z3.exe";
    public bool InverseImplies = false;
    public string Inspector = null;
    public bool OptimizeForBv = false;

    [ContractInvariantMethod]
    void ObjectInvariant() 
    {
      Contract.Invariant(ExeName!=null);
    }

    protected override bool Parse(string opt)
    {
      //Contract.Requires(opt!=null);
      return ParseBool(opt, "REVERSE_IMPLIES", ref InverseImplies) ||
             ParseString(opt, "INSPECTOR", ref Inspector) ||
             ParseBool(opt, "DIST", ref DistZ3) ||
             ParseBool(opt, "OPTIMIZE_FOR_BV", ref OptimizeForBv) ||
             base.Parse(opt);
    }

    public override void PostParse()
    {
      base.PostParse();

      if (DistZ3) {
        ExeName = "z3-dist.exe";
        CommandLineOptions.Clo.RestartProverPerVC = true;
      }     
    }

    public override string Help
    {
      get
      {
        return
@"
Z3-specific options:
~~~~~~~~~~~~~~~~~~~~
INSPECTOR=<string>        Use the specified Z3Inspector binary.
OPTIMIZE_FOR_BV=<bool>    Optimize Z3 options for bitvector reasoning, and not quantifier instantiation. Defaults to false.

Obscure options:
~~~~~~~~~~~~~~~~
DIST=<bool>               Use z3-dist.exe binary.
REVERSE_IMPLIES=<bool>    Encode P==>Q as Q||!P.

" + base.Help;
          // DIST requires non-public binaries
      }
    }
  }

  public class Z3LineariserOptions : LineariserOptions {
    private readonly Z3InstanceOptions opts;

    [ContractInvariantMethod]
    void ObjectInvariant() 
    {
        Contract.Invariant(opts!=null);
    }


    public override CommandLineOptions.BvHandling Bitvectors { get {
      return opts.BitVectors;
    } }
 
    public Z3LineariserOptions(bool asTerm, Z3InstanceOptions opts, List<VCExprVar/*!>!*/> letVariables):base(asTerm) {
    Contract.Requires(opts != null);
      Contract.Requires(cce.NonNullElements(letVariables));
    
      this.opts = opts;
      this.LetVariablesAttr = letVariables;
    }

    public override bool UseWeights { get {
      return true;
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

    public override LineariserOptions SetAsTerm(bool newVal) {
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);

      if (newVal == AsTerm)
        return this;
      return new Z3LineariserOptions(newVal, opts, LetVariables);
    }

    // variables representing formulas in let-bindings have to be
    // printed in a different way than other variables
    private readonly List<VCExprVar/*!>!*/> LetVariablesAttr;
    public override List<VCExprVar/*!>!*/> LetVariables { get {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<VCExprVar>>()));

      return LetVariablesAttr;
    } }

    public override LineariserOptions AddLetVariable(VCExprVar furtherVar) {
      //Contract.Requires(furtherVar != null);
      Contract.Ensures(Contract.Result<LineariserOptions>() != null);

      List<VCExprVar/*!>!*/> allVars = new List<VCExprVar/*!*/>();
      allVars.AddRange(LetVariables);
      allVars.Add(furtherVar);
      return new Z3LineariserOptions(AsTerm, opts, allVars);
    }
    
    public override LineariserOptions AddLetVariables(List<VCExprVar/*!>!*/> furtherVars) {
      //Contract.Requires(furtherVars != null);
    Contract.Ensures(Contract.Result<LineariserOptions>() != null);

      List<VCExprVar/*!>!*/> allVars = new List<VCExprVar/*!*/> ();
      allVars.AddRange(LetVariables);
      allVars.AddRange(furtherVars);
      return new Z3LineariserOptions(AsTerm, opts, allVars);
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public class Z3VCExprTranslator : AxiomVCExprTranslator {
    public Z3VCExprTranslator(VCExpressionGenerator gen, Z3InstanceOptions opts) {
      Contract.Requires(gen != null);
      Contract.Requires(opts != null);
      Gen = gen;
      Opts = opts;
      TypeAxiomBuilder axBuilder;
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

    private Z3VCExprTranslator(Z3VCExprTranslator tl) :base(tl){
      Contract.Requires(tl!=null);
      Gen = tl.Gen;
      Opts = tl.Opts; // we assume that the options have not changed
      AxBuilder = (TypeAxiomBuilder)tl.AxBuilder.Clone();
      UniqueNamer namer = (UniqueNamer)tl.Namer.Clone();
      Namer = namer;
      DeclCollector = new TypeDeclCollector (namer, tl.DeclCollector);
    }

    public override Object Clone() {
      Contract.Ensures(Contract.Result<Object>() != null);

      return new Z3VCExprTranslator(this);
    }

    [ContractInvariantMethod]
    void ObjectInvariant() 
    {
      Contract.Invariant(Opts!=null);
      Contract.Invariant(Gen != null);
      Contract.Invariant(AxBuilder != null);
      Contract.Invariant(Namer != null);
      Contract.Invariant(DeclCollector != null);
    }

    private readonly Z3InstanceOptions Opts;
    private readonly VCExpressionGenerator Gen;
    private readonly TypeAxiomBuilder AxBuilder;
    private readonly UniqueNamer Namer;
    private readonly TypeDeclCollector DeclCollector;

    public override string Lookup(VCExprVar var)
    {
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
      VCExpr exprWithoutTypes = eraser != null ? eraser.Erase(expr, polarity) : expr;
      Contract.Assert(exprWithoutTypes!=null);
      
      LetBindingSorter letSorter = new LetBindingSorter(Gen);
      Contract.Assert(letSorter!=null);
      VCExpr sortedExpr = letSorter.Mutate(exprWithoutTypes, true);
      Contract.Assert(sortedExpr!=null);
      VCExpr sortedAxioms = letSorter.Mutate(AxBuilder.GetNewAxioms(), true);
      Contract.Assert(sortedAxioms!=null);

      if (Opts.Typed) {
        DeclCollector.Collect(sortedAxioms);
        DeclCollector.Collect(sortedExpr);
        FeedTypeDeclsToProver();
      } else {
        TermFormulaFlattener flattener = new TermFormulaFlattener (Gen);
        Contract.Assert(flattener!=null);
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

      LineariserOptions linOptions = new Z3LineariserOptions(false, Opts, new List<VCExprVar/*!*/>());

      AddAxiom(SimplifyLikeExprLineariser.ToString(sortedAxioms, linOptions, Namer));

      string res = SimplifyLikeExprLineariser.ToString(sortedExpr, linOptions, Namer);
      Contract.Assert(res!=null);

      if (CommandLineOptions.Clo.Trace) {
        TimeSpan elapsed = DateTime.Now - start;
        Console.WriteLine("finished   [{0} s]  ", elapsed.TotalSeconds);
      }
      return res;
    }

    private void FeedTypeDeclsToProver() {
      foreach (string s in DeclCollector.GetNewDeclarations()) {
        Contract.Assert(s != null);
        AddTypeDecl(s);
      }
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  public class Factory : ProverFactory
  {

    public override object SpawnProver(ProverOptions popts, object ctxt)
    {
      //Contract.Requires(popts != null);
      //Contract.Requires(ctxt != null);
      Contract.Ensures(Contract.Result<object>() != null);

      Z3InstanceOptions opts = cce.NonNull((Z3InstanceOptions)popts);
      return this.SpawnProver(cce.NonNull((DeclFreeProverContext)ctxt).ExprGen,
                              cce.NonNull((DeclFreeProverContext)ctxt),
                              opts);
    }

    public override object NewProverContext(ProverOptions options) {
      //Contract.Requires(options != null);
      //Contract.Ensures(Contract.Result<object>() != null);

      if (CommandLineOptions.Clo.BracketIdsInVC < 0) {
        CommandLineOptions.Clo.BracketIdsInVC = 0;
      }

      Z3InstanceOptions opts = cce.NonNull((Z3InstanceOptions)options);
      VCExpressionGenerator gen = new VCExpressionGenerator ();
      List<string/*!>!*/> proverCommands = new List<string/*!*/> ();
      proverCommands.Add("all");
      proverCommands.Add("z3");
      proverCommands.Add("simplifyLike");
      if (opts.BitVectors == CommandLineOptions.BvHandling.Z3Native)
        proverCommands.Add("bvDefSem");
      if (opts.BitVectors == CommandLineOptions.BvHandling.ToInt)
        proverCommands.Add("bvInt");
      VCGenerationOptions genOptions = new VCGenerationOptions(proverCommands);
      
      return NewProverContext(gen, genOptions, opts);
    }

    public override ProverOptions BlankProverOptions()
    {
      Contract.Ensures(Contract.Result<ProverOptions>() != null);
      return new Z3InstanceOptions();
    }

    protected virtual Z3ProcessTheoremProver SpawnProver(VCExpressionGenerator gen,
                                                         DeclFreeProverContext ctx,
                                                         Z3InstanceOptions opts) {
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<Z3ProcessTheoremProver>() != null);

      return new Z3ProcessTheoremProver(gen, ctx, opts);
    }

      protected virtual DeclFreeProverContext NewProverContext(VCExpressionGenerator gen, 
                                                               VCGenerationOptions genOptions,
                                                               Z3InstanceOptions opts)
      {
          return new DeclFreeProverContext(gen, genOptions);
      }
  }
}
