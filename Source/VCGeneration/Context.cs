//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie
{
  /// <summary>
  /// The methods of this class are called in the following order:
  ///   DeclareType*
  ///   (DeclareConstant DeclareFunction)*
  ///   AddAxiom*
  ///   DeclareGlobalVariable*
  /// At this time, all "attributes" are passed in as null.
  /// </summary>
  [ContractClass(typeof(ProverContextContracts))]
  public abstract class ProverContext : ICloneable {
    protected virtual void ProcessDeclaration(Declaration decl) {Contract.Requires(decl != null);}
    public virtual void DeclareType(TypeCtorDecl t, string attributes) {Contract.Requires(t != null); ProcessDeclaration(t); }
    public virtual void DeclareConstant(Constant c, bool uniq, string attributes) {Contract.Requires(c != null); ProcessDeclaration(c); }
    public virtual void DeclareFunction(Function f, string attributes) {Contract.Requires(f != null); ProcessDeclaration(f); }
    public virtual void AddAxiom(Axiom a, string attributes) {Contract.Requires(a != null); ProcessDeclaration(a); }
    public virtual void DeclareGlobalVariable(GlobalVariable v, string attributes) {Contract.Requires(v != null); ProcessDeclaration(v); }
    public abstract void AddAxiom(VCExpr vc);
    public abstract string Lookup(VCExprVar var);
    public abstract VCExpressionGenerator ExprGen { get; }
    public abstract Boogie2VCExprTranslator BoogieExprTranslator { get; }
    public abstract VCGenerationOptions VCGenOptions { get; }
    public abstract object Clone();
  }
  
[ContractClassFor(typeof(ProverContext))]
public abstract class ProverContextContracts:ProverContext{
  public override void AddAxiom(VCExpr vc) {
  }
  public override void  AddAxiom(Axiom a, string attributes)
{
}
  public override VCExpressionGenerator  ExprGen
{
	get { Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);
 throw new NotImplementedException(); }
}
  public override Boogie2VCExprTranslator  BoogieExprTranslator
{
	get { Contract.Ensures(Contract.Result<Boogie2VCExprTranslator>() != null);
 throw new NotImplementedException(); }
}
  public override VCGenerationOptions  VCGenOptions
{
	get {Contract.Ensures(Contract.Result<VCGenerationOptions>() != null);
 throw new NotImplementedException(); }
}
  public override object  Clone()
{
 Contract.Ensures(Contract.Result<object>() != null);
	throw new NotImplementedException();
}
}

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  
  /// <summary>
  /// This ProverContext subclass is intended for use with untyped provers that do not require names
  /// to be declared before use.  It constructs its context from unique constants and given axioms.
  /// </summary>
  public class DeclFreeProverContext : ProverContext {
    protected VCExpressionGenerator gen;
    protected VCGenerationOptions genOptions;
    protected Boogie2VCExprTranslator translator;
    
    protected OrderingAxiomBuilder orderingAxiomBuilder;

    StringBuilder proverCommands;
    StringBuilder incrementalProverCommands;
    
    protected List<Variable> distincts;
    protected List<VCExpr> axiomConjuncts;

    [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(gen!=null);
      Contract.Invariant(genOptions != null);
      Contract.Invariant(translator != null);
      Contract.Invariant(orderingAxiomBuilder != null);
      Contract.Invariant(proverCommands != null);
      Contract.Invariant(incrementalProverCommands != null);
      Contract.Invariant(cce.NonNullElements(distincts));
      Contract.Invariant(cce.NonNullElements(axiomConjuncts));
}

    public VCExprTranslator/*?*/ exprTranslator;

    public DeclFreeProverContext(VCExpressionGenerator gen,
                                 VCGenerationOptions genOptions) {
      Contract.Requires(gen != null);
      Contract.Requires(genOptions != null);
      this.gen = gen;
      this.genOptions = genOptions;
      Boogie2VCExprTranslator t = new Boogie2VCExprTranslator (gen, genOptions);
      this.translator = t;
      OrderingAxiomBuilder oab = new OrderingAxiomBuilder(gen, t);
      Contract.Assert(oab != null);
      oab.Setup();
      this.orderingAxiomBuilder = oab;

      proverCommands = new StringBuilder();
      incrementalProverCommands = new StringBuilder();
    
      distincts = new List<Variable>();
      axiomConjuncts = new List<VCExpr>();

      exprTranslator = null;
    }

    private DeclFreeProverContext(DeclFreeProverContext ctxt) {
      Contract.Requires(ctxt != null);
      this.gen = ctxt.gen;
      this.genOptions = ctxt.genOptions;
      Boogie2VCExprTranslator t = (Boogie2VCExprTranslator)ctxt.translator.Clone();
      Contract.Assert(t != null);
      this.translator = t;
      this.orderingAxiomBuilder = new OrderingAxiomBuilder(ctxt.gen, t, ctxt.orderingAxiomBuilder);

      StringBuilder cmds = new StringBuilder ();
      
      cmds.Append(ctxt.proverCommands);
      proverCommands = cmds;
      StringBuilder incCmds = new StringBuilder ();
      incCmds.Append(ctxt.incrementalProverCommands);
      incrementalProverCommands = incCmds;
    
      distincts = new List<Variable>(ctxt.distincts);
      axiomConjuncts = new List<VCExpr>(ctxt.axiomConjuncts);

      if (ctxt.exprTranslator == null)
        exprTranslator = null;
      else
        exprTranslator = (VCExprTranslator)cce.NonNull(ctxt.exprTranslator.Clone());
    }

    public override object Clone() {
      Contract.Ensures(Contract.Result<object>() != null);

      return new DeclFreeProverContext(this);
    }

    internal protected void SayToProver(string msg)
    {
      Contract.Requires(msg != null);
      msg = msg + "\r\n";
      proverCommands.Append(msg);
      incrementalProverCommands.Append(msg);
    }

    protected override void ProcessDeclaration(Declaration decl)
    {
      //Contract.Requires(decl != null);
      for (QKeyValue a = decl.Attributes; a != null; a = a.Next) {
        if (a.Key == "prover" && a.Params.Count == 1) {
          string cmd = a.Params[0] as string;
          if (cmd != null) {
            int pos = cmd.IndexOf(':');
            if (pos <= 0)
              throw new ProverException("Invalid syntax of :prover string: `" + cmd + "'");
            string kind = cmd.Substring(0, pos);
            if (genOptions.IsAnyProverCommandSupported(kind))
              SayToProver(cmd.Substring(pos + 1));
          }
        }
      }
    }
    
    public override void DeclareFunction(Function f, string attributes) {//Contract.Requires(f != null);
      base.ProcessDeclaration(f);
    }

    public override void DeclareConstant(Constant c, bool uniq, string attributes) {//Contract.Requires(c != null);
      base.DeclareConstant(c, uniq, attributes);
      orderingAxiomBuilder.AddConstant(c);

      // TODO: make separate distinct lists for names coming from different types
      // e.g., one for strings, one for ints, one for program types.
      if (uniq){
        distincts.Add(c);
      }
    }
    
    public override void AddAxiom(Axiom ax, string attributes) {//Contract.Requires(ax != null);
      base.AddAxiom(ax, attributes);

      string ignore = ax.FindStringAttribute("ignore");
      if (ignore != null && genOptions.IsAnyProverCommandSupported(ignore)) {
        return;
      }

      axiomConjuncts.Add(translator.Translate(ax.Expr));
    }

    public override void AddAxiom(VCExpr vc)
    {//Contract.Requires(vc != null);
      axiomConjuncts.Add(vc);
    }

    public VCExpr Axioms {
      get {Contract.Ensures(Contract.Result<VCExpr>() != null);
        VCExpr axioms = gen.NAry(VCExpressionGenerator.AndOp, axiomConjuncts);
        List<VCExpr>/*!>!*/ distinctVars = new List<VCExpr> ();
        foreach (Variable v in distincts){
          Contract.Assert(v != null);
          distinctVars.Add(translator.LookupVariable(v));}
        axioms = gen.AndSimp(gen.Distinct(distinctVars), axioms);
        if (CommandLineOptions.Clo.TypeEncodingMethod != CommandLineOptions.TypeEncoding.Monomorphic)
          axioms = gen.AndSimp(orderingAxiomBuilder.Axioms, axioms);
        return axioms;
      }
    }

    public string GetProverCommands(bool full) {Contract.Ensures(Contract.Result<string>() != null);

      string res = (full ? proverCommands : incrementalProverCommands).ToString();
      incrementalProverCommands.Length = 0;
      return res;
    }

    public override string Lookup(VCExprVar var)
    {
        return exprTranslator.Lookup(var);
    }

    public override VCExpressionGenerator ExprGen { get {Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);

     return gen;
    } }
    public override Boogie2VCExprTranslator BoogieExprTranslator { get {Contract.Ensures(Contract.Result<Boogie2VCExprTranslator>() != null);

      return translator;
    } }
    public override VCGenerationOptions VCGenOptions { get {Contract.Ensures(Contract.Result<VCGenerationOptions>() != null);

      return genOptions;
    } }
  }

  // Translator from VCExpressions to strings, which are implemented
  // by the various provers
  [ContractClass(typeof(VCExprTranslatorContracts))]
  public abstract class VCExprTranslator : ICloneable {
    public abstract string translate(VCExpr expr, int polarity);
    public abstract string Lookup(VCExprVar var);
    public abstract Object Clone();
  }

  [ContractClassFor(typeof(VCExprTranslator))]

  public abstract class VCExprTranslatorContracts : VCExprTranslator {
    public override object Clone() {
      Contract.Ensures(Contract.Result<object>() != null);
      throw new NotImplementedException();
    }
    public override string Lookup(VCExprVar var) {
      Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<string>() != null);

      throw new NotImplementedException();
    }
    public override string translate(VCExpr expr, int polarity) {

      Contract.Requires(expr != null);

      Contract.Ensures(Contract.Result<string>() != null);

      throw new NotImplementedException();
    }
  }
}
