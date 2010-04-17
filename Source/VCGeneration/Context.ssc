//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Microsoft.Contracts;
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
  public abstract class ProverContext : ICloneable {
    protected virtual void ProcessDeclaration(Declaration! decl) {}
    public virtual void DeclareType(TypeCtorDecl! t, string attributes) { ProcessDeclaration(t); }
    public virtual void DeclareConstant(Constant! c, bool uniq, string attributes) { ProcessDeclaration(c); }
    public virtual void DeclareFunction(Function! f, string attributes) { ProcessDeclaration(f); }
    public virtual void AddAxiom(Axiom! a, string attributes) { ProcessDeclaration(a); }
    public abstract void AddAxiom(VCExpr! vc);
    public virtual void DeclareGlobalVariable(GlobalVariable! v, string attributes) { ProcessDeclaration(v); }
    
    public abstract VCExpressionGenerator! ExprGen { get; }
    public abstract Boogie2VCExprTranslator! BoogieExprTranslator { get; }
    public abstract VCGenerationOptions! VCGenOptions { get; }

    public abstract object! Clone();
  }
  
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  
  /// <summary>
  /// This ProverContext subclass is intended for use with untyped provers that do not require names
  /// to be declared before use.  It constructs its context from unique constants and given axioms.
  /// </summary>
  public class DeclFreeProverContext : ProverContext {
    protected VCExpressionGenerator! gen;
    protected VCGenerationOptions! genOptions;
    protected Boogie2VCExprTranslator! translator;
    
    protected OrderingAxiomBuilder! orderingAxiomBuilder;

    StringBuilder! proverCommands;
    StringBuilder! incrementalProverCommands;
    
    protected List<Variable!>! distincts;
    protected List<VCExpr!>! axiomConjuncts;

    public VCExprTranslator exprTranslator;

    public DeclFreeProverContext(VCExpressionGenerator! gen,
                                 VCGenerationOptions! genOptions) {
      this.gen = gen;
      this.genOptions = genOptions;
      Boogie2VCExprTranslator! t = new Boogie2VCExprTranslator (gen, genOptions);
      this.translator = t;
      OrderingAxiomBuilder! oab = new OrderingAxiomBuilder(gen, t);
      oab.Setup();
      this.orderingAxiomBuilder = oab;

      proverCommands = new StringBuilder();
      incrementalProverCommands = new StringBuilder();
    
      distincts = new List<Variable!>();
      axiomConjuncts = new List<VCExpr!>();

      exprTranslator = null;
    }

    private DeclFreeProverContext(DeclFreeProverContext! ctxt) {
      this.gen = ctxt.gen;
      this.genOptions = ctxt.genOptions;
      Boogie2VCExprTranslator! t = (Boogie2VCExprTranslator)ctxt.translator.Clone();
      this.translator = t;
      this.orderingAxiomBuilder = new OrderingAxiomBuilder(ctxt.gen, t, ctxt.orderingAxiomBuilder);

      StringBuilder! cmds = new StringBuilder ();
      cmds.Append(ctxt.proverCommands);
      proverCommands = cmds;
      StringBuilder! incCmds = new StringBuilder ();
      incCmds.Append(ctxt.incrementalProverCommands);
      incrementalProverCommands = incCmds;
    
      distincts = new List<Variable!>(ctxt.distincts);
      axiomConjuncts = new List<VCExpr!>(ctxt.axiomConjuncts);

      if (ctxt.exprTranslator == null)
        exprTranslator = null;
      else
        exprTranslator = (VCExprTranslator!)ctxt.exprTranslator.Clone();
    }

    public override object! Clone() {
      return new DeclFreeProverContext(this);
    }

    internal protected void SayToProver(string! msg)
    {
      msg = msg + "\r\n";
      proverCommands.Append(msg);
      incrementalProverCommands.Append(msg);
    }

    protected override void ProcessDeclaration(Declaration! decl)
    {
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
    
    public override void DeclareFunction(Function! f, string attributes) {
      base.ProcessDeclaration(f);
    }

    public override void DeclareConstant(Constant! c, bool uniq, string attributes) {
      base.DeclareConstant(c, uniq, attributes);
      orderingAxiomBuilder.AddConstant(c);

      // TODO: make separate distinct lists for names coming from different types
      // e.g., one for strings, one for ints, one for program types.
      if (uniq){
        distincts.Add(c);
      }
    }
    
    public override void AddAxiom(Axiom! ax, string attributes) {
      base.AddAxiom(ax, attributes);

      string ignore = ax.FindStringAttribute("ignore");
      if (ignore != null && genOptions.IsAnyProverCommandSupported(ignore)) {
        return;
      }

      axiomConjuncts.Add(translator.Translate(ax.Expr));
    }

    public override void AddAxiom(VCExpr! vc)
    {
      axiomConjuncts.Add(vc);
    }

    public VCExpr! Axioms {
      get {
        VCExpr axioms = gen.NAry(VCExpressionGenerator.AndOp, axiomConjuncts);
        List<VCExpr!>! distinctVars = new List<VCExpr!> ();
        foreach (Variable! v in distincts)
          distinctVars.Add(translator.LookupVariable(v));
        axioms = gen.AndSimp(gen.Distinct(distinctVars), axioms);
        if (CommandLineOptions.Clo.TypeEncodingMethod != CommandLineOptions.TypeEncoding.Monomorphic)
          axioms = gen.AndSimp(orderingAxiomBuilder.Axioms, axioms);
        return axioms;
      }
    }

    public string! GetProverCommands(bool full) {
      string! res = (full ? proverCommands : incrementalProverCommands).ToString();
      incrementalProverCommands.Length = 0;
      return res;
    }

    public override VCExpressionGenerator! ExprGen { get {
     return gen;
    } }
    public override Boogie2VCExprTranslator! BoogieExprTranslator { get {
      return translator;
    } }
    public override VCGenerationOptions! VCGenOptions { get {
      return genOptions;
    } }
  }

  // Translator from VCExpressions to strings, which are implemented
  // by the various provers
  public abstract class VCExprTranslator : ICloneable {
    public abstract string! translate(VCExpr! expr, int polarity);
    public abstract string! Lookup(VCExprVar! var);
    public abstract Object! Clone();    
  }
}
