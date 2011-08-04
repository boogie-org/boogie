//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Diagnostics.Contracts;
using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.Simplify;
using VC;
using Microsoft.Boogie.Z3;
using System.Collections;
using System.IO;
using System.Threading;

namespace Microsoft.Boogie.Houdini {
  public class HoudiniChecker {
    private Stack<VCExpr> axioms = new Stack<VCExpr>();
    private Checker checker;
    private string descriptiveName;
    private VCExpr conjecture;
    private ProverInterface.ErrorHandler handler;
        
    internal HoudiniChecker(Checker checker) 
    {
      Contract.Requires(checker.TheoremProver != null);
      Contract.Requires(checker.TheoremProver is Z3ProcessTheoremProver);
      this.checker = checker;
    }
    
    public void PrepareCheck(string _descriptiveName, VCExpr _vc, ProverInterface.ErrorHandler _handler) 
    {
      this.descriptiveName = _descriptiveName;
      this.conjecture = _vc;
      this.handler = _handler;
    }

    public void PushAxiom(VCExpr vc) {
      axioms.Push(vc);
    }

    public void Pop() {
      axioms.Pop();
    }    

    private VCExpr BuildVCAxioms(Stack<VCExpr> axioms) 
    {
      Contract.Requires(axioms.Count > 0);
      VCExpr vc_axioms = null;
      foreach (VCExpr axiom in axioms) {
        if (vc_axioms == null)
          vc_axioms = axiom;
        else
          vc_axioms = checker.VCExprGen.And(vc_axioms,axiom);
      }
      return vc_axioms;
    }
    
    public void Check() 
    {
      Contract.Assert (descriptiveName != null);
      Contract.Assert (conjecture != null);
      Contract.Assert (handler != null);
      outcome = ProverInterface.Outcome.Undetermined;
      
      VCExpr vc;
      if (axioms.Count > 0) {
        VCExpr vc_axioms = BuildVCAxioms(axioms);
        vc = checker.VCExprGen.Implies(vc_axioms, conjecture);
      }
      else {
        vc = conjecture;
      }
      checker.BeginCheck(descriptiveName, vc, handler);
      WaitHandle.WaitAny(new WaitHandle[] {checker.ProverDone});
    }
   
    private ProverInterface.Outcome outcome;
    private UnexpectedProverOutputException outputExn;

    public ProverInterface.Outcome ReadOutcome()
    {
      try {
        outcome = checker.ReadOutcome();
      } catch (UnexpectedProverOutputException e) {
        throw e;
      }
      return outcome;
    }
  }

  public class HoudiniVCGen : VCGen {
    private HoudiniChecker hdnChecker;
    private VCExpressionGenerator gen;
    CounterexampleCollector collector = new CounterexampleCollector();
    
    public HoudiniVCGen(Program program, string logFilePath, bool appendLogFile) 
      : base(program, logFilePath, appendLogFile)
    {
    }
    
    public void VerifyImplementation(Implementation impl, Program program) {
      collector.OnProgress("HdnVCGen", 0, 0, 0.0);
      if (CommandLineOptions.Clo.SoundnessSmokeTest) {
        throw new Exception("HoudiniVCGen does not support Soundness smoke test.");
      }
      
      ConvertCFG2DAG(impl, program);
      ModelViewInfo mvInfo;
      Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = PassifyImpl(impl, program, out mvInfo);
	  Hashtable/*<int, Absy!>*/ label2absy;
      Checker checker = new Checker(this, program, this.logFilePath, this.appendLogFile, impl, CommandLineOptions.Clo.ProverKillTime); 
      VCExpr vc = GenerateVC(impl, null, out label2absy, checker);
              
      ErrorReporter reporter;
      if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local) {
        reporter = new ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, incarnationOriginMap, collector, mvInfo, null, null, program);
      } else {
        reporter = new ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, incarnationOriginMap, collector, mvInfo, null, null, program);
      }
      this.gen = checker.VCExprGen;
      if (checker.TheoremProver is Z3ProcessTheoremProver)
        this.hdnChecker = new HoudiniChecker(checker);
      else
        throw new Exception("HdnChecker only works with z3");
      this.hdnChecker.PrepareCheck(impl.Name, vc, reporter);
      this.hdnChecker.Check();
    }
    
    public void PushAxiom(Axiom axiom) 
    {
      Contract.Assume(hdnChecker != null);
      Contract.Assume(gen != null);
      //VCExpr vc = axiom.Expr.VCView(gen);
      //this.hdnChecker.PushAxiom(vc);
    }

    public void Pop() {
      Contract.Assume(hdnChecker!=null);
      hdnChecker.Pop();
    }
    
    public Outcome Verify(out List<Counterexample> errors)       
  {
      Contract.Assume (hdnChecker != null);
      collector.examples.Clear();
      hdnChecker.Check();
      ProverInterface.Outcome proverOutcome;
      proverOutcome = hdnChecker.ReadOutcome();
      Outcome verifyOutcome = ReadOutcome(proverOutcome);
      if (verifyOutcome == Outcome.Errors) {
        Contract.Assume (collector.examples != null);
        if (collector.examples.Count == 0) {
            string memStr = System.Convert.ToString(System.GC.GetTotalMemory(false));
            if (memStr != null)
                memStr = "?";
            throw new UnexpectedProverOutputException("Outcome.Errors w/ 0 counter examples. " + memStr + " memory used");
        }
        errors = collector.examples;
      } else {
        errors = null;
      }
      return verifyOutcome;
    }

    private Outcome ReadOutcome(ProverInterface.Outcome proverOutcome) {
      switch (proverOutcome) {
          case ProverInterface.Outcome.Valid:
            return Outcome.Correct;
          case ProverInterface.Outcome.Invalid:
            return Outcome.Errors;
          case ProverInterface.Outcome.TimeOut:
            return Outcome.TimedOut;
          case ProverInterface.Outcome.Undetermined:
            return Outcome.Inconclusive;
          default:
            throw new Exception("Unknown Prover Interface outcome while reading outcome.");
        }
    }

  }
  
  
}