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
using Microsoft.Boogie.Z3;
using Microsoft.Boogie.SMTLib;
using System.Collections;
using System.IO;
using System.Threading;
using VC;

namespace Microsoft.Boogie.Houdini {
  public class HoudiniVCGen : VCGen {
    private Checker checker;
    private string descriptiveName;
    private VCExpr conjecture;
    private ProverInterface.ErrorHandler handler;
    CounterexampleCollector collector;

    public VCExpressionGenerator VCExprGenerator {
      get {
        return checker.VCExprGen;
      }
    }

    public Boogie2VCExprTranslator BooogieExprTranslator {
      get {
        DeclFreeProverContext proverContext = (DeclFreeProverContext)checker.TheoremProver.Context;
        return proverContext.BoogieExprTranslator;
      }
    }

    public HoudiniVCGen(Program program, Implementation impl, string logFilePath, bool appendLogFile) 
    : base(program, logFilePath, appendLogFile) {
      descriptiveName = impl.Name;
      collector = new CounterexampleCollector();
      collector.OnProgress("HdnVCGen", 0, 0, 0.0);
      if (CommandLineOptions.Clo.SoundnessSmokeTest) {
        throw new Exception("HoudiniVCGen does not support Soundness smoke test.");
      }

      ConvertCFG2DAG(impl, program);
      ModelViewInfo mvInfo;
      Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = PassifyImpl(impl, program, out mvInfo);
      Hashtable/*<int, Absy!>*/ label2absy;
      checker = new Checker(this, program, logFilePath, appendLogFile, impl, CommandLineOptions.Clo.ProverKillTime);
      if (!(checker.TheoremProver is Z3ProcessTheoremProver || checker.TheoremProver is SMTLibProcessTheoremProver)) {
        throw new Exception("HdnChecker only works with z3");
      }
      conjecture = GenerateVC(impl, null, out label2absy, checker);

      if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local) {
        handler = new ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, incarnationOriginMap, collector, mvInfo, implName2LazyInliningInfo, checker.TheoremProver.Context, program);
      }
      else {
        handler = new ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, incarnationOriginMap, collector, mvInfo, implName2LazyInliningInfo, checker.TheoremProver.Context, program);
      }
    }

    public ProverInterface.Outcome Verify(VCExpr axiom, out List<Counterexample> errors) {
      collector.examples.Clear();
      VCExpr vc = checker.VCExprGen.Implies(axiom, conjecture);
      checker.BeginCheck(descriptiveName, vc, handler);
      WaitHandle.WaitAny(new WaitHandle[] { checker.ProverDone });

      ProverInterface.Outcome proverOutcome = checker.ReadOutcome();
      if (proverOutcome == ProverInterface.Outcome.Invalid) {
        Contract.Assume(collector.examples != null);
        if (collector.examples.Count == 0) {
          string memStr = System.Convert.ToString(System.GC.GetTotalMemory(false));
          if (memStr != null)
            memStr = "?";
          throw new UnexpectedProverOutputException("Outcome.Errors w/ 0 counter examples. " + memStr + " memory used");
        }
        errors = collector.examples;
      }
      else {
        errors = null;
      }
      return proverOutcome;
    }

  }
}