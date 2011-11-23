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
  public class HoudiniSession {
    public static double proverTime = 0;
    private string descriptiveName;
    private VCExpr conjecture;
    private ProverInterface.ErrorHandler handler;
    ConditionGeneration.CounterexampleCollector collector;

    public HoudiniSession(VCGen vcgen, Checker checker, Program program, Implementation impl, string logFilePath, bool appendLogFile) {
      descriptiveName = impl.Name;
      collector = new ConditionGeneration.CounterexampleCollector();
      collector.OnProgress("HdnVCGen", 0, 0, 0.0);
      if (CommandLineOptions.Clo.SoundnessSmokeTest) {
        throw new Exception("HoudiniVCGen does not support Soundness smoke test.");
      }

      vcgen.ConvertCFG2DAG(impl, program);
      ModelViewInfo mvInfo;
      Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = vcgen.PassifyImpl(impl, program, out mvInfo);
      Hashtable/*<int, Absy!>*/ label2absy;
      
      conjecture = vcgen.GenerateVC(impl, null, out label2absy, checker);

      if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local) {
        handler = new VCGen.ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, vcgen.implName2LazyInliningInfo, checker.TheoremProver.Context, program);
      }
      else {
        handler = new VCGen.ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, vcgen.implName2LazyInliningInfo, checker.TheoremProver.Context, program);
      }
    }

    public ProverInterface.Outcome Verify(Checker checker, VCExpr axiom, out List<Counterexample> errors) {
      collector.examples.Clear();
      VCExpr vc = checker.VCExprGen.Implies(axiom, conjecture);

      DateTime now = DateTime.Now;
      checker.BeginCheck(descriptiveName, vc, handler);
      WaitHandle.WaitAny(new WaitHandle[] { checker.ProverDone });
      ProverInterface.Outcome proverOutcome = checker.ReadOutcome();
      proverTime += (DateTime.Now - now).TotalSeconds;

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