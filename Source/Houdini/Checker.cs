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
using Microsoft.Basetypes;
using System.Collections;
using System.IO;
using System.Threading;
using VC;

namespace Microsoft.Boogie.Houdini {
  public class HoudiniSession {
    public static double proverTime = 0;
    public static int numProverQueries = 0;
    public string descriptiveName;
    private VCExpr conjecture;
    private ProverInterface.ErrorHandler handler;
    ConditionGeneration.CounterexampleCollector collector;
    LocalVariable controlFlowVariable;
    int entryBlockId;

    public HoudiniSession(VCGen vcgen, Checker checker, Program program, Implementation impl) {
      descriptiveName = impl.Name;
      collector = new ConditionGeneration.CounterexampleCollector();
      collector.OnProgress("HdnVCGen", 0, 0, 0.0);

      vcgen.ConvertCFG2DAG(impl, program);
      ModelViewInfo mvInfo;
      Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = vcgen.PassifyImpl(impl, program, out mvInfo);
      Hashtable/*<int, Absy!>*/ label2absy;

      if (!CommandLineOptions.Clo.UseLabels) {
        controlFlowVariable = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "@cfc", Microsoft.Boogie.Type.Int));
        impl.LocVars.Add(controlFlowVariable);
        entryBlockId = impl.Blocks[0].UniqueId;
      }
      
      conjecture = vcgen.GenerateVC(impl, controlFlowVariable, out label2absy, checker);

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

      if (!CommandLineOptions.Clo.UseLabels) {
        var ctx = checker.TheoremProver.Context;
        var bet = ctx.BoogieExprTranslator;
        VCExpr controlFlowVariableExpr = bet.LookupVariable(controlFlowVariable);
        VCExpr eqExpr1 = ctx.ExprGen.Eq(controlFlowVariableExpr, ctx.ExprGen.Integer(BigNum.ZERO));
        VCExpr controlFlowFunctionAppl = ctx.ExprGen.ControlFlowFunctionApplication(controlFlowVariableExpr, ctx.ExprGen.Integer(BigNum.ZERO));
        VCExpr eqExpr2 = ctx.ExprGen.Eq(controlFlowFunctionAppl, ctx.ExprGen.Integer(BigNum.FromInt(entryBlockId)));
        vc = ctx.ExprGen.Implies(eqExpr1, ctx.ExprGen.Implies(eqExpr2, vc));
      }

      DateTime now = DateTime.UtcNow;
      checker.BeginCheck(descriptiveName, vc, handler);
      WaitHandle.WaitAny(new WaitHandle[] { checker.ProverDone });
      ProverInterface.Outcome proverOutcome = checker.ReadOutcome();
      proverTime += (DateTime.UtcNow - now).TotalSeconds;
      numProverQueries++;

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