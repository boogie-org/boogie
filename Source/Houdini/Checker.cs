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
    HashSet<Variable> unsatCoreSet;

    public bool InUnsatCore(Variable constant) {
      if (unsatCoreSet == null)
        return true;
      return unsatCoreSet.Contains(constant);
    }

    public HoudiniSession(VCGen vcgen, ProverInterface proverInterface, Program program, Implementation impl) {
      descriptiveName = impl.Name;
      collector = new ConditionGeneration.CounterexampleCollector();
      collector.OnProgress("HdnVCGen", 0, 0, 0.0);

      vcgen.ConvertCFG2DAG(impl, program);
      ModelViewInfo mvInfo;
      Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = vcgen.PassifyImpl(impl, program, out mvInfo);
      Hashtable/*<int, Absy!>*/ label2absy;

      var exprGen = proverInterface.Context.ExprGen;
      VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : exprGen.Integer(BigNum.ZERO);
      
      conjecture = vcgen.GenerateVC(impl, controlFlowVariableExpr, out label2absy, proverInterface.Context);
      if (!CommandLineOptions.Clo.UseLabels) {
        VCExpr controlFlowFunctionAppl = exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
        VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
        conjecture = exprGen.Implies(eqExpr, conjecture);
      }

      Macro macro = new Macro(Token.NoToken, descriptiveName, new VariableSeq(), new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Type.Bool), false));
      proverInterface.DefineMacro(macro, conjecture);
      conjecture = exprGen.Function(macro);

      if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local) {
        handler = new VCGen.ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, vcgen.implName2LazyInliningInfo, proverInterface.Context, program);
      }
      else {
        handler = new VCGen.ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, vcgen.implName2LazyInliningInfo, proverInterface.Context, program);
      }
    }

    private VCExpr BuildAxiom(ProverInterface proverInterface, Dictionary<Variable, bool> currentAssignment) {
      ProverContext proverContext = proverInterface.Context;
      Boogie2VCExprTranslator exprTranslator = proverContext.BoogieExprTranslator;
      VCExpressionGenerator exprGen = proverInterface.VCExprGen;

      VCExpr expr = VCExpressionGenerator.True;
      foreach (KeyValuePair<Variable, bool> kv in currentAssignment) {
        Variable constant = kv.Key;
        VCExprVar exprVar = exprTranslator.LookupVariable(constant);
        if (kv.Value) {
          expr = exprGen.And(expr, exprVar);
        }
        else {
          expr = exprGen.And(expr, exprGen.Not(exprVar));
        }
      }
      return expr;
    }

    public ProverInterface.Outcome Verify(ProverInterface proverInterface, Dictionary<Variable, bool> assignment, out List<Counterexample> errors) {
      collector.examples.Clear();
      VCExpr vc = proverInterface.VCExprGen.Implies(BuildAxiom(proverInterface, assignment), conjecture);

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Verifying " + descriptiveName);
      }
      DateTime now = DateTime.UtcNow;

      proverInterface.BeginCheck(descriptiveName, vc, handler);
      ProverInterface.Outcome proverOutcome = proverInterface.CheckOutcome(handler);

#if UNSAT_CORE
      Boogie2VCExprTranslator exprTranslator = proverInterface.Context.BoogieExprTranslator;
      proverInterface.Push();
      proverInterface.Assert(conjecture, false);
      foreach (var v in assignment.Keys) {
        if (assignment[v]) continue;
        proverInterface.Assert(exprTranslator.LookupVariable(v), false);
      }
      List<Variable> assumptionVars = new List<Variable>();
      List<VCExpr> assumptionExprs = new List<VCExpr>();
      foreach (var v in assignment.Keys) {
        if (!assignment[v]) continue;
        assumptionVars.Add(v);
        assumptionExprs.Add(exprTranslator.LookupVariable(v));
      }
      List<int> unsatCore;
      ProverInterface.Outcome proverOutcome = proverInterface.CheckAssumptions(assumptionExprs, out unsatCore, handler);
      unsatCoreSet = new HashSet<Variable>();
      foreach (int i in unsatCore)
        unsatCoreSet.Add(assumptionVars[i]);
      proverInterface.Pop();
#endif

      double queryTime = (DateTime.UtcNow - now).TotalSeconds;
      proverTime += queryTime;
      numProverQueries++;
      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Time taken = " + queryTime);
      }

      errors = collector.examples;
      return proverOutcome;
    }

  }
}