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
  public class ExistentialConstantCollector : StandardVisitor {
    public static void CollectHoudiniConstants(Houdini houdini, Implementation impl, out HashSet<Variable> houdiniAssertConstants, out HashSet<Variable> houdiniAssumeConstants) {
      ExistentialConstantCollector collector = new ExistentialConstantCollector(houdini);
      collector.VisitImplementation(impl);
      houdiniAssertConstants = collector.houdiniAssertConstants;
      houdiniAssumeConstants = collector.houdiniAssumeConstants;
    }
    private ExistentialConstantCollector(Houdini houdini) {
      this.houdini = houdini;
      this.houdiniAssertConstants = new HashSet<Variable>();
      this.houdiniAssumeConstants = new HashSet<Variable>();
    }
    private Houdini houdini;
    private HashSet<Variable> houdiniAssertConstants;
    private HashSet<Variable> houdiniAssumeConstants;
    public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node) {
      AddHoudiniConstant(node);
      return base.VisitAssertRequiresCmd(node);
    }
    public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node) {
      AddHoudiniConstant(node);
      return base.VisitAssertEnsuresCmd(node);
    }
    public override Cmd VisitAssertCmd(AssertCmd node) {
      AddHoudiniConstant(node);
      return base.VisitAssertCmd(node);
    }
    public override Cmd VisitAssumeCmd(AssumeCmd node) {
      AddHoudiniConstant(node);
      return base.VisitAssumeCmd(node);
    }
    private void AddHoudiniConstant(AssertCmd assertCmd)
    {
        Variable houdiniConstant;
        if (houdini.MatchCandidate(assertCmd.Expr, out houdiniConstant))
            houdiniAssertConstants.Add(houdiniConstant);
    }
    private void AddHoudiniConstant(AssumeCmd assumeCmd)
    {
        Variable houdiniConstant;
        if (houdini.MatchCandidate(assumeCmd.Expr, out houdiniConstant))
            houdiniAssumeConstants.Add(houdiniConstant);
    }
  }

  public class HoudiniSession {
    public static double proverTime = 0;
    public static int numProverQueries = 0;
    public static double unsatCoreProverTime = 0;
    public static int numUnsatCoreProverQueries = 0;
    public static int numUnsatCorePrunings = 0;

    public string descriptiveName;
    private VCExpr conjecture;
    private ProverInterface.ErrorHandler handler;
    ConditionGeneration.CounterexampleCollector collector;
    HashSet<Variable> unsatCoreSet;
    HashSet<Variable> houdiniConstants;
    public HashSet<Variable> houdiniAssertConstants;
    Houdini houdini;
    Implementation implementation;

    public bool InUnsatCore(Variable constant) {
      if (unsatCoreSet == null)
        return true;
      if (unsatCoreSet.Contains(constant))
        return true;
      numUnsatCorePrunings++;
      return false;
    }

    public HoudiniSession(Houdini houdini, VCGen vcgen, ProverInterface proverInterface, Program program, Implementation impl) {
      descriptiveName = impl.Name;
      collector = new ConditionGeneration.CounterexampleCollector();
      collector.OnProgress("HdnVCGen", 0, 0, 0.0);

      vcgen.ConvertCFG2DAG(impl);
      ModelViewInfo mvInfo;
      Hashtable/*TransferCmd->ReturnCmd*/ gotoCmdOrigins = vcgen.PassifyImpl(impl, out mvInfo);

      HashSet<Variable> houdiniAssumeConstants;
      ExistentialConstantCollector.CollectHoudiniConstants(houdini, impl, out houdiniAssertConstants, out houdiniAssumeConstants);
      houdiniConstants = new HashSet<Variable>();
      houdiniConstants.UnionWith(houdiniAssertConstants);
      houdiniConstants.UnionWith(houdiniAssumeConstants);

      var exprGen = proverInterface.Context.ExprGen;
      VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : exprGen.Integer(BigNum.ZERO);

      Hashtable/*<int, Absy!>*/ label2absy;
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
        handler = new VCGen.ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, proverInterface.Context, program);
      }
      else {
        handler = new VCGen.ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, proverInterface.Context, program);
      }

      this.houdini = houdini;
      this.implementation = impl;
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

      /*
      foreach (Variable constant in this.houdiniConstants) {
        VCExprVar exprVar = exprTranslator.LookupVariable(constant);
        if (currentAssignment[constant]) {
          expr = exprGen.And(expr, exprVar);
        }
        else {
          expr = exprGen.And(expr, exprGen.Not(exprVar));
        }
      }
       */
      return expr;
    }

    public ProverInterface.Outcome Verify(ProverInterface proverInterface, Dictionary<Variable, bool> assignment, out List<Counterexample> errors) {
      collector.examples.Clear();

      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Verifying " + descriptiveName);
      }
      DateTime now = DateTime.UtcNow;

      VCExpr vc = proverInterface.VCExprGen.Implies(BuildAxiom(proverInterface, assignment), conjecture);
      proverInterface.BeginCheck(descriptiveName, vc, handler);
      ProverInterface.Outcome proverOutcome = proverInterface.CheckOutcome(handler);

      double queryTime = (DateTime.UtcNow - now).TotalSeconds;
      proverTime += queryTime;
      numProverQueries++;
      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine("Time taken = " + queryTime);
      }

      errors = collector.examples;
      return proverOutcome;
    }

    public void UpdateUnsatCore(ProverInterface proverInterface, Dictionary<Variable, bool> assignment) {
      DateTime now = DateTime.UtcNow;

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
      ProverInterface.Outcome tmp = proverInterface.CheckAssumptions(assumptionExprs, out unsatCore, handler);
      System.Diagnostics.Debug.Assert(tmp == ProverInterface.Outcome.Valid);
      unsatCoreSet = new HashSet<Variable>();
      foreach (int i in unsatCore)
        unsatCoreSet.Add(assumptionVars[i]);
      proverInterface.Pop();

      double unsatCoreQueryTime = (DateTime.UtcNow - now).TotalSeconds;
      unsatCoreProverTime += unsatCoreQueryTime;
      numUnsatCoreProverQueries++;
    }

  }
}