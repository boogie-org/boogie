using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using VC;

namespace Microsoft.Boogie;

sealed class CachedVerificationResultInjector : StandardVisitor
{
  private ExecutionEngineOptions options;
  readonly Program Program;

  // TODO(wuestholz): We should probably increase the threshold to something like 2 seconds.
  static readonly double TimeThreshold = -1.0d;
  Program programInCachedSnapshot;
  Implementation currentImplementation;
  int assumptionVariableCount;
  int temporaryVariableCount;

  public static readonly CachedVerificationResultInjectorStatistics Statistics =
    new CachedVerificationResultInjectorStatistics();

  int FreshAssumptionVariableName
  {
    get { return assumptionVariableCount++; }
  }

  int FreshTemporaryVariableName
  {
    get { return temporaryVariableCount++; }
  }

  CachedVerificationResultInjector(ExecutionEngineOptions options, Program program)
  {
    Program = program;
    this.options = options;
  }

  public Implementation Inject(Implementation implementation, Program programInCachedSnapshot)
  {
    Contract.Requires(implementation != null && programInCachedSnapshot != null);

    this.programInCachedSnapshot = programInCachedSnapshot;
    assumptionVariableCount = 0;
    temporaryVariableCount = 0;
    currentImplementation = implementation;

    #region Introduce explict assumption about the precondition.

    var oldProc = programInCachedSnapshot.FindProcedure(currentImplementation.Proc.Name);
    if (oldProc != null
        && oldProc.DependencyChecksum != currentImplementation.Proc.DependencyChecksum
        && currentImplementation.ExplicitAssumptionAboutCachedPrecondition == null)
    {
      var axioms = new List<Axiom>();
      var after = new List<Cmd>();
      Expr assumedExpr = new LiteralExpr(Token.NoToken, false);
      var canUseSpecs = DependencyCollector.CanExpressOldSpecs(oldProc, Program, true);
      if (canUseSpecs && oldProc.SignatureEquals(options, currentImplementation.Proc))
      {
        var always = Substituter.SubstitutionFromDictionary(currentImplementation.GetImplFormalMap(options), true,
          currentImplementation.Proc);
        var forOld = Substituter.SubstitutionFromDictionary(new Dictionary<Variable, Expr>());
        var clauses = oldProc.Requires.Select(r =>
          Substituter.FunctionCallReresolvingApply(always, forOld, r.Condition, Program));
        var conj = Expr.And(clauses, true);
        assumedExpr = conj != null
          ? FunctionExtractor.Extract(conj, Program, axioms)
          : new LiteralExpr(Token.NoToken, true);
      }

      if (assumedExpr != null)
      {
        var lv = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, string.Format("a##cached##{0}", FreshAssumptionVariableName), Type.Bool),
          new QKeyValue(Token.NoToken, "assumption", new List<object>(), null));
        currentImplementation.InjectAssumptionVariable(lv, !canUseSpecs);
        var lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, lv));
        var rhs = LiteralExpr.And(new IdentifierExpr(Token.NoToken, lv), assumedExpr);
        var assumed = new AssignCmd(currentImplementation.tok, new List<AssignLhs> {lhs}, new List<Expr> {rhs});
        assumed.IrrelevantForChecksumComputation = true;
        currentImplementation.ExplicitAssumptionAboutCachedPrecondition = assumed;
        after.Add(assumed);
      }

      if (options.TraceCachingForTesting || options.TraceCachingForBenchmarking) {
        using var tokTxtWr = new TokenTextWriter("<console>", options.OutputWriter, false, false, options);
        var loc = currentImplementation.tok != null && currentImplementation.tok != Token.NoToken
          ? string.Format("{0}({1},{2})", currentImplementation.tok.filename, currentImplementation.tok.line,
            currentImplementation.tok.col)
          : "<unknown location>";
        options.OutputWriter.WriteLine("Processing implementation {0} (at {1}):", currentImplementation.VerboseName, loc);
        foreach (var a in axioms)
        {
          options.OutputWriter.Write("  >>> added axiom: ");
          a.Expr.Emit(tokTxtWr);
          options.OutputWriter.WriteLine();
        }

        foreach (var b in after)
        {
          options.OutputWriter.Write("  >>> added after assuming the current precondition: ");
          b.Emit(tokTxtWr, 0);
        }
      }
    }

    #endregion

    var result = VisitImplementation(currentImplementation);
    currentImplementation = null;
    this.programInCachedSnapshot = null;
    return result;
  }

  public static void Inject(ExecutionEngine engine, Program program, 
    IReadOnlyList<Implementation> implementations, string requestId,
    string programId, out long[] cachingActionCounts)
  {
    var eai = new CachedVerificationResultInjector(engine.Options, program);

    cachingActionCounts = new long[Enum.GetNames(typeof(VC.ConditionGeneration.CachingAction)).Length];
    var run = new CachedVerificationResultInjectorRun
    {
      Start = DateTime.UtcNow, ImplementationCount = implementations.Count(),
      CachingActionCounts = cachingActionCounts
    };
    foreach (var impl in implementations)
    {
      var vr = engine.Cache.Lookup(impl, engine.Options.RunDiagnosticsOnTimeout, out var priority);
      if (vr != null && vr.ProgramId == programId)
      {
        if (priority == Priority.LOW)
        {
          run.LowPriorityImplementationCount++;
        }
        else if (priority == Priority.MEDIUM)
        {
          run.MediumPriorityImplementationCount++;
        }
        else if (priority == Priority.HIGH)
        {
          run.HighPriorityImplementationCount++;
        }
        else if (priority == Priority.SKIP)
        {
          run.SkippedImplementationCount++;
        }

        if (priority == Priority.LOW || priority == Priority.MEDIUM || engine.Options.VerifySnapshots >= 3)
        {
          if (TimeThreshold < vr.End.Subtract(vr.Start).TotalMilliseconds)
          {
            eai.SetErrorAndAssertionChecksumsInCachedSnapshot(impl, vr);
            if (vr.ProgramId != null)
            {
              var p = engine.Cache.CachedProgram(vr.ProgramId);
              if (p != null)
              {
                eai.Inject(impl, p);
                run.TransformedImplementationCount++;
              }
            }
          }
        }
      }
    }

    run.End = DateTime.UtcNow;
    Statistics.AddRun(requestId, run);
  }

  private void SetErrorAndAssertionChecksumsInCachedSnapshot(Implementation implementation,
    ImplementationRunResult result)
  {
    if (result.VcOutcome == VcOutcome.Errors && result.Errors != null &&
        result.Errors.Count < options.ErrorLimit)
    {
      implementation.SetErrorChecksumToCachedError(result.Errors.Select(cex =>
        new Tuple<byte[], byte[], object>(cex.Checksum, cex.SugaredCmdChecksum, cex)));
      implementation.AssertionChecksumsInCachedSnapshot = result.AssertionChecksums;
    }
    else if (result.VcOutcome == VcOutcome.Correct)
    {
      implementation.SetErrorChecksumToCachedError(new List<Tuple<byte[], byte[], object>>());
      implementation.AssertionChecksumsInCachedSnapshot = result.AssertionChecksums;
    }
  }

  public override Cmd VisitCallCmd(CallCmd node)
  {
    var result = base.VisitCallCmd(node);

    var oldProc = programInCachedSnapshot.FindProcedure(node.Proc.Name);
    if (oldProc != null
        && oldProc.DependencyChecksum != node.Proc.DependencyChecksum
        && node.AssignedAssumptionVariable == null)
    {
      var before = new List<Cmd>();
      var beforePreconditionCheck = new List<Cmd>();
      var after = new List<Cmd>();
      var axioms = new List<Axiom>();
      Expr assumedExpr = new LiteralExpr(Token.NoToken, false);
      // TODO(wuestholz): Try out two alternatives: only do this for low priority implementations or not at all.
      var canUseSpecs = DependencyCollector.CanExpressOldSpecs(oldProc, Program);
      if (canUseSpecs && oldProc.SignatureEquals(options, node.Proc))
      {
        var desugaring = node.GetDesugaring(options);
        Contract.Assert(desugaring != null);
        var precond = node.CheckedPrecondition(oldProc, Program, e => FunctionExtractor.Extract(e, Program, axioms));
        if (precond != null)
        {
          var assume = new AssumeCmd(node.tok, precond,
            new QKeyValue(Token.NoToken, "precondition_previous_snapshot", new List<object>(), null));
          assume.IrrelevantForChecksumComputation = true;
          beforePreconditionCheck.Add(assume);
        }

        var unmods = node.UnmodifiedBefore(oldProc);
        var eqs = new List<Expr>();
        foreach (var unmod in unmods)
        {
          var oldUnmod = new LocalVariable(Token.NoToken,
            new TypedIdent(Token.NoToken, string.Format("{0}##old##{1}", unmod.Name, FreshTemporaryVariableName),
              unmod.Type));
          var lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, oldUnmod));
          var rhs = new IdentifierExpr(Token.NoToken, unmod.Decl);
          var cmd = new AssignCmd(Token.NoToken, new List<AssignLhs> {lhs}, new List<Expr> {rhs});
          cmd.IrrelevantForChecksumComputation = true;
          before.Add(cmd);
          var eq = LiteralExpr.Eq(new IdentifierExpr(Token.NoToken, oldUnmod),
            new IdentifierExpr(Token.NoToken, unmod.Decl));
          eq.Type = Type.Bool;
          eq.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
          eqs.Add(eq);
        }

        var mods = node.ModifiedBefore(oldProc);
        var oldSubst = new Dictionary<Variable, Expr>();
        foreach (var mod in mods)
        {
          var oldMod = new LocalVariable(Token.NoToken,
            new TypedIdent(Token.NoToken, string.Format("{0}##old##{1}", mod.Name, FreshTemporaryVariableName),
              mod.Type));
          oldSubst[mod.Decl] = new IdentifierExpr(Token.NoToken, oldMod);
          var lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, oldMod));
          var rhs = new IdentifierExpr(Token.NoToken, mod.Decl);
          var cmd = new AssignCmd(Token.NoToken, new List<AssignLhs> {lhs}, new List<Expr> {rhs});
          cmd.IrrelevantForChecksumComputation = true;
          before.Add(cmd);
        }

        assumedExpr = node.Postcondition(oldProc, eqs, oldSubst, Program,
          e => FunctionExtractor.Extract(e, Program, axioms));
        if (assumedExpr == null)
        {
          assumedExpr = new LiteralExpr(Token.NoToken, true);
        }
      }

      if (assumedExpr != null)
      {
        var lv = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, string.Format("a##cached##{0}", FreshAssumptionVariableName), Type.Bool),
          new QKeyValue(Token.NoToken, "assumption", new List<object>(), null));
        node.AssignedAssumptionVariable = lv;
        currentImplementation.InjectAssumptionVariable(lv, !canUseSpecs);
        var lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, lv));
        var rhs = LiteralExpr.And(new IdentifierExpr(Token.NoToken, lv), assumedExpr);
        var assumed = new AssignCmd(node.tok, new List<AssignLhs> {lhs}, new List<Expr> {rhs});
        assumed.IrrelevantForChecksumComputation = true;
        after.Add(assumed);
      }

      node.ExtendDesugaring(options, before, beforePreconditionCheck, after);
      if (options.TraceCachingForTesting || options.TraceCachingForBenchmarking) {
        using var tokTxtWr = new TokenTextWriter("<console>", options.OutputWriter, false, false, options);
        var loc = node.tok != null && node.tok != Token.NoToken
          ? $"{node.tok.filename}({node.tok.line},{node.tok.col})"
          : "<unknown location>";
        options.OutputWriter.WriteLine("Processing call to procedure {0} in implementation {1} (at {2}):", node.Proc.VerboseName,
          currentImplementation.VerboseName, loc);
        foreach (var a in axioms)
        {
          options.OutputWriter.Write("  >>> added axiom: ");
          a.Expr.Emit(tokTxtWr);
          options.OutputWriter.WriteLine();
        }

        foreach (var b in before)
        {
          options.OutputWriter.Write("  >>> added before: ");
          b.Emit(tokTxtWr, 0);
        }

        foreach (var b in beforePreconditionCheck)
        {
          options.OutputWriter.Write("  >>> added before precondition check: ");
          b.Emit(tokTxtWr, 0);
        }

        foreach (var a in after)
        {
          options.OutputWriter.Write("  >>> added after: ");
          a.Emit(tokTxtWr, 0);
        }
      }
    }

    return result;
  }
}