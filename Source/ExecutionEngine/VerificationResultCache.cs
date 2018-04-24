using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Runtime.Caching;
using System.Text;
using System.Text.RegularExpressions;
using VC;

namespace Microsoft.Boogie
{

  struct CachedVerificationResultInjectorRun
  {
    public DateTime Start { get; internal set; }
    public DateTime End { get; internal set; }
    public int TransformedImplementationCount { get; internal set; }
    public int ImplementationCount { get; internal set; }
    public int SkippedImplementationCount { get; set; }
    public int LowPriorityImplementationCount { get; set; }
    public int MediumPriorityImplementationCount { get; set; }
    public int HighPriorityImplementationCount { get; set; }
    public long[] CachingActionCounts { get; set; }
  }


  sealed class CachedVerificationResultInjectorStatistics
  {
    ConcurrentDictionary<string, CachedVerificationResultInjectorRun> runs = new ConcurrentDictionary<string, CachedVerificationResultInjectorRun>();

    public bool AddRun(string requestId, CachedVerificationResultInjectorRun run)
    {
      return runs.TryAdd(requestId, run);
    }

    public string Output(bool printTime = false)
    {
      var wr = new StringWriter();
      if (runs.Any())
      {
        wr.WriteLine("Cached verification result injector statistics as CSV:");
        wr.WriteLine("Request ID, Transformed, Low, Medium, High, Skipped{0}", printTime ? ", Time (ms)" : "");
        foreach (var kv in runs.OrderBy(kv => ExecutionEngine.AutoRequestId(kv.Key)))
        {
          var t = printTime ? string.Format(", {0,8:F0}", kv.Value.End.Subtract(kv.Value.Start).TotalMilliseconds) : "";
          wr.WriteLine("{0,-19}, {1,3}, {2,3}, {3,3}, {4,3}, {5,3}{6}", kv.Key, kv.Value.TransformedImplementationCount, kv.Value.LowPriorityImplementationCount, kv.Value.MediumPriorityImplementationCount, kv.Value.HighPriorityImplementationCount, kv.Value.SkippedImplementationCount, t);
        }
      }
      return wr.ToString();
    }
  }


  sealed class CachedVerificationResultInjector : StandardVisitor
  {
    readonly Program Program;
    // TODO(wuestholz): We should probably increase the threshold to something like 2 seconds.
    static readonly double TimeThreshold = -1.0d;
    Program programInCachedSnapshot;
    Implementation currentImplementation;
    int assumptionVariableCount;
    int temporaryVariableCount;

    public static readonly CachedVerificationResultInjectorStatistics Statistics = new CachedVerificationResultInjectorStatistics();

    int FreshAssumptionVariableName
    {
      get
      {
        return assumptionVariableCount++;
      }
    }

    int FreshTemporaryVariableName
    {
      get
      {
        return temporaryVariableCount++;
      }
    }

    CachedVerificationResultInjector(Program program)
    {
      Program = program;
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
        if (canUseSpecs && oldProc.SignatureEquals(currentImplementation.Proc))
        {
          var always = Substituter.SubstitutionFromHashtable(currentImplementation.GetImplFormalMap(), true, currentImplementation.Proc);
          var forOld = Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>());
          var clauses = oldProc.Requires.Select(r => Substituter.FunctionCallReresolvingApply(always, forOld, r.Condition, Program));
          var conj = Expr.And(clauses, true);
          assumedExpr = conj != null ? FunctionExtractor.Extract(conj, Program, axioms) : new LiteralExpr(Token.NoToken, true);
        }

        if (assumedExpr != null)
        {
          var lv = new LocalVariable(Token.NoToken,
            new TypedIdent(Token.NoToken, string.Format("a##cached##{0}", FreshAssumptionVariableName), Type.Bool),
            new QKeyValue(Token.NoToken, "assumption", new List<object>(), null));
          currentImplementation.InjectAssumptionVariable(lv, !canUseSpecs);
          var lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, lv));
          var rhs = LiteralExpr.And(new IdentifierExpr(Token.NoToken, lv), assumedExpr);
          var assumed = new AssignCmd(currentImplementation.tok, new List<AssignLhs> { lhs }, new List<Expr> { rhs });
          assumed.IrrelevantForChecksumComputation = true;
          currentImplementation.ExplicitAssumptionAboutCachedPrecondition = assumed;
          after.Add(assumed);
        }

        if (CommandLineOptions.Clo.TraceCachingForTesting || CommandLineOptions.Clo.TraceCachingForBenchmarking)
        {
          using (var tokTxtWr = new TokenTextWriter("<console>", Console.Out, false, false))
          {
            var loc = currentImplementation.tok != null && currentImplementation.tok != Token.NoToken ? string.Format("{0}({1},{2})", currentImplementation.tok.filename, currentImplementation.tok.line, currentImplementation.tok.col) : "<unknown location>";
            Console.Out.WriteLine("Processing implementation {0} (at {1}):", currentImplementation.Name, loc);
            foreach (var a in axioms)
            {
              Console.Out.Write("  >>> added axiom: ");
              a.Expr.Emit(tokTxtWr);
              Console.Out.WriteLine();
            }
            foreach (var b in after)
            {
              Console.Out.Write("  >>> added after assuming the current precondition: ");
              b.Emit(tokTxtWr, 0);
            }
          }
        }
      }

      #endregion

      var result = VisitImplementation(currentImplementation);
      currentImplementation = null;
      this.programInCachedSnapshot = null;
      return result;
    }

    public static void Inject(Program program, IEnumerable<Implementation> implementations, string requestId, string programId, out long[] cachingActionCounts)
    {
      var eai = new CachedVerificationResultInjector(program);

      cachingActionCounts = new long[Enum.GetNames(typeof(VC.ConditionGeneration.CachingAction)).Length];
      var run = new CachedVerificationResultInjectorRun { Start = DateTime.UtcNow, ImplementationCount = implementations.Count(), CachingActionCounts = cachingActionCounts };
      foreach (var impl in implementations)
      {
        int priority;
        var vr = ExecutionEngine.Cache.Lookup(impl, out priority);
        if (vr != null && vr.ProgramId == programId)
        {
          if (priority == Priority.LOW) {
            run.LowPriorityImplementationCount++;
          } else if (priority == Priority.MEDIUM) {
            run.MediumPriorityImplementationCount++;
          } else if (priority == Priority.HIGH) {
            run.HighPriorityImplementationCount++;
          } else if (priority == Priority.SKIP) {
            run.SkippedImplementationCount++;
          }

          if (priority == Priority.LOW || priority == Priority.MEDIUM || 3 <= CommandLineOptions.Clo.VerifySnapshots) {
            if (TimeThreshold < vr.End.Subtract(vr.Start).TotalMilliseconds) {
              SetErrorAndAssertionChecksumsInCachedSnapshot(impl, vr);
              if (vr.ProgramId != null) {
                var p = ExecutionEngine.CachedProgram(vr.ProgramId);
                if (p != null) {
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

    private static void SetErrorAndAssertionChecksumsInCachedSnapshot(Implementation implementation, VerificationResult result)
    {
      if (result.Outcome == ConditionGeneration.Outcome.Errors && result.Errors != null && result.Errors.Count < CommandLineOptions.Clo.ProverCCLimit)
      {
        implementation.SetErrorChecksumToCachedError(result.Errors.Select(cex => new Tuple<byte[], byte[], object>(cex.Checksum, cex.SugaredCmdChecksum, cex)));
        implementation.AssertionChecksumsInCachedSnapshot = result.AssertionChecksums;
      }
      else if (result.Outcome == ConditionGeneration.Outcome.Correct)
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
        var beforePrecondtionCheck = new List<Cmd>();
        var after = new List<Cmd>();
        var axioms = new List<Axiom>();
        Expr assumedExpr = new LiteralExpr(Token.NoToken, false);
        // TODO(wuestholz): Try out two alternatives: only do this for low priority implementations or not at all.
        var canUseSpecs = DependencyCollector.CanExpressOldSpecs(oldProc, Program);
        if (canUseSpecs && oldProc.SignatureEquals(node.Proc))
        {
          var desugaring = node.Desugaring;
          Contract.Assert(desugaring != null);
          var precond = node.CheckedPrecondition(oldProc, Program, e => FunctionExtractor.Extract(e, Program, axioms));
          if (precond != null)
          {
            var assume = new AssumeCmd(node.tok, precond, new QKeyValue(Token.NoToken, "precondition_previous_snapshot", new List<object>(), null));
            assume.IrrelevantForChecksumComputation = true;
            beforePrecondtionCheck.Add(assume);
          }

          var unmods = node.UnmodifiedBefore(oldProc);
          var eqs = new List<Expr>();
          foreach (var unmod in unmods)
          {
            var oldUnmod = new LocalVariable(Token.NoToken,
              new TypedIdent(Token.NoToken, string.Format("{0}##old##{1}", unmod.Name, FreshTemporaryVariableName), unmod.Type));
            var lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, oldUnmod));
            var rhs = new IdentifierExpr(Token.NoToken, unmod.Decl);
            var cmd = new AssignCmd(Token.NoToken, new List<AssignLhs> { lhs }, new List<Expr> { rhs });
            cmd.IrrelevantForChecksumComputation = true;
            before.Add(cmd);
            var eq = LiteralExpr.Eq(new IdentifierExpr(Token.NoToken, oldUnmod), new IdentifierExpr(Token.NoToken, unmod.Decl));
            eq.Type = Type.Bool;
            eq.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
            eqs.Add(eq);
          }

          var mods = node.ModifiedBefore(oldProc);
          var oldSubst = new Dictionary<Variable, Expr>();
          foreach (var mod in mods)
          {
            var oldMod = new LocalVariable(Token.NoToken,
              new TypedIdent(Token.NoToken, string.Format("{0}##old##{1}", mod.Name, FreshTemporaryVariableName), mod.Type));
            oldSubst[mod.Decl] = new IdentifierExpr(Token.NoToken, oldMod);
            var lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, oldMod));
            var rhs = new IdentifierExpr(Token.NoToken, mod.Decl);
            var cmd = new AssignCmd(Token.NoToken, new List<AssignLhs> { lhs }, new List<Expr> { rhs });
            cmd.IrrelevantForChecksumComputation = true;
            before.Add(cmd);
          }
          
          assumedExpr = node.Postcondition(oldProc, eqs, oldSubst, Program, e => FunctionExtractor.Extract(e, Program, axioms));
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
          var assumed = new AssignCmd(node.tok, new List<AssignLhs> { lhs }, new List<Expr> { rhs });
          assumed.IrrelevantForChecksumComputation = true;
          after.Add(assumed);
        }

        node.ExtendDesugaring(before, beforePrecondtionCheck, after);
        if (CommandLineOptions.Clo.TraceCachingForTesting || CommandLineOptions.Clo.TraceCachingForBenchmarking)
        {
          using (var tokTxtWr = new TokenTextWriter("<console>", Console.Out, false, false))
          {
            var loc = node.tok != null && node.tok != Token.NoToken ? string.Format("{0}({1},{2})", node.tok.filename, node.tok.line, node.tok.col) : "<unknown location>";
            Console.Out.WriteLine("Processing call to procedure {0} in implementation {1} (at {2}):", node.Proc.Name, currentImplementation.Name, loc);
            foreach (var a in axioms)
            {
              Console.Out.Write("  >>> added axiom: ");
              a.Expr.Emit(tokTxtWr);
              Console.Out.WriteLine();
            }
            foreach (var b in before)
            {
              Console.Out.Write("  >>> added before: ");
              b.Emit(tokTxtWr, 0);
            }
            foreach (var b in beforePrecondtionCheck)
            {
              Console.Out.Write("  >>> added before precondition check: ");
              b.Emit(tokTxtWr, 0);
            }
            foreach (var a in after)
            {
              Console.Out.Write("  >>> added after: ");
              a.Emit(tokTxtWr, 0);
            }
          }
        }
      }

      return result;
    }
  }


  sealed class FunctionExtractor : StandardVisitor
  {
    readonly Dictionary<Variable, BoundVariable> Substitutions = new Dictionary<Variable, BoundVariable>();

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (node.Decl == null || !(node.Decl is LocalVariable || node.Decl is Formal || node.Decl is GlobalVariable))
      {
        return node;
      }
      else
      {
        BoundVariable boundVar;
        if (!Substitutions.TryGetValue(node.Decl, out boundVar))
        {
          boundVar = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, node.Name, node.Type));
          Substitutions[node.Decl] = boundVar;
        }
        return new IdentifierExpr(node.tok, boundVar);
      }
    }

    public static Expr Extract(Expr expr, Program program, List<Axiom> axioms)
    {
      Contract.Requires(expr != null && program != null && !program.TopLevelDeclarationsAreFrozen && axioms != null);
      
      if (expr is LiteralExpr)
      {
        return expr;
      }

      var extractor = new FunctionExtractor();

      var body = extractor.VisitExpr(expr);

      var name = program.FreshExtractedFunctionName();
      var originalVars = extractor.Substitutions.Keys.ToList();
      var formalInArgs = originalVars.Select(v => new Formal(Token.NoToken, new TypedIdent(Token.NoToken, extractor.Substitutions[v].Name, extractor.Substitutions[v].TypedIdent.Type), true)).ToList<Variable>();
      var formalOutArg = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, name + "$result$", expr.Type), false);
      var func = new Function(Token.NoToken, name, formalInArgs, formalOutArg);
      func.AddAttribute("never_pattern");

      var boundVars = originalVars.Select(k => extractor.Substitutions[k]);
      var axiomCall = new NAryExpr(Token.NoToken, new FunctionCall(func), boundVars.Select(b => new IdentifierExpr(Token.NoToken, b)).ToList<Expr>());
      axiomCall.Type = expr.Type;
      axiomCall.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      var eq = LiteralExpr.Eq(axiomCall, body);
      eq.Type = body.Type;
      eq.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      if (0 < formalInArgs.Count)
      {
        var forallExpr = new ForallExpr(Token.NoToken, boundVars.ToList<Variable>(), new Trigger(Token.NoToken, true, new List<Expr> { axiomCall }), eq);
        body = forallExpr;
        forallExpr.Attributes = new QKeyValue(Token.NoToken, "weight", new List<object> { new LiteralExpr(Token.NoToken, Basetypes.BigNum.FromInt(30)) }, null);
        body.Type = Type.Bool;
      }
      else
      {
        body = eq;
      }

      var axiom = new Axiom(Token.NoToken, body);
      func.DefinitionAxiom = axiom;
      program.AddTopLevelDeclaration(func);
      program.AddTopLevelDeclaration(axiom);
      axioms.Add(axiom);

      var call = new NAryExpr(Token.NoToken, new FunctionCall(func), originalVars.Select(v => new IdentifierExpr(Token.NoToken, v)).ToList<Expr>());
      call.Type = expr.Type;
      call.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      return call;
    }
  }


  sealed class OtherDefinitionAxiomsCollector : ReadOnlyVisitor
  {
    Axiom currentAxiom;
    Trigger currentTrigger;

    public static void Collect(IEnumerable<Axiom> axioms)
    {
      var start = DateTime.UtcNow;

      var v = new OtherDefinitionAxiomsCollector();
      foreach (var a in axioms)
      {
        v.currentAxiom = a;
        v.VisitExpr(a.Expr);
        v.currentAxiom = null;
      }

      var end = DateTime.UtcNow;
      if (CommandLineOptions.Clo.TraceCachingForDebugging)
      {
        Console.Out.WriteLine("Collected other definition axioms within {0:F0} ms.", end.Subtract(start).TotalMilliseconds);
      }
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      currentTrigger = node.Triggers;
      while (currentTrigger != null)
      {
        foreach (var e in currentTrigger.Tr)
        {
          VisitExpr(e);
        }
        currentTrigger = currentTrigger.Next;
      }
      return base.VisitQuantifierExpr(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      var funCall = node.Fun as FunctionCall;
      if (funCall != null && funCall.Func != null && funCall.Func.Checksum != null && funCall.Func.Checksum != "stable") {
        if (funCall.ArgumentCount == 0 || currentTrigger != null) {
          // We found a function call within a trigger of a quantifier expression, or the function does not take any
          // arguments so we don't expect it ever to sit inside a quantifier.
          funCall.Func.AddOtherDefinitionAxiom(currentAxiom);
        }
      }
      return base.VisitNAryExpr(node);
    }
  }


  sealed class DependencyCollector : ReadOnlyVisitor
  {
    private DeclWithFormals currentDeclaration;
    private Axiom currentAxiom;

    public static void Collect(Program program)
    {
      var start = DateTime.UtcNow;

      var dc = new DependencyCollector();
      dc.VisitProgram(program);

      var end = DateTime.UtcNow;
      if (CommandLineOptions.Clo.TraceCachingForDebugging)
      {
        Console.Out.WriteLine("Collected dependencies within {0:F0} ms.", end.Subtract(start).TotalMilliseconds);
      }
    }

    public static bool CanExpressOldSpecs(Procedure oldProc, Program newProg, bool ignoreModifiesClauses = false)
    {
      Contract.Requires(oldProc != null && newProg != null);

      var funcs = newProg.Functions;
      var globals = newProg.GlobalVariables;
      return oldProc.DependenciesCollected
             && (oldProc.FunctionDependencies == null || oldProc.FunctionDependencies.All(dep => funcs.Any(f => f.Name == dep.Name && f.DependencyChecksum == dep.DependencyChecksum)))
             && (ignoreModifiesClauses || oldProc.Modifies.All(m => globals.Any(g => g.Name == m.Name)));
    }

    public override Procedure VisitProcedure(Procedure node)
    {
      currentDeclaration = node;

      foreach (var param in node.InParams)
      {
        if (param.TypedIdent != null && param.TypedIdent.WhereExpr != null)
        {
          VisitExpr(param.TypedIdent.WhereExpr);
        }
      }

      var result = base.VisitProcedure(node);
      node.DependenciesCollected = true;
      currentDeclaration = null;
      return result;
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      currentDeclaration = node;

      foreach (var param in node.InParams)
      {
        if (param.TypedIdent != null && param.TypedIdent.WhereExpr != null)
        {
          VisitExpr(param.TypedIdent.WhereExpr);
        }
      }

      if (node.Proc != null)
      {
        node.AddProcedureDependency(node.Proc);
      }

      var result = base.VisitImplementation(node);
      node.DependenciesCollected = true;
      currentDeclaration = null;
      return result;
    }

    public override Axiom VisitAxiom(Axiom node)
    {
      if (node.DependenciesCollected)
      {
        if (currentDeclaration != null && node.FunctionDependencies != null)
        {
          foreach (var f in node.FunctionDependencies)
          {
            currentDeclaration.AddFunctionDependency(f);
          }
        }
        return node;
      }
      currentAxiom = node;
      var result = base.VisitAxiom(node);
      node.DependenciesCollected = true;
      currentAxiom = null;
      return result;
    }

    public override Function VisitFunction(Function node)
    {
      currentDeclaration = node;

      if (node.DefinitionAxiom != null)
      {
        VisitAxiom(node.DefinitionAxiom);
      }
      if (node.OtherDefinitionAxioms != null)
      {
        foreach (var a in node.OtherDefinitionAxioms)
        {
          if (a != node.DefinitionAxiom)
          {
            VisitAxiom(a);
          }
        }
      }

      var result = base.VisitFunction(node);
      node.DependenciesCollected = true;
      currentDeclaration = null;
      return result;
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      if (currentDeclaration != null)
      {
        currentDeclaration.AddProcedureDependency(node.Proc);
      }

      return base.VisitCallCmd(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      var funCall = node.Fun as FunctionCall;
      if (funCall != null)
      {
        if (currentDeclaration != null)
        {
          currentDeclaration.AddFunctionDependency(funCall.Func);
        }
        if (currentAxiom != null)
        {
          currentAxiom.AddFunctionDependency(funCall.Func);
        }
      }

      return base.VisitNAryExpr(node);
    }
  }


  static internal class Priority
  {
    public static readonly int LOW = 1;             // the same snapshot has been verified before, but a callee has changed
    public static readonly int MEDIUM = 2;          // old snapshot has been verified before
    public static readonly int HIGH = 3;            // has been never verified before
    public static readonly int SKIP = int.MaxValue; // highest priority to get them done as soon as possible
  }


  public sealed class VerificationResultCache
  {
    private readonly MemoryCache Cache = new MemoryCache("VerificationResultCache");
    private readonly CacheItemPolicy Policy = new CacheItemPolicy { SlidingExpiration = new TimeSpan(0, 10, 0), Priority = CacheItemPriority.Default };


    public void Insert(Implementation impl, VerificationResult result)
    {
      Contract.Requires(impl != null);
      Contract.Requires(result != null);

      Cache.Set(impl.Id, result, Policy);
    }


    public VerificationResult Lookup(Implementation impl, out int priority)
    {
      Contract.Requires(impl != null);

      var result = Cache.Get(impl.Id) as VerificationResult;
      if (result == null)
      {
        priority = Priority.HIGH;
      }
      else if (result.Checksum != impl.Checksum)
      {
        priority = Priority.MEDIUM;
      }
      else if (impl.DependencyChecksum == null || result.DependeciesChecksum != impl.DependencyChecksum)
      {
        priority = Priority.LOW;
      }
      else if (result.Outcome == ConditionGeneration.Outcome.TimedOut && CommandLineOptions.Clo.RunDiagnosticsOnTimeout)
      {
        priority = Priority.MEDIUM;
      }
      else
      {
        priority = Priority.SKIP;
      }
      return result;
    }


    public void Clear()
    {
      Cache.Trim(100);
    }


    public void RemoveMatchingKeys(Regex keyRegexp)
    {
      Contract.Requires(keyRegexp != null);

      foreach (var kv in Cache)
      {
        if (keyRegexp.IsMatch(kv.Key))
        {
          Cache.Remove(kv.Key);
        }
      }
    }


    public int VerificationPriority(Implementation impl)
    {
      Contract.Requires(impl != null);

      int priority;
      Lookup(impl, out priority);
      return priority;
    }
  }

}
