using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using VC;

namespace Microsoft.Boogie
{

  class CachedVerificationResultInjector : StandardVisitor
  {
    readonly IEnumerable<Implementation> Implementations;
    readonly Program Program;
    Program programInCachedSnapshot;
    Implementation currentImplementation;
    int assumptionVariableCount;
    int temporaryVariableCount;

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

    protected CachedVerificationResultInjector(Program program, IEnumerable<Implementation> implementations)
    {
      Implementations = implementations;
      Program = program;
    }

    public Implementation Inject(Implementation implementation, Program programInCachedSnapshot)
    {
      Contract.Requires(implementation != null && programInCachedSnapshot != null);

      this.programInCachedSnapshot = programInCachedSnapshot;
      assumptionVariableCount = 0;
      temporaryVariableCount = 0;
      currentImplementation = implementation;
      var result = VisitImplementation(implementation);
      currentImplementation = null;
      this.programInCachedSnapshot = null;
      return result;
    }

    public static void Inject(Program program, IEnumerable<Implementation> implementations)
    {
      var eai = new CachedVerificationResultInjector(program, implementations);

      foreach (var impl in implementations)
      {
        if (ExecutionEngine.Cache.VerificationPriority(impl) == Priority.LOW)
        {
          var vr = ExecutionEngine.Cache.Lookup(impl.Id);
          // TODO(wuestholz): We should probably increase the threshold to something like 2 seconds.
          if (vr != null && 0.0 < vr.End.Subtract(vr.Start).TotalMilliseconds)
          {
            if (vr.Errors != null)
            {
              impl.ErrorsInCachedSnapshot = vr.Errors.ToList<object>();
            }
            else if (vr.Outcome == ConditionGeneration.Outcome.Correct)
            {
              impl.ErrorsInCachedSnapshot = new List<object>();
            }
            var p = vr.Program;
            if (p != null)
            {
              eai.Inject(impl, p);
            }
          }
        }
      }
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      var result = base.VisitCallCmd(node);

      // TODO(wuestholz): Maybe we should speed up this lookup.
      var oldProc = programInCachedSnapshot.TopLevelDeclarations.OfType<Procedure>().FirstOrDefault(p => p.Name == node.Proc.Name);
      if (oldProc != null
          && DependencyCollector.DependenciesChecksum(oldProc) != DependencyCollector.DependenciesChecksum(node.Proc)
          && DependencyCollector.AllFunctionDependenciesAreDefinedAndUnchanged(oldProc, Program))
      {
        var lv = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, string.Format("a##post##{0}", FreshAssumptionVariableName), Type.Bool),
          new QKeyValue(Token.NoToken, "assumption", new List<object>(), null));
        currentImplementation.InjectAssumptionVariable(lv);

        var before = new List<Cmd>();
        if (currentImplementation.NoErrorsInCachedSnapshot
            && oldProc.Requires.Any())
        {
          var pre = node.Precondition(oldProc, Program);
          var assume = new AssumeCmd(Token.NoToken, pre, new QKeyValue(Token.NoToken, "precondition_previous_snapshot", new List<object>(), null));
          before.Add(assume);
        }
        else if (currentImplementation.AnyErrorsInCachedSnapshot)
        {
          // TODO(wuestholz): Add an assume statement if the precondition was verified in the previous snapshot.
        }

        var post = node.Postcondition(oldProc, Program);
        var mods = node.UnmodifiedBefore(oldProc);
        foreach (var m in mods)
        {
          var mPre = new LocalVariable(Token.NoToken,
            new TypedIdent(Token.NoToken, string.Format("{0}##pre##{1}", m.Name, FreshTemporaryVariableName), m.Type));
          before.Add(new AssignCmd(Token.NoToken,
                       new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, mPre)) },
                       new List<Expr> { new IdentifierExpr(Token.NoToken, m.Decl) }));
          var eq = LiteralExpr.Eq(new IdentifierExpr(Token.NoToken, mPre), new IdentifierExpr(Token.NoToken, m.Decl));
          post = LiteralExpr.And(post, eq);
        }
        var lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, lv));
        var rhs = LiteralExpr.And(new IdentifierExpr(Token.NoToken, lv), post);
        var assumed = new AssignCmd(Token.NoToken, new List<AssignLhs> { lhs }, new List<Expr> { rhs });

        node.ExtendDesugaring(before, new List<Cmd> { assumed });
      }

      return result;
    }
  }


  class DependencyCollector : ReadOnlyVisitor
  {
    private HashSet<Procedure> procedureDependencies;
    private HashSet<Function> functionDependencies;
    private bool allDependenciesHaveChecksum = true;

    public DependencyCollector()
    {
      procedureDependencies = new HashSet<Procedure>();
      functionDependencies = new HashSet<Function>();
    }

    static bool Collect(Absy node, out ISet<Procedure> procedureDependencies, out ISet<Function> functionDependencies)
    {
      var dc = new DependencyCollector();
      dc.Visit(node);
      procedureDependencies = dc.procedureDependencies;
      functionDependencies = dc.functionDependencies;
      return dc.allDependenciesHaveChecksum;
    }

    static bool Collect(Procedure proc, out ISet<Function> functionDependencies)
    {
      var dc = new DependencyCollector();
      dc.Visit(proc);
      functionDependencies = dc.functionDependencies;
      return dc.allDependenciesHaveChecksum;
    }

    public static bool AllFunctionDependenciesAreDefinedAndUnchanged(Procedure oldProc, Program newProg)
    {
      Contract.Requires(oldProc != null && newProg != null);

      ISet<Function> oldDeps;
      if (!Collect(oldProc, out oldDeps))
      {
        return false;
      }
      // TODO(wuestholz): Maybe we should speed up this lookup.
      var funcs = newProg.TopLevelDeclarations.OfType<Function>();
      return oldDeps.All(dep => funcs.Any(f => f.Name == dep.Name && f.Checksum == dep.Checksum));
    }

    public static string DependenciesChecksum(DeclWithFormals decl)
    {
      if (decl.DependenciesChecksum != null)
      {
        return decl.DependenciesChecksum;
      }

      ISet<Procedure> procDeps;
      ISet<Function> funcDeps;
      if (!DependencyCollector.Collect(decl, out procDeps, out funcDeps))
      {
        return null;
      }

      var md5 = System.Security.Cryptography.MD5.Create();
      var procChecksums = procDeps.MapConcat(dep => dep.Checksum, "");
      var funcChecksums = funcDeps.MapConcat(dep => dep.Checksum, "");
      var data = Encoding.UTF8.GetBytes(procChecksums + funcChecksums);
      var hashedData = md5.ComputeHash(data);
      var result = BitConverter.ToString(hashedData);
      decl.DependenciesChecksum = result;
      return result;
    }

    public override Procedure VisitProcedure(Procedure node)
    {
      procedureDependencies.Add(node);
      allDependenciesHaveChecksum &= node.Checksum != null;

      foreach (var param in node.InParams)
      {
        if (param.TypedIdent != null && param.TypedIdent.WhereExpr != null)
        {
          VisitExpr(param.TypedIdent.WhereExpr);
        }
      }

      return base.VisitProcedure(node);
    }

    public override Function VisitFunction(Function node)
    {
      functionDependencies.Add(node);
      allDependenciesHaveChecksum &= node.Checksum != null;

      if (node.DefinitionAxiom != null)
      {
        VisitAxiom(node.DefinitionAxiom);
      }

      return base.VisitFunction(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      var visited = procedureDependencies.Contains(node.Proc);
      if (!visited)
      {
        VisitProcedure(node.Proc);
      }

      return base.VisitCallCmd(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      var funCall = node.Fun as FunctionCall;
      if (funCall != null)
      {
        var visited = functionDependencies.Contains(funCall.Func);
        if (!visited)
        {
          VisitFunction(funCall.Func);
        }
      }

      return base.VisitNAryExpr(node);
    }
  }


  static internal class Priority
  {
    public static int LOW = 1;
    public static int MEDIUM = 2;
    public static int HIGH = 3;
    public static int SKIP = int.MaxValue;
  }


  public class VerificationResultCache
  {
    private readonly ConcurrentDictionary<string, VerificationResult> Cache = new ConcurrentDictionary<string, VerificationResult>();


    public void Insert(string key, VerificationResult result)
    {
      Contract.Requires(key != null);
      Contract.Requires(result != null);

      Cache[key] = result;
    }


    public VerificationResult Lookup(string key)
    {
      VerificationResult result;
      var success = Cache.TryGetValue(key, out result);
      return success ? result : null;
    }


    public VerificationResult Lookup(Implementation impl)
    {
      if (!NeedsToBeVerified(impl))
      {
        return Lookup(impl.Id);
      }
      else
      {
        return null;
      }
    }


    public void Clear()
    {
      Cache.Clear();
    }


    public void RemoveMatchingKeys(Regex keyRegexp)
    {
      foreach (var kv in Cache)
      {
        if (keyRegexp.IsMatch(kv.Key))
        {
          VerificationResult res;
          Cache.TryRemove(kv.Key, out res);
        }
      }
    }


    public bool NeedsToBeVerified(Implementation impl)
    {
      return VerificationPriority(impl) < Priority.SKIP;
    }


    public int VerificationPriority(Implementation impl)
    {
      if (!Cache.ContainsKey(impl.Id))
      {
        return Priority.HIGH;  // high priority (has been never verified before)
      }
      else if (Cache[impl.Id].Checksum != impl.Checksum)
      {
        return Priority.MEDIUM;  // medium priority (old snapshot has been verified before)
      }
      else if (impl.DependenciesChecksum == null || Cache[impl.Id].DependeciesChecksum != impl.DependenciesChecksum)
      {
        return Priority.LOW;  // low priority (the same snapshot has been verified before, but a callee has changed)
      }
      else
      {
        return Priority.SKIP;  // skip verification (highest priority to get them done as soon as possible)
      }
    }
  }

}
