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
    public int ImplementationCount { get; internal set; }
  }


  class CachedVerificationResultInjectorStatistics
  {
    ConcurrentDictionary<string, CachedVerificationResultInjectorRun> runs = new ConcurrentDictionary<string, CachedVerificationResultInjectorRun>();

    public bool AddRun(string requestId, CachedVerificationResultInjectorRun run)
    {
      return runs.TryAdd(requestId, run);
    }

    public string Output(bool printTime = false)
    {
      var wr = new StringWriter();
      wr.WriteLine("");
      wr.WriteLine("Cached verification result injector statistics:");
      if (printTime)
      {
        wr.WriteLine("Request ID, Time, Implementations (ms)");
      }
      else
      {
        wr.WriteLine("Request ID, Implementations (ms)");
      }
      foreach (var kv in runs)
      {
        if (printTime)
        {
          wr.WriteLine("{0}, {1}, {2}", kv.Key, kv.Value.End.Subtract(kv.Value.Start).TotalMilliseconds, kv.Value.ImplementationCount);
        }
        else
        {
          wr.WriteLine("{0}, {1}", kv.Key, kv.Value.ImplementationCount);
        }
      }
      return wr.ToString();
    }
  }


  class CachedVerificationResultInjector : StandardVisitor
  {
    readonly IEnumerable<Implementation> Implementations;
    readonly Program Program;
    // TODO(wuestholz): We should probably increase the threshold to something like 2 seconds.
    static readonly double TimeThreshold = 0.0;
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

    public static void Inject(Program program, IEnumerable<Implementation> implementations, string requestId)
    {
      var eai = new CachedVerificationResultInjector(program, implementations);

      var run = new CachedVerificationResultInjectorRun { Start = DateTime.UtcNow };
      foreach (var impl in implementations)
      {
        int priority;
        var vr = ExecutionEngine.Cache.Lookup(impl, out priority);
        if (vr != null && priority == Priority.LOW)
        {
          if (TimeThreshold < vr.End.Subtract(vr.Start).TotalMilliseconds)
          {
            if (vr.Errors != null)
            {
              impl.ErrorsInCachedSnapshot = vr.Errors.ToList<object>();
            }
            else if (vr.Outcome == ConditionGeneration.Outcome.Correct)
            {
              impl.ErrorsInCachedSnapshot = new List<object>();
            }
            if (vr.ProgramId != null)
            {
              var p = ExecutionEngine.CachedProgram(vr.ProgramId);
              if (p != null)
              {
                eai.Inject(impl, p);
                run.ImplementationCount++;
              }
            }
          }
        }
      }
      run.End = DateTime.UtcNow;
      Statistics.AddRun(requestId, run);
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

      string result = null;
      using (var ms = new System.IO.MemoryStream())
      using (var wr = new System.IO.BinaryWriter(ms))
      {
        foreach (var dep in procDeps)
        {
          wr.Write(Encoding.UTF8.GetBytes(dep.Checksum));
        }
        foreach (var dep in funcDeps)
        {
          wr.Write(Encoding.UTF8.GetBytes(dep.Checksum));
        }
        wr.Flush();
        wr.BaseStream.Position = 0;
        var md5 = System.Security.Cryptography.MD5.Create();
        var hashedData = md5.ComputeHash(wr.BaseStream);
        result = BitConverter.ToString(hashedData);
      }
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
    public static readonly int LOW = 1;             // the same snapshot has been verified before, but a callee has changed
    public static readonly int MEDIUM = 2;          // old snapshot has been verified before
    public static readonly int HIGH = 3;            // has been never verified before
    public static readonly int SKIP = int.MaxValue; // highest priority to get them done as soon as possible
  }


  public class VerificationResultCache
  {
    private readonly MemoryCache Cache = new MemoryCache("VerificationResultCache");
    private readonly CacheItemPolicy Policy = new CacheItemPolicy { SlidingExpiration = new TimeSpan(0, 10, 0) };


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
      else if (impl.DependenciesChecksum == null || result.DependeciesChecksum != impl.DependenciesChecksum)
      {
        priority = Priority.LOW;
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
