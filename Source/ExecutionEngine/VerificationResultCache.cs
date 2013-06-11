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

  class DependencyCollector : StandardVisitor
  {
    private HashSet<DeclWithFormals> dependencies;

    public DependencyCollector()
    {
      dependencies = new HashSet<DeclWithFormals>();
    }

    public static void Collect(Absy node, out List<DeclWithFormals> dependencies)
    {
      var dc = new DependencyCollector();
      dc.Visit(node);
      dependencies = dc.dependencies.ToList();
    }

    public static string DependenciesChecksum(Implementation impl)
    {
      List<DeclWithFormals> deps;
      DependencyCollector.Collect(impl, out deps);
      if (deps.Any(dep => dep.Checksum == null))
      {
        return null;
      }

      var md5 = System.Security.Cryptography.MD5.Create();
      var data = Encoding.UTF8.GetBytes(deps.MapConcat(dep => dep.Checksum, ""));
      var hashedData = md5.ComputeHash(data);
      return BitConverter.ToString(hashedData);
    }

    public override Procedure VisitProcedure(Procedure node)
    {
      dependencies.Add(node);

      return base.VisitProcedure(node);
    }

    public override Function VisitFunction(Function node)
    {
      dependencies.Add(node);

      return base.VisitFunction(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      var result = base.VisitCallCmd(node);

      var visited = dependencies.Contains(node.Proc);
      if (!visited)
      {
        VisitProcedure(node.Proc);
      }

      return result;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      var result = base.VisitNAryExpr(node);

      var funCall = node.Fun as FunctionCall;
      if (funCall != null)
      {
        var visited = dependencies.Contains(funCall.Func);
        if (!visited)
        {
          VisitFunction(funCall.Func);
          if (funCall.Func.DefinitionAxiom != null)
          {
            VisitAxiom(funCall.Func.DefinitionAxiom);
          }
        }
      }

      return result;
    }
  }


  public class VerificationResult
  {
    public readonly string Checksum;
    public readonly string DependeciesChecksum;
    public readonly string RequestId;
    public readonly ConditionGeneration.Outcome Outcome;
    public readonly List<Counterexample> Errors;

    public VerificationResult(string requestId, string checksum, string depsChecksum, ConditionGeneration.Outcome outcome, List<Counterexample> errors)
    {
      Checksum = checksum;
      DependeciesChecksum = depsChecksum;
      Outcome = outcome;
      Errors = errors;
      RequestId = requestId;
    }
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
      if (!Cache.ContainsKey(impl.Id)
          || Cache[impl.Id].Checksum != impl.Checksum)
      {
        return true;
      }

      var depsChecksum = DependencyCollector.DependenciesChecksum(impl);
      return depsChecksum == null || Cache[impl.Id].DependeciesChecksum != depsChecksum;
    }

  }

}
