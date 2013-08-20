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

      foreach (var param in node.InParams)
      {
        if (param.TypedIdent != null && param.TypedIdent.WhereExpr != null)
        {
          param.TypedIdent.WhereExpr = VisitExpr(param.TypedIdent.WhereExpr);
        }
      }

      return base.VisitProcedure(node);
    }

    public override Function VisitFunction(Function node)
    {
      dependencies.Add(node);

      if (node.DefinitionAxiom != null)
      {
        node.DefinitionAxiom = VisitAxiom(node.DefinitionAxiom);
      }

      return base.VisitFunction(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      var visited = dependencies.Contains(node.Proc);
      if (!visited)
      {
        node.Proc = VisitProcedure(node.Proc);
      }

      return base.VisitCallCmd(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      var funCall = node.Fun as FunctionCall;
      if (funCall != null)
      {
        var visited = dependencies.Contains(funCall.Func);
        if (!visited)
        {
          funCall.Func = VisitFunction(funCall.Func);
        }
      }

      return base.VisitNAryExpr(node);
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
      return VerificationPriority(impl) < int.MaxValue;
    }


    public int VerificationPriority(Implementation impl)
    {
      if (!Cache.ContainsKey(impl.Id))
      {
        return 3;  // high priority (has been never verified before)
      }
      else if (Cache[impl.Id].Checksum != impl.Checksum)
      {
        return 2;  // medium priority (old snapshot has been verified before)
      }
      else if (impl.DependenciesChecksum == null || Cache[impl.Id].DependeciesChecksum != impl.DependenciesChecksum)
      {
        return 1;  // low priority (the same snapshot has been verified before, but a callee has changed)
      }
      else
      {
        return int.MaxValue;  // skip verification (highest priority to get them done as soon as possible)
      }
    }
  }

}
