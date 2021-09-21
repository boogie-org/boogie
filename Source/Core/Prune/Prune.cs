using System;
using System.Linq;
using System.Collections.Generic;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{

  public static class Util
  {
    public static V GetOrCreate<K, V>(this IDictionary<K, V> dictionary, K key, Func<V> createValue)
    {
      if (dictionary.TryGetValue(key, out var result)) {
        return result;
      }

      result = createValue();
      dictionary[key] = result;
      return result;
    }
    
    public static uint SafeMult(uint a, uint b) {
      uint result = UInt32.MaxValue;
      try {
        checked {
          result = a * b;
        }
      } catch (OverflowException) { }

      return result;
    }
  }
  
  public class Prune {
    private static bool ExcludeDep(Declaration d)
    {
      return d.Attributes != null &&
              QKeyValue.FindBoolAttribute(d.Attributes, "exclude_dep");
    }

    public static Dictionary<object, List<object>> InitializeEdges(Program program)
    {
      if (!CommandLineOptions.Clo.PruneFunctionsAndAxioms)
      {
        return null;
      }
      var nodes = program.Axioms.Select(ax => (DependencyEvaluator)new AxiomVisitor(ax)).ToList();
      nodes.ForEach(axv => ((AxiomVisitor)axv).Visit(axv.node));
      var functionNodes = program.Functions.Select(f => (DependencyEvaluator)new FunctionVisitor(f)).ToList();
      functionNodes.ForEach(fv => ((FunctionVisitor)fv).Visit(fv.node));
      nodes.AddRange(functionNodes);
      nodes.ForEach(u => u.incoming = u.incoming.Where(i => !ExcludeDep(i)).ToHashSet());
      nodes.ForEach(u => u.outgoing = u.outgoing.Where(i => !ExcludeDep(i)).ToHashSet());

      var edges = new Dictionary<object, List<object>>();
      foreach (var node in nodes) {
        foreach (var incomingSingle in node.incoming) {
          var targets = edges.GetOrCreate(incomingSingle, () => new());
          targets.Add(node.node);
        }
        foreach (var incomingTuple in node.incomingTuples) {
          foreach (var mergeIncoming in incomingTuple) {
            var mergeIncomingTargets = edges.GetOrCreate(mergeIncoming, () => new());
            mergeIncomingTargets.Add(incomingTuple);
          }
          var mergeTargets = edges.GetOrCreate(incomingTuple, () => new());
          mergeTargets.Add(node.node);
        }
        foreach (var outgoingSingle in node.outgoing) {
          var targets = edges.GetOrCreate(node.node, () => new());
          targets.Add(outgoingSingle);
        }
      }

      return edges;
    }

    public static Variable GetWhereVariable(Cmd c) {
      if (c is AssumeCmd ac)
      {
        var attr = QKeyValue.FindAttribute(ac.Attributes, qkv => qkv.Key == "where" && qkv.Params.Count == 1);
        if (attr != null)
        {
          var ie = (IdentifierExpr) attr.Params[0];
          return ie.Decl;
        }
      }
      return null;
    }

    public static void TrimWhereAssumes(List<Block> blocks, HashSet<Variable> liveVars) {
      var whereAssumes = new Dictionary<Variable, AssumeVisitor> ();
      foreach (var blk in blocks)
      {
        foreach(var cmd in blk.Cmds)
        {
          var v = GetWhereVariable(cmd);
          if (v != null)
          {
            var ac = cmd as AssumeCmd;
            whereAssumes[v] = new AssumeVisitor(ac);
            whereAssumes[v].Visit(ac);
          }
        }
      }

      var todo = new Stack<Variable> (liveVars);
      while (todo.Any())
      {
        var t = todo.Pop();
        if (whereAssumes.Keys.Contains(t)) {
          whereAssumes[t].RelVars.Where(v => !liveVars.Contains(v)).ToList().ForEach(v => todo.Push(v));
        }
        liveVars.Add(t);
      }

      bool DeadWhereAssumption(Cmd c)
      {
        var v = GetWhereVariable(c);
        return v != null && !liveVars.Contains(v);
      }

      blocks.ForEach(blk => blk.Cmds = blk.Cmds.Where(c => !DeadWhereAssumption(c)).ToList());
    }

    public static IEnumerable<Declaration> PruneDecl(Program p, List<Block> blocks)
    {
      if (p.edges == null || blocks == null || !CommandLineOptions.Clo.PruneFunctionsAndAxioms)
      {
        return p.TopLevelDeclarations;
      }

      // an implementation only has outgoing edges.
      BlocksVisitor bnode = new BlocksVisitor(blocks);
      bnode.Blocks.ForEach(blk => bnode.Visit(blk));
      TrimWhereAssumes(blocks, bnode.RelVars);
      var implHooks = bnode.outgoing;

      var reachableDeclarations = GraphAlgorithms.FindReachableNodesInGraphWithMergeNodes(p.edges, implHooks).ToHashSet();
      var result = p.TopLevelDeclarations.Where(d => d is not Constant && d is not Axiom && d is not Function || reachableDeclarations.Contains(d));
      return result;
    }
  }
}