using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class Prune {
    private static bool ExcludeDep(Declaration d)
    {
      return d.Attributes != null &&
              QKeyValue.FindBoolAttribute(d.Attributes, "exclude_dep");
    }

    public static Dictionary<DependencyEvaluator, List<DependencyEvaluator>> InitializeEdges(Program program)
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
      nodes.ForEach(u => u.incoming = u.incoming.Where(i => u.node == i || !ExcludeDep(i)).ToHashSet());
      nodes.ForEach(u => u.outgoing = u.outgoing.Where(i => !ExcludeDep(i)).ToHashSet());
      var edges = new Dictionary<DependencyEvaluator, List<DependencyEvaluator>>();
      
      // TODO remove square complexity.
      nodes.ForEach(u => edges[u] = nodes.Where(v => DependencyEvaluator.Depends(u, v)).ToList());
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

      var edges = p.edges;
      // an implementation only has outgoing edges.
      BlocksVisitor bnode = new BlocksVisitor(blocks);
      bnode.Blocks.ForEach(blk => bnode.Visit(blk));
      TrimWhereAssumes(blocks, bnode.RelVars);
      var implHooks = edges.Keys.Where(m => DependencyEvaluator.Depends(bnode, m));

      var reachableDeclarations = ComputeReachability(p, implHooks).ToHashSet();
      var result = p.TopLevelDeclarations.Where(d => d is not Constant && d is not Axiom && d is not Function || reachableDeclarations.Contains(d));
      return result;
    }
    
    static IEnumerable<Declaration> ComputeReachability(Program p, IEnumerable<DependencyEvaluator> implHooks)
    {
      var edges = p.edges;
      var todo = new Stack<DependencyEvaluator>(implHooks);
      var visited = new HashSet<DependencyEvaluator>();
      while(todo.Any())
      {
        var d = todo.Pop();
        foreach (var x in edges[d].Where(t => !visited.Contains(t)))
        {
          todo.Push(x);
        }
        visited.Add(d);
      }
      return visited.Select(a => a.node);
    }
  }
}