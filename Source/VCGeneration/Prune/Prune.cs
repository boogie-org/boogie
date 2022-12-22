using System;
using System.Linq;
using System.Collections.Generic;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class Prune {

    public static Dictionary<HashSet<Declaration>, List<HashSet<Declaration>>> ComputeDeclarationDependencies(VCGenOptions options, Program program)
    {
      if (!options.Prune)
      {
        return null;
      }
      var axiomDependencyEvaluators = program.Axioms.Select(AxiomVisitor.GetDependencies);
      var functionDependencyEvaluators = program.Functions.Select(FunctionVisitor.GetDependencies);
      var constantDependencyEvaluators = program.Constants.Select(ConstantVisitor.GetDependencies);
      var allDependencyEvaluators = axiomDependencyEvaluators.Concat(functionDependencyEvaluators).Concat(constantDependencyEvaluators).ToList();

      var edges = new Dictionary<HashSet<Declaration>, List<HashSet<Declaration>>>(new HashSetComparer<Declaration>());
      foreach (var dependencyEvaluator in allDependencyEvaluators) {
        foreach (var incomingTuple in dependencyEvaluator.incomingSets.Where(x => x.Length > 0)) {
          var source = new HashSet<Declaration>(incomingTuple);
          var targets = edges.GetOrCreate(source, () => new());
          targets.Add(new HashSet<Declaration> { dependencyEvaluator.declaration });
        }
        foreach (var outgoingSingle in dependencyEvaluator.outgoing)
        {
          var source = new HashSet<Declaration> { dependencyEvaluator.declaration };
          var target = new HashSet<Declaration> { outgoingSingle };
          var targets = edges.GetOrCreate(source, () => new());
          targets.Add(target);
        }
      }
      return edges;
    }

    /*
     * Global variables, type constructor declarations, type synonyms, procedures and implementations are not pruned, but none of them produce solver commands.
     * See Checker.Setup for more information.
     * Data type constructor declarations are not pruned and they do affect VC generation.
     */
    public static IEnumerable<Declaration> GetLiveDeclarations(VCGenOptions options, Program program, List<Block> blocks)
    {
      if (program.DeclarationDependencies == null || blocks == null || !options.Prune)
      {
        return program.TopLevelDeclarations;
      }

      BlocksVisitor blocksNode = new BlocksVisitor(blocks);
      blocksNode.Blocks.ForEach(blk => blocksNode.Visit(blk));

      var keepRoots = program.TopLevelDeclarations.Where(d => QKeyValue.FindBoolAttribute(d.Attributes, "keep"));
      var reachableDeclarations = FindReachableNodesInGraphWithMergeNodes(program.DeclarationDependencies, blocksNode.outgoing.Concat(keepRoots).ToHashSet()).ToHashSet();
      return program.TopLevelDeclarations.Where(d => 
        d is not Constant && d is not Axiom && d is not Function || reachableDeclarations.Contains(d));
    }

    private static IEnumerable<Declaration> FindReachableNodesInGraphWithMergeNodes(Dictionary<HashSet<Declaration>, List<HashSet<Declaration>>> edges, IEnumerable<Declaration> roots)
    {
      var todo = new Stack<HashSet<Declaration>>(roots.Select(root => new HashSet<Declaration> { root }));
      var visitedNodes = new HashSet<HashSet<Declaration>>(new HashSetComparer<Declaration>());
      var visitedDecls = new HashSet<Declaration>();
      while (todo.Any())
      {
        var node = todo.Pop();
        if (!visitedNodes.Contains(node))
        {
          visitedNodes.Add(node);
          visitedDecls.UnionWith(node);
          var outgoing = edges.GetValueOrDefault(node) ?? new List<HashSet<Declaration>>();
          foreach (var x in outgoing)
          {
            todo.Push(x);
          }
        }
        if (!todo.Any())
        {
          // add more work for nodes whose outgoing edges may be enabled now
          todo = new Stack<HashSet<Declaration>>(edges.Keys.Where(x =>
            !visitedNodes.Contains(x) && visitedDecls.IsSupersetOf(x)));
        }
      }
      return visitedDecls;
    }
  }
}