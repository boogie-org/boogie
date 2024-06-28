#nullable enable
using System.Linq;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Data;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  
  public class Prune {

    public static Dictionary<object, List<object>> ComputeDeclarationDependencies(VCGenOptions options, Program program)
    {
      if (!options.Prune)
      {
        return null;
      }
      var axiomNodes = program.Axioms.Select(AxiomVisitor.GetDependencies);
      var functionNodes = program.Functions.Select(FunctionVisitor.GetDependencies);
      var constantNodes = program.Constants.Select(ConstantVisitor.GetDependencies);
      var nodes = axiomNodes.Concat(functionNodes).Concat(constantNodes).ToList();

      var edges = new Dictionary<object, List<object>>();
      foreach (var node in nodes) {
        foreach (var incomingTuple in node.incomingSets) {
          object source;
          if (incomingTuple.Length == 0) {
            continue;
          }

          if (incomingTuple.Length == 1) {
            source = incomingTuple.First();
          } else {
            foreach (var mergeIncoming in incomingTuple) {
              var mergeIncomingTargets = edges.GetOrCreate(mergeIncoming, () => new());
              mergeIncomingTargets.Add(incomingTuple);
            }

            source = incomingTuple;
          }

          var targets = edges.GetOrCreate(source, () => new());
          targets.Add(node.declaration);
        }
        foreach (var outgoingSingle in node.Outgoing) {
          var targets = edges.GetOrCreate(node.declaration, () => new());
          targets.Add(outgoingSingle);
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

      var graph = new Graph<Cmd>();
      foreach (var block in blocks) {
        foreach (var predecessor in block.Predecessors) {
          graph.AddEdge(predecessor.Cmds.Last(), block.Cmds[0]);
        }

        for (var index = 0; index < block.Cmds.Count - 1; index++) {
          var command = block.Cmds[index];
          var nextCommand = block.Cmds[index];
          graph.AddEdge(command, nextCommand);
        }
      }

      var revealedAnalysis = new RevealedAnalysis(graph.Nodes,
        cmd => graph.Successors(cmd),
        cmd => graph.Predecessors(cmd));
      revealedAnalysis.Run();

      var merged = revealedAnalysis.States.Values.Select(s => s.Peek()).Aggregate(RevealedAnalysis.MergeStates);
      
      /* hide P {
       *   hide * {
       *
       *   }
       *   P hidden.
       * }
       *
       * Only a single endresult
       *
       * Do we need to insert the reverse operations? It seems like it.
       * A result per command.
       *
       * Als we --isolate-assertions en --isolate-paths forceren wordt het simpeler
       *
       * We willen de revealed set per assertion.
       * 
       */

      PruneBlocksVisitor blocksVisitor = new PruneBlocksVisitor();
      foreach (var block in blocks)
      {
        blocksVisitor.Visit(block);
      }

      var keepRoots = program.TopLevelDeclarations.Where(d => QKeyValue.FindBoolAttribute(d.Attributes, "keep"));
      var reachableDeclarations = GraphAlgorithms.FindReachableNodesInGraphWithMergeNodes(program.DeclarationDependencies, 
        blocksVisitor.Outgoing.Concat(keepRoots).ToHashSet(), TraverseDeclaration).ToHashSet();
      return program.TopLevelDeclarations.Where(d => 
        d is not Constant && d is not Axiom && d is not Function || reachableDeclarations.Contains(d));

      bool TraverseDeclaration(object parent, object child)
      {
        var result = parent is not Function function || child is not Axiom axiom || merged.IsRevealed(function)
          || !axiom.CanHide;
        return result;
      }
    }
  }
}