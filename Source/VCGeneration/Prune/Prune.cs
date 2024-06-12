using System.Linq;
using System.Collections.Generic;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  
  public class Prune {

    public static Dictionary<object, List<object>> ComputeDeclarationDependencies(VCGenOptions options, Program program)
    {
      if (options.Prune == PruneMode.Not)
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
      if (program.DeclarationDependencies == null || blocks == null || options.Prune == PruneMode.Not)
      {
        return program.TopLevelDeclarations;
      }

      PruneBlocksVisitor blocksVisitor = new PruneBlocksVisitor();
      foreach (var block in blocks)
      {
        blocksVisitor.Visit(block);
      }

      var revealedOutgoing = options.Prune == PruneMode.AllRevealed
        ? blocksVisitor.Outgoing
        : blocksVisitor.Outgoing.Where(d =>
          DeclarationFilter(d)); 

      var keepRoots = program.TopLevelDeclarations.Where(d => QKeyValue.FindBoolAttribute(d.Attributes, "keep"));
      var reachableDeclarations = GraphAlgorithms.FindReachableNodesInGraphWithMergeNodes(program.DeclarationDependencies, 
        revealedOutgoing.Concat(keepRoots).ToHashSet(),
        node => node is not Function function || blocksVisitor.RevealedFunctions.Contains(function))
        .OfType<Declaration>().Where(d => DeclarationFilter(d)).ToHashSet();
      return program.TopLevelDeclarations.Where(d => 
        d is not Constant && d is not Axiom && d is not Function || reachableDeclarations.Contains(d));

      bool DeclarationFilter(Declaration d)
      {
        return d is not Function function || blocksVisitor.RevealedFunctions.Contains(function);
      }
    }
  }
}