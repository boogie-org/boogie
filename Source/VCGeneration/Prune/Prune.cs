using System;
using System.Linq;
using System.Collections.Generic;
using Microsoft.Boogie.GraphUtil;
using VC;

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
        foreach (var outgoingSingle in node.outgoing) {
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
        return program.Declarations;
      }

      BlocksVisitor blocksNode = new BlocksVisitor(blocks);
      blocksNode.Blocks.ForEach(blk => blocksNode.Visit(blk));

      var keepRoots = program.Declarations.Where(d => QKeyValue.FindBoolAttribute(d.Attributes, "keep"));
      var reachableDeclarations = GraphAlgorithms.FindReachableNodesInGraphWithMergeNodes(program.DeclarationDependencies, blocksNode.outgoing.Concat(keepRoots).ToHashSet()).ToHashSet();
      return program.Declarations.Where(d =>
        !IsPrunableType(d) || reachableDeclarations.Contains(d));
    }

    private static bool IsPrunableType(Declaration d)
    {
      return d is Constant || d is Axiom || d is Function;
    }

    public static void PrintTopLevelDeclarationsForPruning(Split split, string suffix)
    {
      if (!split.Options.Prune || split.Options.PrintPrunedFile == null)
      {
        return;
      }

      using var writer = new TokenTextWriter(
        $"{split.Options.PrintPrunedFile}-{suffix}-{Util.EscapeFilename(split.Implementation.Name)}", false,
        split.Options.PrettyPrint, split.Options);

      (split.TopLevelDeclarations ?? split.Parent.Program.TopLevelDeclarations).Where(IsPrunableType).ToList().Emit(writer);
    }
  }
}