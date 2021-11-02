using System.Linq;
using System.Collections.Generic;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class Prune {
    private static bool ExcludeDep(Declaration d)
    {
      return d.Attributes != null &&
              QKeyValue.FindBoolAttribute(d.Attributes, "exclude_dep");
    }

    public static Dictionary<object, List<object>> ComputeDeclarationDependencies(Program program)
    {
      if (!CommandLineOptions.Clo.PruneFunctionsAndAxioms)
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

    /*
     * Global variables, type constructor declarations, type synonyms, procedures and implementations are not pruned, but none of them produce solver commands.
     * See Checker.Setup for more information.
     * Data type constructor declarations are not pruned and they do affect VC generation.
     */
    public static IEnumerable<Declaration> GetLiveDeclarations(Program program, List<Block> blocks)
    {
      if (program.DeclarationDependencies == null || blocks == null || !CommandLineOptions.Clo.PruneFunctionsAndAxioms)
      {
        return program.TopLevelDeclarations;
      }

      BlocksVisitor blocksNode = new BlocksVisitor(blocks);
      blocksNode.Blocks.ForEach(blk => blocksNode.Visit(blk));
      TrimWhereAssumes(blocks, blocksNode.RelVars);

      // an implementation only has outgoing edges.
      var reachableDeclarations = GraphAlgorithms.FindReachableNodesInGraphWithMergeNodes(program.DeclarationDependencies, blocksNode.outgoing).ToHashSet();
      var result = program.TopLevelDeclarations.Where(d => d is not Constant && d is not Axiom && d is not Function || reachableDeclarations.Contains(d)).ToList();
      var removedDeclarations = program.TopLevelDeclarations.Except(result).ToList();
      return result;
    }
  }
}