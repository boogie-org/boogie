using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using VCGeneration.Prune;

namespace VCGeneration;

public static class BlockTransformations {
  public static void Optimize(List<Block> blocks, Program program) {
    foreach (var block in blocks) {
      // TODO somehow this had 0 effect on my customer codebase
      OldBlockTransformations.StopControlFlowAtAssumeFalse(block);
    }
    PruneAssumptions(program, blocks);
    OptimizeBlocks(blocks);
  }

  public static void OptimizeBlocks(List<Block> blocks) {
    DeleteUselessBlocks(blocks);
    MergeOneToOneBlocks(blocks);
  }

  private static void DeleteUselessBlocks(List<Block> blocks) {
    var toVisit = new HashSet<Block>();
    var removed = new HashSet<Block>();
    foreach (var block in blocks) {
      toVisit.Add(block);
    }
    while(toVisit.Count > 0) {
      var block = toVisit.First();
      toVisit.Remove(block);
      if (removed.Contains(block)) {
        continue;
      }
      if (block.Cmds.Any()) {
        continue;
      }

      var isBranchingBlock = block.TransferCmd is GotoCmd gotoCmd1 && gotoCmd1.labelTargets.Count > 1 && 
                             block.Predecessors.Count != 1;
      if (isBranchingBlock) {
        continue;
      }

      removed.Add(block);
      blocks.Remove(block);

      var noPredecessors = !block.Predecessors.Any();
      var noSuccessors = block.TransferCmd is not GotoCmd outGoto2 || !outGoto2.labelTargets.Any();
      foreach (var predecessor in block.Predecessors) {
        var intoCmd = (GotoCmd)predecessor.TransferCmd;
        intoCmd.RemoveTarget(block);
        if (noSuccessors) {
          toVisit.Add(predecessor);
        }
      }

      if (block.TransferCmd is not GotoCmd outGoto) {
        continue;
      }

      foreach (var outBlock in outGoto.labelTargets) {
        outBlock.Predecessors.Remove(block);
        if (noPredecessors) {
          toVisit.Add(outBlock);
        }
      }

      foreach (var predecessor in block.Predecessors) {
        var intoCmd = (GotoCmd)predecessor.TransferCmd;
        foreach (var outBlock in outGoto.labelTargets) {
          if (!intoCmd.labelTargets.Contains(outBlock)) {
            intoCmd.AddTarget(outBlock);
            outBlock.Predecessors.Add(predecessor);
          }
        }
      }
    }
  }

  private static void MergeOneToOneBlocks(List<Block> blocks) {
    var stack = new Stack<Block>();
    foreach (var block in blocks) {
      if (!block.Predecessors.Any()) {
        stack.Push(block);
      }
    }
    while (stack.Any()) {
      var current = stack.Pop();
      if (current.TransferCmd is not GotoCmd gotoCmd) {
        continue;
      }

      if (gotoCmd.labelTargets.Count != 1) {
        foreach (var aNext in gotoCmd.labelTargets) {
          stack.Push(aNext);
        }
        continue;
      }

      var next = gotoCmd.labelTargets.Single();
      if (next.Predecessors.Count != 1) {
        stack.Push(next);
        continue;
      }

      blocks.Remove(next);
      current.Cmds.AddRange(next.Cmds);
      current.TransferCmd = next.TransferCmd;
      foreach (var nextTarget in current.Exits()) {
        nextTarget.Predecessors.Remove(next);
        nextTarget.Predecessors.Add(current);
      }
      stack.Push(current);
    }
  }

  public static void PruneAssumptions(Program program, List<Block> blocks) {
    Dictionary<PredicateCmd, ISet<Variable>> commandVariables = new();

    var gatekeepers = program.Variables.
      Where(g => g.Name.Contains("Height") || g.Name.StartsWith("reveal__")).ToList();
    
    var controlFlowGraph = Pruner.GetControlFlowGraph(blocks);
    var asserts = controlFlowGraph.Nodes.OfType<AssertCmd>().ToList();
    var assumesToKeep = new HashSet<AssumeCmd>();
    foreach (var assert in asserts) {
      var proofByContradiction = assert.Expr.Equals(Expr.False) 
                                 || assert.Expr.ToString() == "Lit(false)"; // TODO use annotation placed by Dafny
      var reachableAssumes = controlFlowGraph.ComputeReachability(assert, false).OfType<AssumeCmd>().ToHashSet();
      if (proofByContradiction) {
        foreach (var assume in reachableAssumes) {
          assumesToKeep.Add(assume);
        }

        continue;
      }
      
      var dependencyGraph = new Graph<object>();
      foreach (var cmd in reachableAssumes.Append<PredicateCmd>(assert)) {
        var variables = GetVariables(cmd);
        var groups = variables.GroupBy(v => v is Constant
                               || v is GlobalVariable
                               || v is Incarnation { OriginalVariable: Constant or GlobalVariable }).ToList();

        var locals = groups.FirstOrDefault(g => !g.Key) ?? Enumerable.Empty<Variable>();
        var globalsForCommand = groups.FirstOrDefault(g => g.Key);
        var localsKnot = new object();
        foreach (var local in locals) {
          dependencyGraph.AddEdge(local, localsKnot);
          dependencyGraph.AddEdge(localsKnot, local);
        }

        if (globalsForCommand != null) {
          var globalsKnot = new object();
          foreach (var global in globalsForCommand) {
            dependencyGraph.AddEdge(global, globalsKnot);
            dependencyGraph.AddEdge(globalsKnot, global);
          }
          dependencyGraph.AddEdge(localsKnot, globalsKnot);
        }
      }

      var controlFlowAssumes = new List<Variable>();
      // var controlFlowAssumes = 
      //   reachableAssumes.Where(cmd => QKeyValue.FindBoolAttribute(cmd.Attributes, "partition")).
      //     SelectMany(GetVariables).ToList();
      HashSet<Variable> dependentVariables = new();

      foreach (var root in controlFlowAssumes.Concat(gatekeepers).Concat(GetVariables(assert))) {
        if (!dependencyGraph.Nodes.Contains(root)) {
          continue;
        }
        foreach (var reachable in dependencyGraph.ComputeReachability(root)) {
          if (reachable is Variable variable) {
            dependentVariables.Add(variable);
          }
        }
      }
      
      foreach(var assumeCmd in reachableAssumes) {
        if (assumeCmd.Expr.Equals(Expr.False) // TODO take into account Lit, use annotation placed by Dafny 
            || GetVariables(assumeCmd).Overlaps(dependentVariables)) {
          assumesToKeep.Add(assumeCmd); // Explicit assume false should be kept. // TODO take into account Lit ??
        } else {
          var c = 3;
        }
      }
    }
    
    foreach (var block in blocks) {
      block.Cmds = block.Cmds.Where(cmd => cmd is not AssumeCmd assumeCmd || assumesToKeep.Contains(assumeCmd)).ToList();
    }

    return;

    ISet<Variable> GetVariables(PredicateCmd cmd) {
      return commandVariables.GetOrCreate(cmd, () => {
        var set = new GSet<object>();
        cmd.Expr.ComputeFreeVariables(set);
        return set.OfType<Variable>().ToHashSet();
      });
    }
  }
}