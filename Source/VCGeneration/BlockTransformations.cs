using System;
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
    ISet<Variable> GetVariables(PredicateCmd cmd) {
      return commandVariables.GetOrCreate(cmd, () => {
        var set = new GSet<object>();
        cmd.Expr.ComputeFreeVariables(set);
        return set.OfType<Variable>().ToHashSet();
      });
    }
    
    var globals = program.Variables.Where(g => g.Name.Contains("Height")).ToList();
    
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
      
      var dependencyGraph = new Graph<Absy>();
      foreach (var cmd in reachableAssumes.Append<PredicateCmd>(assert)) {
        foreach (var variable in GetVariables(cmd)) {
          if (!globals.Contains(variable) && 
              (false
              || variable is Incarnation { OriginalVariable: GlobalVariable } 
              || variable.Name.Contains("$w$")
              || variable is Constant
              || variable is GlobalVariable
              )) 
          {
            continue;
          }
          dependencyGraph.AddEdge(cmd, variable);
          dependencyGraph.AddEdge(variable, cmd);
        }
      }

      var controlFlowAssumes = new List<AssumeCmd>();
      // reachableAssumes.Where(cmd => QKeyValue.FindBoolAttribute(cmd.Attributes, "partition")).ToList();
      HashSet<AssumeCmd> dependentAssumes = new();
      // TODO could improve performance related to globals

      foreach (var root in controlFlowAssumes.Concat<Absy>(globals).Append<Absy>(assert)) {
        if (!dependencyGraph.Nodes.Contains(root)) {
          continue;
        }
        foreach (var reachable in dependencyGraph.ComputeReachability(root)) {
          if (reachable is AssumeCmd assumeCmd) {
            dependentAssumes.Add(assumeCmd);
          }
        }
      }
      
      foreach(var assumeCmd in reachableAssumes)
      {
        if (GetVariables(assumeCmd).All(v => v is Constant)) {
          assumesToKeep.Add(assumeCmd);
        } 
        else 
        if (assumeCmd.Expr.Equals(Expr.False) || dependentAssumes.Contains(assumeCmd)) {
          assumesToKeep.Add(assumeCmd); // Explicit assume false should be kept. // TODO take into account Lit ??
        } else {
          var c = 3;
        }
      }
    }
    
    foreach (var block in blocks) {
      block.Cmds = block.Cmds.Where(cmd => {
        var keep = cmd is not AssumeCmd assumeCmd || assumesToKeep.Contains(assumeCmd);

        if (!keep) {
          var b = 3;
        }
        return keep;
      }).ToList();
    }
  }
}