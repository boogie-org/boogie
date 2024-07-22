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
      gotoCmd.RemoveTarget(next);
      if (next.TransferCmd is GotoCmd nextGotoCmd) {
        gotoCmd.AddTargets(nextGotoCmd.labelTargets);
        foreach (var nextTarget in nextGotoCmd.labelTargets) {
          nextTarget.Predecessors.Remove(next);
          nextTarget.Predecessors.Add(current);
        }
      }
      stack.Push(current);
    }
  }

  public static void PruneAssumptions(Program program, List<Block> blocks) {

    var controlFlowGraph0 = Pruner.GetControlFlowGraph(blocks);
    var asserts = controlFlowGraph0.Nodes.OfType<AssertCmd>().ToList();
    var reachesAnalysis = new ReachesAssertionAnalysis(asserts,
      cmd => controlFlowGraph0.Predecessors(cmd),
      cmd => controlFlowGraph0.Successors(cmd));
    reachesAnalysis.Run();
    foreach (var block in blocks) {
      block.Cmds = block.Cmds.Where(cmd => {
        var keep = cmd is not AssumeCmd || reachesAnalysis.States.GetValueOrDefault(cmd, false);
        return keep;
      }).ToList();
    }

    var commandsPartOfContradiction = new HashSet<Cmd>();
    var controlFlowGraph = Pruner.GetControlFlowGraph(blocks);
    foreach (var assert in asserts) {
      var proofByContradiction = assert.Expr.Equals(Expr.False); // TODO take into account Lit ??
      if (proofByContradiction) {
        // Assumptions before a proof by contradiction may all be relevant for proving false
        foreach (var reachable in controlFlowGraph.ComputeReachability(assert, false).OfType<AssumeCmd>()) {
          commandsPartOfContradiction.Add(reachable);
        }
      }
    }
    
    var globals = program.Variables.Where(g => g.Name.Contains("Height")).ToList();

    Dictionary<PredicateCmd, ISet<Variable>> commandVariables = new();
    ISet<Variable> GetVariables(PredicateCmd cmd) {
      return commandVariables.GetOrCreate(cmd, () => {
        var set = new GSet<object>();
        cmd.Expr.ComputeFreeVariables(set);
        return set.OfType<Variable>().ToHashSet();
      });
    }
    
    var dependencyGraph = new Graph<Absy>();
    foreach (var block in blocks) {
      foreach (var cmd in block.Cmds.OfType<PredicateCmd>()) {
        foreach (var variable in GetVariables(cmd)) {
          dependencyGraph.AddEdge(cmd, variable);
          dependencyGraph.AddEdge(variable, cmd);
        }
      }
    }

    foreach (var global in globals) {
      dependencyGraph.Nodes.Add(global);
    }

    var controlFlowAssumes = dependencyGraph.Nodes.OfType<AssumeCmd>().Where(
      cmd => QKeyValue.FindBoolAttribute(cmd.Attributes, "partition"));
    HashSet<AssumeCmd> reachableAssumes = new();
    foreach (var root in asserts.Concat<Absy>(globals).Concat(controlFlowAssumes)) {
      foreach (var reachable in dependencyGraph.ComputeReachability(root)) {
        if (reachable is AssumeCmd assumeCmd) {
          reachableAssumes.Add(assumeCmd);
        }
      }
    }
    
    foreach (var block in blocks) {
      block.Cmds = block.Cmds.Where(cmd => {
        var keep = cmd is not AssumeCmd assumeCmd ||
                   assumeCmd.Expr.Equals(Expr.False) || // Explicit assume false should be kept. // TODO take into account Lit ??
                   commandsPartOfContradiction.Contains(assumeCmd) ||
                   reachableAssumes.Contains(assumeCmd);

        if (!keep) {
          var b = 3;
        }
        return keep;
      }).ToList();
    }
  }
}

class ReachesAssertionAnalysis : DataflowAnalysis<Absy, bool> {
  public ReachesAssertionAnalysis(IReadOnlyList<Absy> roots, Func<Absy, IEnumerable<Absy>> getNext, Func<Absy, IEnumerable<Absy>> getPrevious) : base(roots, getNext, getPrevious)
  {
  }

  protected override bool Empty => false;
  protected override bool Merge(bool first, bool second) {
    return first || second;
  }

  protected override bool StateEquals(bool first, bool second) {
    return first == second;
  }

  protected override bool Update(Absy node, bool state) {
    return node is AssertCmd || state;
  }
}