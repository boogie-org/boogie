using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
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
    var stack = new Stack<Block>();
    foreach (var block in blocks) {
      stack.Push(block);
    }
    while(stack.Any()) {
      var block = stack.Pop();
      if (block.Cmds.Any()) {
        continue;
      }

      var isBranchingBlock = block.TransferCmd is GotoCmd gotoCmd1 && gotoCmd1.labelTargets.Count > 1 && 
                             block.Predecessors.Count != 1;
      if (isBranchingBlock) {
        continue;
      }

      blocks.Remove(block);

      foreach (var predecessor in block.Predecessors) {
        var intoCmd = (GotoCmd)predecessor.TransferCmd;
        intoCmd.RemoveTarget(block);
        stack.Push(predecessor);
      }

      if (block.TransferCmd is not GotoCmd outGoto) {
        continue;
      }

      foreach (var outBlock in outGoto.labelTargets) {
        outBlock.Predecessors.Remove(block);
        stack.Push(outBlock);
      }

      foreach (var predecessor in block.Predecessors) {
        var intoCmd = (GotoCmd)predecessor.TransferCmd;
        foreach (var outBlock in outGoto.labelTargets) {
          outBlock.Predecessors.Remove(block);
          if (!outGoto.labelTargets.Contains(outBlock)) {
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
    var commandsPartOfContradiction = new HashSet<Cmd>();
    var controlFlowGraph = Pruner.GetControlFlowGraph(blocks);
    var asserts = controlFlowGraph.Nodes.OfType<AssertCmd>().ToList();
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
    var liveAnalysis = new LiveVariablesAnalysis(globals, 
      asserts, 
      cmd => controlFlowGraph.Predecessors(cmd),
      cmd => controlFlowGraph.Successors(cmd));
    liveAnalysis.Run();
    
    foreach (var block in blocks) {
      block.Cmds = block.Cmds.Where(cmd => {
        var keep = cmd is not AssumeCmd assumeCmd ||
                   // Do not keep explicit assume false of it does not lead to an assertion.
                       assumeCmd.Expr.Equals(Expr.False) || // Explicit assume false should be kept. // TODO take into account Lit ??
                       commandsPartOfContradiction.Contains(assumeCmd) ||
                       liveAnalysis.LiveCommands.Contains(assumeCmd);
        
        return keep;
      }).ToList();
    }
  }
}

class LiveVariablesAnalysis : DataflowAnalysis<Absy, ImmutableHashSet<Variable>> {
  private readonly Dictionary<PredicateCmd, ISet<Variable>> commandVariables;
  private readonly IReadOnlyList<Variable> globals;
  public HashSet<Cmd> LiveCommands { get; } = new();

  public LiveVariablesAnalysis(
    IReadOnlyList<Variable> globals,
    IReadOnlyList<Absy> roots, 
    Func<Absy, IEnumerable<Absy>> getNext, 
    Func<Absy, IEnumerable<Absy>> getPrevious) : base(roots, getNext, getPrevious) {
    this.globals = globals;
    commandVariables = roots.OfType<PredicateCmd>().ToDictionary(cmd => cmd, cmd => {
      var set = new GSet<object>();
      cmd.Expr.ComputeFreeVariables(set);
      return (ISet<Variable>)set.OfType<Variable>().ToHashSet();
    });
  }

  protected override ImmutableHashSet<Variable> Empty => ImmutableHashSet.CreateRange(globals);
  
  protected override ImmutableHashSet<Variable> Merge(ImmutableHashSet<Variable> first, ImmutableHashSet<Variable> second) {
    return first.Union(second);
  }

  protected override bool StateEquals(ImmutableHashSet<Variable> first, ImmutableHashSet<Variable> second) {
    return first.SetEquals(second);
  }

  ISet<Variable> GetVariables(PredicateCmd cmd) {
    return commandVariables.GetOrCreate(cmd, () => {
      var set = new GSet<object>();
      cmd.Expr.ComputeFreeVariables(set);
      return set.OfType<Variable>().ToHashSet();
    });
  }

  protected override ImmutableHashSet<Variable> Update(Absy node, ImmutableHashSet<Variable> state) {
    if (node is PredicateCmd predicateCmd) {
      var isLive = false;
      if (node is AssertCmd) {
        isLive = true;
      } else if (node is AssumeCmd assumeCmd) {
        /*
         * A path that can not be taken is one whose control flow assumptions together, prove false.
         * By proving false, subsequent assertions are always provable, so the impossible path does not throw errors.
         * Because of this, we may not prune assumptions resulting from control flow paths.
         */
        var isControlFlowCommand = QKeyValue.FindBoolAttribute(assumeCmd.Attributes, "partition");
        if (isControlFlowCommand || GetVariables(assumeCmd).Intersect(state).Any()) {
          isLive = true;
        }
      }
      if (isLive) {
        LiveCommands.Add(predicateCmd);
        return GetVariables(predicateCmd).Aggregate(state, (set, variable) => set.Add(variable));
      }
    }
    return state;
  }
}