#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Boogie;

record RevealedState(bool AllHiddenNotRevealed, IImmutableSet<Function> Offset);

class RevealedAnalysis : DataflowAnalysis<Cmd, RevealedState> {
  public RevealedAnalysis(IReadOnlyList<Cmd> nodes, Func<Cmd, IReadOnlyList<Cmd>> getNext, Func<Cmd, IReadOnlyList<Cmd>> getPrevious) : base(nodes, getNext, getPrevious)
  {
  }

  protected override RevealedState Empty => new(false, ImmutableHashSet<Function>.Empty);

  protected override RevealedState Merge(RevealedState first, RevealedState second) {
    if (!first.AllHiddenNotRevealed && !second.AllHiddenNotRevealed) {
      return new RevealedState(false, first.Offset.Union(second.Offset));
    }

    if (!first.AllHiddenNotRevealed) {
      return first;
    }
    
    if (!second.AllHiddenNotRevealed) {
      return second;
    }

    return new RevealedState(false, first.Offset.Intersect(second.Offset));
  }

  protected override RevealedState Update(Cmd node, RevealedState state) {
    if (node is HideRevealCmd revealCmd) {
      if (revealCmd.Function == null) {
        return new RevealedState(revealCmd.Hide, ImmutableHashSet<Function>.Empty);
      }

      if (revealCmd.Hide == state.AllHiddenNotRevealed) {
        return state;
      }

      return state with { Offset = state.Offset.Add(revealCmd.Function) };
    }

    return state;
  }
}