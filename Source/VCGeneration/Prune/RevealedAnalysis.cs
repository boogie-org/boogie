#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Boogie;

record RevealedState(bool AllHiddenNotRevealed, IImmutableSet<Function> Offset) {
  public bool IsRevealed(Function function) {
    return AllHiddenNotRevealed == Offset.Contains(function);
  }
}

class RevealedAnalysis : DataflowAnalysis<Cmd, ImmutableStack<RevealedState>> {
  
  public RevealedAnalysis(IEnumerable<Cmd> nodes, 
    Func<Cmd, IEnumerable<Cmd>> getNext, 
    Func<Cmd, IEnumerable<Cmd>> getPrevious) : base(nodes, getNext, getPrevious)
  {
  }

  protected override ImmutableStack<RevealedState> Empty => ImmutableStack<RevealedState>.Empty;

  protected override ImmutableStack<RevealedState> Merge(ImmutableStack<RevealedState> first, ImmutableStack<RevealedState> second) {
    var firstTop = first.Peek();
    var secondTop = second.Peek();
    return ImmutableStack.Create(MergeStates(firstTop, secondTop));
  }

  /// <summary>
  /// Takes the union of what is revealed.
  /// </summary>
  public static RevealedState MergeStates(RevealedState first, RevealedState second) {
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

  static RevealedState GetUpdatedState(HideRevealCmd hideRevealCmd, RevealedState state) {
      if (hideRevealCmd.Function == null) {
        return new RevealedState(hideRevealCmd.Hide, ImmutableHashSet<Function>.Empty);
      }

      if (hideRevealCmd.Hide == state.AllHiddenNotRevealed) {
        return state;
      }

      return state with { Offset = state.Offset.Add(hideRevealCmd.Function) };
  }
  
  protected override ImmutableStack<RevealedState> Update(Cmd node, ImmutableStack<RevealedState> state) {
    if (node is PopHideReveal) {
      return state.Pop();
    }

    if (node is HideRevealCmd hideRevealCmd) {
      var latestState = state.Peek();
      var updatedState = GetUpdatedState(hideRevealCmd, latestState);
      return state.Push(updatedState);
    }

    return state;
  }
}