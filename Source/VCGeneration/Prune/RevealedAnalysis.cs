#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;

record RevealedState(bool AllHiddenNotRevealed, IImmutableSet<Function> Offset) {
  public bool IsRevealed(Function function) {
    return AllHiddenNotRevealed == Offset.Contains(function);
  }

  public static readonly RevealedState AllRevealed = new RevealedState(false, ImmutableHashSet<Function>.Empty);
  public static readonly RevealedState AllHidden = new RevealedState(true, ImmutableHashSet<Function>.Empty);
}

class RevealedAnalysis : DataflowAnalysis<Cmd, ImmutableStack<RevealedState>> {
  
  public RevealedAnalysis(IReadOnlyList<Cmd> roots, 
    Func<Cmd, IEnumerable<Cmd>> getNext, 
    Func<Cmd, IEnumerable<Cmd>> getPrevious) : base(roots, getNext, getPrevious)
  {
  }

  protected override ImmutableStack<RevealedState> Empty => ImmutableStack<RevealedState>.Empty.Push(
    RevealedState.AllRevealed);

  protected override ImmutableStack<RevealedState> Merge(ImmutableStack<RevealedState> first, ImmutableStack<RevealedState> second) {
    var firstTop = first.Peek();
    var secondTop = second.Peek();
    var mergedTop = MergeStates(firstTop, secondTop);
    return ImmutableStack.Create(mergedTop);
  }

  protected override bool StateEquals(ImmutableStack<RevealedState> first, ImmutableStack<RevealedState> second) {
    return first.Peek().Equals(second.Peek());
  }

  /// <summary>
  /// Takes the union of what is revealed.
  /// </summary>
  public static RevealedState MergeStates(RevealedState first, RevealedState second) {
    if (!first.AllHiddenNotRevealed && !second.AllHiddenNotRevealed) {
      var intersect = first.Offset.Intersect(second.Offset);
      if (intersect.Count == first.Offset.Count) {
        return first;
      }
      return new RevealedState(false, intersect);
    }

    if (!first.AllHiddenNotRevealed) {
      return first;
    }
    
    if (!second.AllHiddenNotRevealed) {
      return second;
    }

    var union = first.Offset.Union(second.Offset);
    if (union.Count == first.Offset.Count) {
      return first;
    }
    return new RevealedState(true, union);
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
    if (node is ChangeScope changeScope) {
      return changeScope.Push ? state.Push(state.Peek()) : 
        state.Pop();
    }

    if (node is HideRevealCmd hideRevealCmd) {
      var latestState = state.Peek();
      var updatedState = GetUpdatedState(hideRevealCmd, latestState);
      return updatedState.Equals(latestState) ? state : state.Pop().Push(updatedState);
    }

    return state;
  }
}