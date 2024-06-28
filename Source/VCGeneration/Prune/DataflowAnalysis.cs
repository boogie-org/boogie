using System;
using System.Collections.Generic;
using System.Linq;

abstract class DataflowAnalysis<TNode, TState> {
  private readonly Dictionary<TNode, TState> states;
  private readonly Func<TNode, IReadOnlyList<TNode>> getNext;
  private readonly Func<TNode, IReadOnlyList<TNode>> getPrevious;

  protected DataflowAnalysis(IReadOnlyList<TNode> nodes,  
    Func<TNode, IReadOnlyList<TNode>> getNext,
    Func<TNode, IReadOnlyList<TNode>> getPrevious) {
    this.getNext = getNext;
    this.getPrevious = getPrevious;
    states = nodes.ToDictionary(n => n, n => Empty);
  }
  
  protected abstract TState Empty { get; }

  protected abstract TState Merge(TState first, TState second);

  protected abstract TState Update(TNode node, TState state);

  public void Run() {
    var queue = new Queue<TNode>();
    foreach (var node in states.Keys) {
      queue.Enqueue(node);
    }
    while (queue.Any()) {
      var node = queue.Dequeue();
      var previous = getPrevious(node);
      var inState = previous.Select(p => states[p]).Aggregate(Merge);
      var outState = Update(node, inState);
      var previousOutState = states[node];
      if (!outState.Equals(previousOutState)) {
        states[node] = outState;
        foreach (var next in getNext(node)) {
          queue.Enqueue(next);
        }
      }
    }
  }
}