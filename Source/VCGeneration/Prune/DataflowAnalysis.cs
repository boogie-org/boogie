using System;
using System.Collections.Generic;
using System.Linq;

abstract class DataflowAnalysis<TNode, TState> {
  protected readonly Dictionary<TNode, TState> states;
  protected readonly Dictionary<TNode, TState> inStates = new();
  private readonly Func<TNode, IEnumerable<TNode>> getNext;
  private readonly Func<TNode, IEnumerable<TNode>> getPrevious;

  protected DataflowAnalysis(IEnumerable<TNode> nodes,  
    Func<TNode, IEnumerable<TNode>> getNext,
    Func<TNode, IEnumerable<TNode>> getPrevious) {
    this.getNext = getNext;
    this.getPrevious = getPrevious;
    states = nodes.ToDictionary(n => n, n => Empty);
  }

  public IReadOnlyDictionary<TNode, TState> States => states;
  
  protected abstract TState Empty { get; }

  protected abstract TState Merge(TState first, TState second);

  protected abstract bool StateEquals(TState first, TState second);
  
  protected abstract TState Update(TNode node, TState state);

  public void Run() {
    var queue = new Queue<TNode>();
    foreach (var node in states.Keys) {
      queue.Enqueue(node);
    }
    while (queue.Any()) {
      var node = queue.Dequeue();
      var previous = getPrevious(node);
      var previousStates = previous.Select(p => states[p]).ToList();
      var inState = previousStates.Any() ? previousStates.Aggregate(Merge) : Empty;
      var previousInState = inStates.GetValueOrDefault(node);
      if (previousInState != null && StateEquals(inState, previousInState)) {
        continue;
      }

      inStates[node] = inState;
      var outState = Update(node, inState);
      var previousOutState = states[node];
      if (!StateEquals(outState, previousOutState)) {
        states[node] = outState;
        foreach (var next in getNext(node)) {
          queue.Enqueue(next);
        }
      }
    }
  }
}