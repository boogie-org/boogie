using Graphing;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie {

public static class GraphAlgorithms {

  public static Graph<Node> Dual<Node>(this Graph<Node> g, Node dummySource) {
    var exits = g.Nodes.Where(n => g.Successors(n).Count() == 0).ToList();
    if (exits.Count == 0)
      return null;
    var dual = new Graph<Node>(new HashSet<Tuple<Node, Node>>(g.Edges.Select(e => new Tuple<Node, Node>(e.Item2, e.Item1))));
    if (exits.Count == 1)
      dual.AddSource(exits[0]);
    else {
      dual.AddSource(dummySource);
      foreach (var exit in exits)
        dual.AddEdge(dummySource, exit);
    }
    return dual;
  }

  public static List<Tuple<Node, bool>> LoopyTopSort<Node>(this Graph<Node> g) {
    Contract.Assert(g.Reducible);

    int n = g.Nodes.Count;
    var nodeToNumber = new Dictionary<Node, int>(n);
    var numberToNode = new Node[n];
    var allNodes = new List<int>();
    int counter = 0;
    foreach (Node node in g.Nodes) {
      numberToNode[counter] = node;
      nodeToNumber[node] = counter;
      allNodes.Add(counter);
      counter++;
    }

    var loops = new List<int>[n];
    foreach (var h in g.Headers) {
      var loopNodes = new HashSet<Node>();
      foreach (var b in g.BackEdgeNodes(h))
        loopNodes.UnionWith(g.NaturalLoops(h, b));
      loops[nodeToNumber[h]] =
        new List<int>(loopNodes.Select(node => nodeToNumber[node]));
    }

    var successors = new List<int>[n];
    int[] incomingEdges = new int[n];

    foreach (var e in g.Edges) {
      Contract.Assert(e.Item1 != null);
      Contract.Assert(e.Item2 != null);
      int source = nodeToNumber[e.Item1], target = nodeToNumber[e.Item2];
      if (loops[target] == null || !loops[target].Contains(source)) {
        if (successors[source] == null)
          successors[source] = new List<int>();
        successors[source].Add(target);
        incomingEdges[target]++;
      }
    }

    var sortedNodes = new List<Tuple<Node, bool>>();

    var regionStack = new Stack<Tuple<Node, List<int>>>();
    regionStack.Push(new Tuple<Node, List<int>>(default(Node), allNodes));

    while (regionStack.Count != 0) {
      int rootIndex = -1;
      foreach (var i in regionStack.Peek().Item2) {
        if (incomingEdges[i] == 0) {
          rootIndex = i;
          break;
        }
      }
      if (rootIndex == -1) {
        var region = regionStack.Pop();
        if (regionStack.Count != 0)
          sortedNodes.Add(new Tuple<Node, bool>(region.Item1, true));
        continue;
      }
      incomingEdges[rootIndex] = -1;
      sortedNodes.Add(new Tuple<Node, bool>(numberToNode[rootIndex], false));
      if (successors[rootIndex] != null)
        foreach (int s in successors[rootIndex])
          incomingEdges[s]--;
      if (loops[rootIndex] != null)
        regionStack.Push(new Tuple<Node, List<int>>(numberToNode[rootIndex],
                                                    loops[rootIndex]));
    }

    return sortedNodes;
  }
  
  // Algorithm from Jeanne Ferrante, Karl J. Ottenstein, Joe D. Warren,
  // "The Program Dependence Graph and Its Use in Optimization"
  public static Dictionary<Node, HashSet<Node>> ControlDependence<Node>(this Graph<Node> g) where Node : class, new() {
    Graph<Node> dual = g.Dual(new Node());
    DomRelation<Node> pdom = dual.DominatorMap;
    var result = new Dictionary<Node, HashSet<Node>>();

    var S = g.Edges.Where(e => !pdom.DominatedBy(e.Item1, e.Item2));
    foreach (var edge in S) {
      var L = pdom.LeastCommonAncestor(edge.Item1, edge.Item2);
      var deps = new List<Node>();
      if (L == edge.Item1) {
        pdom.DominatedBy(edge.Item2, edge.Item1, deps);
        deps.Add(edge.Item2);
        deps.Add(edge.Item1);
      } else {
        pdom.DominatedBy(edge.Item2, L, deps);
        deps.Add(edge.Item2);
      }
      if (result.ContainsKey(edge.Item1)) {
        result[edge.Item1].UnionWith(deps);
      } else {
        result[edge.Item1] = new HashSet<Node>(deps);
      }
    }
    return result;
  }

}

}
