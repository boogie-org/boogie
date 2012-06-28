using Graphing;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie {

public static class GraphAlgorithms {

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

}

}
