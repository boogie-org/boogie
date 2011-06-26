//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Text; // for StringBuilder
using System.Diagnostics.Contracts;
namespace Graphing {

  internal static class Util {
    private static string/*!*/ ListToString<T>(IEnumerable<T> xs) {
      Contract.Ensures(Contract.Result<string>() != null);
      StringBuilder sb = new StringBuilder();
      sb.Append("[");
      bool first = true;
      foreach (T/*!*/ x in xs) {
        Contract.Assert(x != null);
        if (!first)
          sb.Append(", ");
        sb.Append(x.ToString());
        first = false;
      }
      sb.Append("]");
      return sb.ToString();
    }
    public static string/*!*/ MapToString<Node>(Dictionary<Node, List<Node>> d) {
      Contract.Ensures(Contract.Result<string>() != null);
      StringBuilder sb = new StringBuilder();
      sb.Append("{");
      bool first = true;
      foreach (KeyValuePair<Node, List<Node>> de in d) {
        if (!first)
          sb.Append(", ");
        Contract.Assert(!object.Equals(de.Key,default(Node)));
        sb.Append(de.Key.ToString());
        sb.Append("~>");
        sb.Append(ListToString(de.Value));
        first = false;
      }
      sb.Append("}");
      return sb.ToString();
    }
  }

  // own struct to represent possibly undefined values, because Mono does
  // not like arrays with element type T! or T?
  public struct Maybe<T> {
    private T Value;
    public bool IsSet;  // initialised with false by the default ctor
    public T Val {
      get {
        Contract.Assume(IsSet);
        return Value;
      }
      set {
        Value = value;
        IsSet = true;
      }
    }
    public void UnSet() {
      IsSet = false;
    }
  }

  internal class DomRelation<Node> {
    // doms maps (unique) node numbers to the node numbers of the immediate dominator
    // to use it on Nodes, one needs the two way mapping between nodes and their numbers.
    private int[] doms; // 0 is unused: means undefined
    // here are the two mappings
    private Maybe<Node>[] postOrderNumberToNode;
    private Dictionary<Node, int> nodeToPostOrderNumber;
    private int sourceNum; // (number for) root of the graph
    private Node source; // root of the graph
    private Graph<Node> graph;
    private Dictionary<Node, List<Node>> immediateDominatorMap;

    [NotDelayed]
    internal DomRelation(Graph<Node> g, Node source) {
      this.graph = g;
      // slot 0 not used: nodes are numbered from 1 to n so zero
      // can represent undefined.
      this.source = source;
      //:base();
      this.NewComputeDominators();
    }
    public Dictionary<Node, List<Node>> ImmediateDominatorMap {
      get {
        Contract.Assume(this.immediateDominatorMap != null);
        return this.immediateDominatorMap;
      }
    }
    public bool DominatedBy(Node dominee, Node dominator) {
      Contract.Assume(this.nodeToPostOrderNumber != null);
      Contract.Assume(this.doms != null);
      int domineeNum = this.nodeToPostOrderNumber[dominee];
      int dominatorNum = this.nodeToPostOrderNumber[dominator];
      if (domineeNum == dominatorNum)
        return true;
      int currentNodeNum = this.doms[domineeNum];
      do {
        if (currentNodeNum == dominatorNum)
          return true;
        currentNodeNum = this.doms[currentNodeNum];
      } while (currentNodeNum != this.sourceNum);
      return false;
    }
    private Dictionary<Node, List<Node>> domMap = null;
    [Pure]
    public override string ToString() {
      Contract.Assume(this.doms != null);
      int[] localDoms = this.doms;
      Contract.Assume(this.postOrderNumberToNode != null);
      if (domMap == null) {
        domMap = new Dictionary<Node, List<Node>>();
        for (int i = 1; i < localDoms.Length; i++) { // 0 slot is not used
          int domineeNum = i;
          int currentNodeNum = domineeNum;
          List<Node> dominators = new List<Node>();
          while (currentNodeNum != this.sourceNum) {
            dominators.Add(this.postOrderNumberToNode[currentNodeNum].Val);
            currentNodeNum = this.doms[currentNodeNum];
          }
          dominators.Add(this.postOrderNumberToNode[this.sourceNum].Val);
          domMap.Add(this.postOrderNumberToNode[i].Val, dominators);
        }
      }
      StringBuilder sb = new StringBuilder();
      sb.Append("{");
      bool first = true;
      foreach (KeyValuePair<Node, List<Node>> de in domMap) {
        if (!first)
          sb.Append(", ");
        Contract.Assert(!object.Equals(de.Key, default(Node)));
        sb.Append(de.Key.ToString());
        sb.Append("~>");
        sb.Append(ListToString(de.Value));
        first = false;
      }
      sb.Append("}");
      return sb.ToString();
    }
    private void PrintIntArray(int[] xs) {
      Console.Write("[");
      for (int i = 0; i < xs.Length; i++) {
        if (0 < i)
          Console.Write(", ");
        Console.Write(xs[i]);
      }
      Console.WriteLine("]");
    }
    public void PrintList<T>(IEnumerable<T> xs) {
      Console.Write("[");
      int i = 0;
      foreach (T/*!*/ x in xs) {
        Contract.Assert(x != null);
        if (0 < i)
          Console.Write(", ");
        Console.Write(x.ToString());
        i++;
      }
      Console.WriteLine("]");
    }
    public string/*!*/ ListToString<T>(IEnumerable<T> xs) {
      Contract.Ensures(Contract.Result<string>() != null);
      StringBuilder sb = new StringBuilder();
      sb.Append("[");
      bool first = true;
      foreach (T/*!*/ x in xs) {
        Contract.Assert(x != null);
        if (!first)
          sb.Append(", ");
        sb.Append(x.ToString());
        first = false;
      }
      sb.Append("]");
      return sb.ToString();
    }

    // Keith D. Cooper, Timothy J. Harvey, Ken Kennedy, "A Simple, Fast Dominance Algorithm ", Software Practice and Experience, 2001.
    // http://citeseer.ist.psu.edu/cooper01simple.html
    private void NewComputeDominators() {
      int n = this.graph.Nodes.Count;
      this.postOrderNumberToNode = new Maybe<Node>[n + 1];
      this.nodeToPostOrderNumber = new Dictionary<Node, int>();
      //HashSet<Node> visited = new HashSet<Node>();
      //int currentNumber = 1;
      Contract.Assume(this.source != null);
      //this.PostOrderVisit(this.source, visited, ref currentNumber);
      this.PostOrderVisitIterative(this.source);
      this.sourceNum = this.nodeToPostOrderNumber[source];
      //    for (int i = 1; i <= n; i++){ Console.WriteLine(postOrderNumberToNode[i]); }
      this.doms = new int[n + 1]; // 0 is unused: means undefined
      Node start_node = this.source;
      this.doms[this.nodeToPostOrderNumber[start_node]] = this.nodeToPostOrderNumber[start_node];
      bool changed = true;
      //    PrintIntArray(doms);
      while (changed) {
        changed = false;
        // for all nodes, b, in reverse postorder (except start_node)
        for (int nodeNum = n - 1; 1 <= nodeNum; nodeNum--) {
          Node b = this.postOrderNumberToNode[nodeNum].Val;
          IEnumerable<Node> predecessors = this.graph.Predecessors(b);
          // find a predecessor (i.e., a higher number) for which
          // the doms array has been set
          int new_idom = 0;
          int first_processed_predecessor = 0;
          #region new_idom <- number of first (processed) predecessor of b (pick one)
          foreach (Node p in predecessors) {
            if (this.doms[this.nodeToPostOrderNumber[p]] != 0) {
              int x = this.nodeToPostOrderNumber[p];
              new_idom = x;
              first_processed_predecessor = x;
              break;
            }
          }
          #endregion
          #region for all other predecessors, p, of b
          foreach (Node p in predecessors) {
            if (this.nodeToPostOrderNumber[p] == first_processed_predecessor) {
              continue;
            }
            if (this.doms[this.nodeToPostOrderNumber[p]] != 0)
              new_idom = intersect(this.nodeToPostOrderNumber[p], new_idom, this.doms);
          }
          #endregion
          if (this.doms[this.nodeToPostOrderNumber[b]] != new_idom) {
            this.doms[this.nodeToPostOrderNumber[b]] = new_idom;
            changed = true;
          }
        }
      }
      #region Populate the Immediate Dominator Map
      int sourceNum = this.nodeToPostOrderNumber[this.source];
      immediateDominatorMap = new Dictionary<Node, List<Node>>();
      for (int i = 1; i <= n; i++) {
        Node node = this.postOrderNumberToNode[i].Val;
        Node idomNode = this.postOrderNumberToNode[this.doms[i]].Val;
        if (i == sourceNum && this.doms[i] == sourceNum) {
          continue;
        }
        if (immediateDominatorMap.ContainsKey(idomNode)) {
          immediateDominatorMap[idomNode].Add(node);
        } else {
          List<Node> l = new List<Node>();
          l.Add(node);
          immediateDominatorMap.Add(idomNode, l);
        }
      }
      #endregion
    }
    private int intersect(int b1, int b2, int[] doms) {
      int finger1 = b1;
      int finger2 = b2;
      while (finger1 != finger2) {
        while (finger1 < finger2) {
          finger1 = doms[finger1];
        }
        while (finger2 < finger1) {
          finger2 = doms[finger2];
        }
      }
      return finger1;
    }
    private void PostOrderVisit(Node/*!*/ n, HashSet<Node> visited, ref int currentNumber) {
      Contract.Requires(n != null);
      if (visited.Contains(n))
        return;
      visited.Add(n);
      foreach (Node/*!*/ child in this.graph.Successors(n)) {
        Contract.Assert(child != null);
        PostOrderVisit(child, visited, ref currentNumber);
      }
      Contract.Assume(this.postOrderNumberToNode != null);
      Contract.Assume(this.nodeToPostOrderNumber != null);
      this.postOrderNumberToNode[currentNumber].Val = n;
      this.nodeToPostOrderNumber[n] = currentNumber;
      currentNumber++;
      return;
    }
    // Iterative version: mimics the above recursive procedure
    private void PostOrderVisitIterative(Node n)
    {
        Contract.Requires(n != null);
        var visited = new HashSet<Node>();
        var grey = new HashSet<Node>();
        var stack = new Stack<Node>();

        int currentNumber = 1;

        stack.Push(n);
        visited.Add(n);

        while (stack.Count != 0)
        {
            var curr = stack.Pop();

            if (grey.Contains(curr))
            {
                Contract.Assume(this.postOrderNumberToNode != null);
                Contract.Assume(this.nodeToPostOrderNumber != null);
                this.postOrderNumberToNode[currentNumber].Val = curr;
                this.nodeToPostOrderNumber[curr] = currentNumber;
                currentNumber++;
            }
            else
            {
                grey.Add(curr);
                stack.Push(curr);
                foreach (Node/*!*/ child in this.graph.Successors(curr))
                {
                    Contract.Assert(child != null);
                    if (!visited.Contains(child))
                    {
                        visited.Add(child);
                        stack.Push(child);
                    }
                }
            }

        }


    }
  }

  public class Graph<Node> {
    private HashSet<Tuple<Node/*!*/, Node/*!*/>> es;
    private HashSet<Node> ns;
    private Node source;
    private bool reducible;
    private HashSet<Node> headers;
    private Dictionary<Node, HashSet<Node>> backEdgeNodes;
    private Dictionary<Tuple<Node/*!*/, Node/*!*/>, HashSet<Node>> naturalLoops;

    private DomRelation<Node> dominatorMap = null;
    private Dictionary<Node, HashSet<Node>> predCache = new Dictionary<Node, HashSet<Node>>();
    private Dictionary<Node, HashSet<Node>> succCache = new Dictionary<Node, HashSet<Node>>();
    private bool predComputed;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(es == null || Contract.ForAll(es, p => p.Item1 != null && p.Item2 != null));
      Contract.Invariant(naturalLoops == null || Contract.ForAll(naturalLoops.Keys, p => p.Item2 != null && p.Item1 != null));
    }


    private class PreHeader {
      Node/*!*/ myHeader;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(myHeader != null);
      }

      internal PreHeader(Node/*!*/ h) {
        Contract.Requires(h != null);
        myHeader = h;
      }

      [Pure]
      public override string/*!*/ ToString() {
        Contract.Ensures(Contract.Result<string>() != null);
        return "#" + myHeader.ToString();
      }
    }

    public Graph(HashSet<Tuple<Node/*!*/, Node/*!*/>> edges) {

      Contract.Requires(cce.NonNullElements(edges) && Contract.ForAll(edges, p => p.Item1 != null && p.Item2 != null));
      es = edges;

      // original A#
      //ns = Set<Node>{ x : <x,y> in es } + Set<Node>{ y : <x,y> in es };

      // closest Spec#
      //ns = new Set<Node>{ Tuple<Node,Node> p in edges; p.Item1 } + new Set<Node>{ Tuple<Node,Node> p in edges; p.Item2 };

      // 
      HashSet<Node> temp = new HashSet<Node>();
      foreach (Tuple<Node/*!*/, Node/*!*/> p in edges) {
        Contract.Assert(p.Item1 != null);
        temp.Add(p.Item1);
        Contract.Assert(p.Item2 != null);
        temp.Add(p.Item2);
      }
      ns = temp;
    }
    public Graph() {
      es = new HashSet<Tuple<Node/*!*/, Node/*!*/>>();
      ns = new HashSet<Node>();
    }

    // BUGBUG: Set<T>.ToString() should return a non-null string
    [Pure]
    public override string/*!*/ ToString() {
      return "" + es.ToString();
    }

    public void AddSource(Node/*!*/ x) {
      Contract.Requires(x != null);
      // BUGBUG: This generates bad code in the compiler
      //ns += new Set<Node>{x};
      ns.Add(x);
      source = x;
    }

    public void AddEdge(Node/*!*/ source, Node/*!*/ dest) {
      Contract.Requires(source != null);
      Contract.Requires(dest != null);
      //es += Set<Edge>{<source,dest>};
      //ns += Set<Node>{source, dest};
      es.Add(new Tuple<Node/*!*/, Node/*!*/>(source, dest));
      ns.Add(source);
      ns.Add(dest);
      predComputed = false;
    }

    public HashSet<Node> Nodes {
      get {
        return ns;
      }
    }
    public IEnumerable<Tuple<Node/*!*/, Node/*!*/>> Edges {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Tuple<Node, Node>>>())
          && Contract.ForAll(Contract.Result<IEnumerable<Tuple<Node, Node>>>(), n =>
          n.Item1 != null && n.Item2 != null));
        return es;
      }
    }

    public bool Edge(Node/*!*/ x, Node/*!*/ y) {
      Contract.Requires(x != null);
      Contract.Requires(y != null);
      // original A#
      // return <x,y> in es;
      return es.Contains(new Tuple<Node/*!*/, Node/*!*/>(x, y));
    }

    private void ComputePredSuccCaches() {
      if (predComputed)
        return;
      predComputed = true;
      predCache = new Dictionary<Node, HashSet<Node>>();
      succCache = new Dictionary<Node, HashSet<Node>>();

      foreach (Node n in Nodes) {
        predCache[n] = new HashSet<Node>();
        succCache[n] = new HashSet<Node>();
      }

      foreach (Tuple<Node/*!*/, Node/*!*/> p in Edges) {
        Contract.Assert(p.Item1 != null);
        Contract.Assert(p.Item2 != null);
        HashSet<Node> tmp;

        tmp = predCache[p.Item2];
        tmp.Add(p.Item1);
        predCache[p.Item2] = tmp;

        tmp = succCache[p.Item1];
        tmp.Add(p.Item2);
        succCache[p.Item1] = tmp;
      }
    }

    internal IEnumerable<Node> Predecessors(Node n) {
      // original A#
      //Set<Node> result = Set{ x : x in Nodes, Edge(x,n) };

      ComputePredSuccCaches();
      return predCache[n];
    }

    internal IEnumerable<Node> Successors(Node n) {
      ComputePredSuccCaches();
      return succCache[n];
    }

    internal DomRelation<Node> /*Map<Node,Set<Node>>*/ DominatorMap {
      get {
        Contract.Assert(source != null);
        if (this.dominatorMap == null) {
          this.dominatorMap = new DomRelation<Node>(this, this.source);
        }
        return this.dominatorMap;
      }
    }

    public Dictionary<Node, List<Node>> ImmediateDominatorMap {
      get {
        Contract.Assert(source != null);
        if (this.dominatorMap == null) {
          this.dominatorMap = new DomRelation<Node>(this, this.source);
        }
        return this.dominatorMap.ImmediateDominatorMap;
      }
    }
    public List<Node> ImmediatelyDominatedBy(Node/*!*/ n) {
      Contract.Requires(n != null);
      List<Node> dominees;
      this.ImmediateDominatorMap.TryGetValue(n, out dominees);
      return dominees == null ? new List<Node>() : dominees;
    }

    public IEnumerable<Node/*?*/> TopologicalSort() {
      bool acyclic;
      List<Node> sortedList;
      this.TarjanTopSort(out acyclic, out sortedList);
      return acyclic ? sortedList : new List<Node>();
    }
    // From Tarjan 1972
    public void TarjanTopSort(out bool acyclic, out List<Node> sortedNodes) {
      int n = this.Nodes.Count;
      if (n == 0) {
        acyclic = true;
        sortedNodes = new List<Node>();
        return;
      }
      int[] incomingEdges = new int[n];
      // need an arbitrary numbering for the nodes to use as indices into
      // the arrays used within this algorithm
      Dictionary<Node, int> nodeToNumber = new Dictionary<Node, int>(n);
      Maybe<Node>[] numberToNode = new Maybe<Node>[n];
      int counter = 0;
      foreach (Node node in this.Nodes) {
        numberToNode[counter].Val = node;
        nodeToNumber[node] = counter;
        counter++;
      }
      foreach (Tuple<Node/*!*/, Node/*!*/> e in this.Edges) {
        Contract.Assert(e.Item1 != null);
        Contract.Assert(e.Item2 != null);
        Node/*!*/ target = e.Item2;
        incomingEdges[nodeToNumber[target]]++;
      }
      List<Node> sorted = new List<Node>();
      int sortedIndex = 0;
      while (sortedIndex < n) {
        // find a root (i.e., its index)
        int rootIndex = -1;
        for (int i = 0; i < n; i++) {
          if (incomingEdges[i] == 0) {
            rootIndex = i;
            break;
          }
        }
        if (rootIndex == -1) {
          acyclic = false;
          sortedNodes = new List<Node>();
          return;
        }
        // mark root so it won't be used again
        incomingEdges[rootIndex] = -1;
        Node root = numberToNode[rootIndex].Val;
        sorted.Add(root);
        ++sortedIndex;
        foreach (Node s in this.Successors(root)) {
          incomingEdges[nodeToNumber[s]]--;
        }
      }
      acyclic = true;
      sortedNodes = sorted;
      return;
    }
    private IEnumerable<Node> OldTopologicalSort() {
      Tuple<bool, List<Node>> result = this.TopSort();
      return result.Item1 ? result.Item2 : (IEnumerable<Node>)new List<Node>();
    }
    // From AsmL distribution example
    private Tuple<bool, List<Node>> TopSort()
    {
      List<Node> S = new List<Node>();
      HashSet<Node> V = this.Nodes;
      HashSet<Node> X = new HashSet<Node>();
      foreach (Node/*!*/ n in V) {
        Contract.Assert(n != null);
        X.Add(n);
      }
      bool change = true;
      while (change)
      // invariant: X = V - S
    {
        change = false;
        if (X.Count > 0) {
          foreach (Node/*!*/ n in X) {
            Contract.Assert(n != null);
            // see if n has any incoming edges from any other node in X
            bool inDegreeZero = true;
            foreach (Node/*!*/ u in X) {
              Contract.Assert(u != null);
              if (this.Edge(u, n)) {
                inDegreeZero = false;
                break; // no point looking further
              }
            }
            if (inDegreeZero) {
              S.Add(n);
              X.Remove(n);
              change = true;
              break; // might as well go back and start looking through X from the beginning
            }
          }
          // Then we made it all the way through X without finding a source node
          if (!change) {
            return new Tuple<bool, List<Node>>(false, new List<Node>());
          }
        }
      }
      return new Tuple<bool, List<Node>>(true, S);
    }

    public static bool Acyclic(Graph<Node> g, Node source) {
      bool acyclic;
      List<Node> sortedList;
      g.TarjanTopSort(out acyclic, out sortedList);
      return acyclic;
    }

    // [Dragon, Fig. 10.15, p. 604. Algorithm for constructing the natural loop.]
    static HashSet<Node> NaturalLoop(Graph<Node> g, Tuple<Node/*!*/, Node/*!*/> backEdge)
    {
      Contract.Requires(backEdge.Item1 != null && backEdge.Item2 != null);
      Node/*!*/ n = backEdge.Item1;
      Node/*!*/ d = backEdge.Item2;
      Stack<Node> stack = new Stack<Node>();
      HashSet<Node> loop = new HashSet<Node>();
      loop.Add(d);
      if (!n.Equals(d)) // then n is not in loop
      {
        loop.Add(n);
        stack.Push(n); // push n onto stack
      }
      while (stack.Count > 0) // not empty
      {
        Node m = stack.Peek();
        stack.Pop(); // pop stack
        foreach (Node/*!*/ p in g.Predecessors(m)) {
          Contract.Assert(p != null);
          if (!(loop.Contains(p))) {
            loop.Add(p);
            stack.Push(p); // push p onto stack
          }
        }
      }
      return loop;
    }

    internal struct ReducibleResult {
      internal bool reducible;
      internal HashSet<Node> headers;
      internal Dictionary<Node, HashSet<Node>> backEdgeNodes;
      internal Dictionary<Tuple<Node/*!*/, Node/*!*/>, HashSet<Node>> naturalLoops;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Contract.ForAll(naturalLoops.Keys, p => p.Item1 != null && p.Item2 != null));
      }

      internal ReducibleResult(bool b, HashSet<Node> headers, Dictionary<Node, HashSet<Node>> backEdgeNodes, Dictionary<Tuple<Node/*!*/, Node/*!*/>, HashSet<Node>> naturalLoops)
      {
        Contract.Requires(naturalLoops == null || Contract.ForAll(naturalLoops.Keys, Key => Key.Item1 != null && Key.Item2 != null));
        this.reducible = b;
        this.headers = headers;
        this.backEdgeNodes = backEdgeNodes;
        this.naturalLoops = naturalLoops;
      }

    }

    // [Dragon, p. 606]
    static ReducibleResult ComputeReducible(Graph<Node> g, Node source) {
      // first, compute the dom relation
      DomRelation<Node> /*Map<Node,Set<Node>>*/ D = g.DominatorMap;
      return ComputeReducible(g, source, D);
    }

    // [Dragon, p. 606]
    static ReducibleResult ComputeReducible(Graph<Node> g,
                                Node source,
                                DomRelation<Node>/*!*/ DomRelation) {
      Contract.Requires(DomRelation != null);

      //Console.WriteLine("[" + DateTime.Now +"]: begin ComputeReducible");
      IEnumerable<Tuple<Node/*!*/, Node/*!*/>> edges = g.Edges;
      Contract.Assert(Contract.ForAll(edges, n => n.Item1 != null && n.Item2 != null));
      HashSet<Tuple<Node/*!*/, Node/*!*/>> backEdges = new HashSet<Tuple<Node/*!*/, Node/*!*/>>();
      HashSet<Tuple<Node/*!*/, Node/*!*/>> nonBackEdges = new HashSet<Tuple<Node/*!*/, Node/*!*/>>();
      foreach (Tuple<Node/*!*/, Node/*!*/> e in edges) {
        Contract.Assert(e.Item1 != null);
        Contract.Assert(e.Item2 != null);
        Node x = e.Item1;
        Node y = e.Item2; // so there is an edge from x to y
        if (DomRelation.DominatedBy(x, y)) { // y dom x: which means y dominates x
          backEdges.Add(e);
        } else {
          nonBackEdges.Add(e);
        }
      }
      if (!Acyclic(new Graph<Node>(nonBackEdges), source)) {
        return new ReducibleResult(false,
                                   new HashSet<Node>(),
                                   new Dictionary<Node, HashSet<Node>>(),
                                   new Dictionary<Tuple<Node/*!*/, Node/*!*/>, HashSet<Node>>());
      } else {
        // original A#:
        //Set<Node> headers = Set{ d : <n,d> in backEdges };
        HashSet<Node> headers = new HashSet<Node>();
        foreach (Tuple<Node/*!*/, Node/*!*/> e in backEdges) {

          Contract.Assert(e.Item1 != null);
          Contract.Assert(e.Item2 != null);
          headers.Add(e.Item2);
        }
        // original A#:
        //Map<Node,Set<Node>> backEdgeNodes = Map{ h -> bs  : h in headers, bs = Set<Node>{ b : <b,x> in backEdges, x == h } };
        Dictionary<Node, HashSet<Node>> backEdgeNodes = new Dictionary<Node, HashSet<Node>>();
        foreach (Node/*!*/ h in headers) {
          Contract.Assert(h != null);
          HashSet<Node> bs = new HashSet<Node>();
          foreach (Tuple<Node, Node> backedge in backEdges) {
            Contract.Assert(backedge.Item1 != null);
            Contract.Assert(backedge.Item2 != null);
            if (backedge.Item2.Equals(h)) {
              bs.Add(backedge.Item1);
            }
          }
          backEdgeNodes.Add(h, bs);
        }

        // original A#:
        //Map<Tuple<Node,Node>,Set<Node>> naturalLoops = Map{ e -> NaturalLoop(g,e) : e in backEdges };
        Dictionary<Tuple<Node/*!*/, Node/*!*/>, HashSet<Node>> naturalLoops = new Dictionary<Tuple<Node/*!*/, Node/*!*/>, HashSet<Node>>();
        foreach (Tuple<Node/*!*/, Node/*!*/> e in backEdges) {
          Contract.Assert(e.Item1 != null && e.Item2 != null);
          naturalLoops.Add(e, NaturalLoop(g, e));
        }

        //Console.WriteLine("[" + DateTime.Now +"]: end ComputeReducible");
        return new ReducibleResult(true, headers, backEdgeNodes, naturalLoops);
      }
    }

    public bool Reducible {
      get {
        return reducible;
      }
    }
    public IEnumerable<Node> Headers {
      get {
        return headers;
      }
    }
    public IEnumerable<Node> BackEdgeNodes(Node/*!*/ h) {
      Contract.Requires(h != null);
      // original A#:
      //return h in backEdgeNodes ? backEdgeNodes[h] : null;
      return (backEdgeNodes.ContainsKey(h) ? backEdgeNodes[h] : (IEnumerable<Node>)new List<Node>());
    }
    public IEnumerable<Node> NaturalLoops(Node/*!*/ header, Node/*!*/ backEdgeNode) {
      Contract.Requires(header != null);
      Contract.Requires(backEdgeNode != null);
      Tuple<Node/*!*/, Node/*!*/> e = new Tuple<Node/*!*/, Node/*!*/>(backEdgeNode, header);
      return naturalLoops.ContainsKey(e) ? naturalLoops[e] : (IEnumerable<Node>)new List<Node>();
    }

    public void ComputeLoops() {
      ReducibleResult r = ComputeReducible(this, this.source);
      this.reducible = r.reducible;
      this.headers = r.headers;
      this.backEdgeNodes = r.backEdgeNodes;
      this.naturalLoops = r.naturalLoops;
      return;
    }

    public IEnumerable<Node> SortHeadersByDominance()
    {
        Graph<Node> dag = new Graph<Node>();
        foreach (Node b in headers)
        {
            dag.AddSource(b);
            foreach (Node c in headers)
            {
                if (b.Equals(c)) continue;
                if (DominatorMap.DominatedBy(b, c))
                {
                    System.Diagnostics.Debug.Assert(!DominatorMap.DominatedBy(c, b));
                    dag.AddEdge(b, c);
                }
            }
        }
        return dag.TopologicalSort();
    }
  } // end: class Graph

  public class GraphProgram {
    static void TestGraph<T>(T/*!*/ source, params Tuple<T/*!*/, T/*!*/>[] edges) {
      Contract.Requires(source != null);
      Contract.Requires(Contract.ForAll(edges, pair => pair.Item1 != null && pair.Item2 != null));
      HashSet<Tuple<T/*!*/, T/*!*/>> es = new HashSet<Tuple<T/*!*/, T/*!*/>>();
      foreach (Tuple<T/*!*/, T/*!*/> e in edges) {
        Contract.Assert(e.Item1 != null && e.Item2 != null);
        es.Add(e);
      }
      Graph<T> g = new Graph<T>(es);
      g.AddSource(source);
      Console.WriteLine("G = " + g);
      g.ComputeLoops();
      Console.WriteLine("G's Dominator Map = " + g.DominatorMap);
      Console.WriteLine("G's Immediate Dominator Map = " + Util.MapToString(g.ImmediateDominatorMap));
      Console.WriteLine("G is reducible: " + (g.Reducible ? "yes" : "no"));
    }

    static void Main(string[] args)
      //requires forall{string s in args; s != null};
    {
      Console.WriteLine("Spec# says hello!");
      // This generates bad IL -- need to fix a bug in the compiler
      //Graph<int> g = new Graph<int>(new Set<Tuple<int,int>>{ new Tuple<int,int>(1,2), new Tuple<int,int>(1,3), new Tuple<int,int>(2,3) });

      Console.WriteLine("");
      TestGraph<char>('a',
        new Tuple<char, char>('a', 'b'),
        new Tuple<char, char>('a', 'c'),
        new Tuple<char, char>('b', 'c')
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Tuple<char, char>('a', 'b'),
        new Tuple<char, char>('a', 'c'),
        new Tuple<char, char>('b', 'd'),
        new Tuple<char, char>('c', 'e'),
        new Tuple<char, char>('c', 'f'),
        new Tuple<char, char>('d', 'e'),
        new Tuple<char, char>('e', 'd'),
        new Tuple<char, char>('e', 'f'),
        new Tuple<char, char>('f', 'e')
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Tuple<char, char>('a', 'b'),
        new Tuple<char, char>('a', 'c'),
        new Tuple<char, char>('b', 'c'),
        new Tuple<char, char>('c', 'b')
      );

      Console.WriteLine("");
      TestGraph<int>(1,
        new Tuple<int, int>(1, 2),
        new Tuple<int, int>(1, 3),
        new Tuple<int, int>(2, 3)
      );

      Console.WriteLine("");
      TestGraph<int>(1,
        new Tuple<int, int>(1, 2),
        new Tuple<int, int>(1, 3),
        new Tuple<int, int>(2, 3),
        new Tuple<int, int>(3, 2)
      );

      Console.WriteLine("");
      TestGraph<int>(2,
        new Tuple<int, int>(2, 3),
        new Tuple<int, int>(2, 4),
        new Tuple<int, int>(3, 2)
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Tuple<char, char>('a', 'b'),
        new Tuple<char, char>('a', 'c'),
        new Tuple<char, char>('b', 'c'),
        new Tuple<char, char>('b', 'b')
      );


    }
  }

}
