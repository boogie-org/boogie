//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using Microsoft.SpecSharp.Collections;
using Microsoft.Contracts;
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
        sb.Append(cce.NonNull(de.Key).ToString());
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
        sb.Append(cce.NonNull(de.Key).ToString());
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
      Dictionary<Node, bool> visited = new Dictionary<Node, bool>(n);
      int currentNumber = 1;
      Contract.Assume(this.source != null);
      this.PostOrderVisit(this.source, visited, ref currentNumber);
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
    private void PostOrderVisit(Node/*!*/ n, Dictionary<Node, bool> visited, ref int currentNumber) {
      Contract.Requires(n != null);
      if (visited.ContainsKey(n))
        return;
      visited[n] = true;
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
  }
  public class Graph<Node> {
    private Set<Pair<Node/*!*/, Node/*!*/>> es;
    private Set<Node> ns;
    private Node source;
    private bool reducible;
    private Set<Node> headers;
    private Map<Node, Set<Node>> backEdgeNodes;
    private Map<Pair<Node/*!*/, Node/*!*/>, Set<Node>> naturalLoops;

    private DomRelation<Node> dominatorMap = null;
    private Dictionary<Node, Set<Node>> predCache = new Dictionary<Node, Set<Node>>();
    private Dictionary<Node, Set<Node>> succCache = new Dictionary<Node, Set<Node>>();
    private bool predComputed;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(es == null || Contract.ForAll(es, p => p.First != null && p.Second != null));
      Contract.Invariant(naturalLoops == null || Contract.ForAll(naturalLoops.Keys, p => p.Second != null && p.First != null));
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

    public Graph(Set<Pair<Node/*!*/, Node/*!*/>> edges) {

      Contract.Requires(cce.NonNullElements(edges) && Contract.ForAll(edges, p => p.First != null && p.Second != null));
      es = edges;

      // original A#
      //ns = Set<Node>{ x : <x,y> in es } + Set<Node>{ y : <x,y> in es };

      // closest Spec#
      //ns = new Set<Node>{ Pair<Node,Node> p in edges; p.First } + new Set<Node>{ Pair<Node,Node> p in edges; p.Second };

      // 
      Set<Node> temp = new Set<Node>();
      foreach (Pair<Node/*!*/, Node/*!*/> p in edges) {
        Contract.Assert(p.First != null);
        temp.Add(p.First);
        Contract.Assert(p.Second != null);
        temp.Add(p.Second);
      }
      ns = temp;
    }
    public Graph() {
      es = new Set<Pair<Node/*!*/, Node/*!*/>>();
      ns = new Set<Node>();
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
      es.Add(new Pair<Node/*!*/, Node/*!*/>(source, dest));
      ns.Add(source);
      ns.Add(dest);
      predComputed = false;
    }

    public Set<Node> Nodes {
      get {
        return ns;
      }
    }
    public IEnumerable<Pair<Node/*!*/, Node/*!*/>> Edges {
      get {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Pair<Node, Node>>>())
          && Contract.ForAll(Contract.Result<IEnumerable<Pair<Node, Node>>>(), n =>
          n.First != null && n.Second != null));
        return es;
      }
    }

    public bool Edge(Node/*!*/ x, Node/*!*/ y) {
      Contract.Requires(x != null);
      Contract.Requires(y != null);
      // original A#
      // return <x,y> in es;
      return es.Contains(new Pair<Node/*!*/, Node/*!*/>(x, y));
    }

    private void ComputePredSuccCaches() {
      if (predComputed)
        return;
      predComputed = true;
      predCache = new Dictionary<Node, Set<Node>>();
      succCache = new Dictionary<Node, Set<Node>>();

      foreach (Node n in Nodes) {
        predCache[n] = new Set<Node>();
        succCache[n] = new Set<Node>();
      }

      foreach (Pair<Node/*!*/, Node/*!*/> p in Edges) {
        Contract.Assert(p.First != null);
        Contract.Assert(p.Second != null);
        Set<Node> tmp;

        tmp = predCache[p.Second];
        tmp.Add(p.First);
        predCache[p.Second] = tmp;

        tmp = succCache[p.First];
        tmp.Add(p.Second);
        succCache[p.First] = tmp;
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
      foreach (Pair<Node/*!*/, Node/*!*/> e in this.Edges) {
        Contract.Assert(e.First != null);
        Contract.Assert(e.Second != null);
        Node/*!*/ target = e.Second;
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
      Pair<bool, Seq<Node>> result = this.TopSort();
      return result.First ? result.Second : (IEnumerable<Node>)new Seq<Node>();
    }
    // From AsmL distribution example
    private Pair<bool, Seq<Node>> TopSort() {
      Seq<Node> S = new Seq<Node>();
      Set<Node> V = this.Nodes;
      Set<Node> X = new Set<Node>();
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
            return new Pair<bool, Seq<Node>>(false, new Seq<Node>());
          }
        }
      }
      return new Pair<bool, Seq<Node>>(true, S);
    }

    public static bool Acyclic(Graph<Node> g, Node source) {
      bool acyclic;
      List<Node> sortedList;
      g.TarjanTopSort(out acyclic, out sortedList);
      return acyclic;
    }

    //
    // [Dragon, pp. 670--671]
    // returns map D s.t. d in D(n) iff d dom n
    //
    static private Map<Node, Set<Node>> OldComputeDominators(Graph<Node> g, Node/*!*/ source) {
      Contract.Requires(source != null);
      Contract.Assert(g.source != null);
      Set<Node> N = g.Nodes;
      Set<Node> nonSourceNodes = N - new Set<Node>(source);
      Map<Node, Set<Node>> D = new Map<Node, Set<Node>>();
      D[source] = new Set<Node>(source);
      foreach (Node/*!*/ n in nonSourceNodes) {
        Contract.Assert(n != null);
        D[n] = N;
      }
      bool change = true;
      while (change) {
        change = false;
        foreach (Node/*!*/ n in nonSourceNodes) {
          Contract.Assert(n != null);

          // original A#
          //Set<Set<Node>> allPreds = new Set<Set<Node>>{ Node p in this.Predecessors(n) ; D[p] };

          Set<Set<Node>> allPreds = new Set<Set<Node>>();
          foreach (Node/*!*/ p in g.Predecessors(n)) {
            Contract.Assert(p != null);
            allPreds.Add(D[p]);
          }
          Set<Node> temp = new Set<Node>(n) + Set<Node>.BigIntersect(allPreds);
          if (temp != D[n]) {
            change = true;
            D[n] = temp;
          }
        }
      }
      return D;
    }

    // [Dragon, Fig. 10.15, p. 604. Algorithm for constructing the natural loop.]
    static Set<Node> NaturalLoop(Graph<Node> g, Pair<Node/*!*/, Node/*!*/> backEdge) {
      Contract.Requires(backEdge.First != null && backEdge.Second != null);
      Node/*!*/ n = backEdge.First;
      Node/*!*/ d = backEdge.Second;
      Seq<Node> stack = new Seq<Node>();
      Set<Node> loop = new Set<Node>(d);
      if (!n.Equals(d)) // then n is not in loop
    {
        loop.Add(n);
        stack = new Seq<Node>(n) + stack; // push n onto stack
      }
      while (stack.Count > 0) // not empty
    {
        Node m = stack.Head;
        stack = stack.Tail; // pop stack
        foreach (Node/*!*/ p in g.Predecessors(m)) {
          Contract.Assert(p != null);
          if (!(loop.Contains(p))) {
            loop.Add(p);
            stack = new Seq<Node>(p) + stack; // push p onto stack
          }
        }
      }
      return loop;
    }

    internal struct ReducibleResult {
      internal bool reducible;
      internal Set<Node> headers;
      internal Map<Node, Set<Node>> backEdgeNodes;
      internal Map<Pair<Node/*!*/, Node/*!*/>, Set<Node>> naturalLoops;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Contract.ForAll(naturalLoops.Keys, p => p.First != null && p.Second != null));
      }

      internal ReducibleResult(bool b, Set<Node> headers, Map<Node, Set<Node>> backEdgeNodes, Map<Pair<Node/*!*/, Node/*!*/>, Set<Node>> naturalLoops) {
        Contract.Requires(naturalLoops == null || Contract.ForAll(naturalLoops.Keys, Key => Key.First != null && Key.Second != null));
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
      IEnumerable<Pair<Node/*!*/, Node/*!*/>> edges = g.Edges;
      Contract.Assert(Contract.ForAll(edges, n => n.First != null && n.Second != null));
      Set<Pair<Node/*!*/, Node/*!*/>> backEdges = new Set<Pair<Node/*!*/, Node/*!*/>>();
      Set<Pair<Node/*!*/, Node/*!*/>> nonBackEdges = new Set<Pair<Node/*!*/, Node/*!*/>>();
      foreach (Pair<Node/*!*/, Node/*!*/> e in edges) {
        Contract.Assert(e.First != null);
        Contract.Assert(e.Second != null);
        Node x = e.First;
        Node y = e.Second; // so there is an edge from x to y
        if (DomRelation.DominatedBy(x, y)) { // y dom x: which means y dominates x
          backEdges.Add(e);
        } else {
          nonBackEdges.Add(e);
        }
      }
      if (!Acyclic(new Graph<Node>(nonBackEdges), source)) {
        return new ReducibleResult(false,
                                   new Set<Node>(),
                                   new Map<Node, Set<Node>>(),
                                   new Map<Pair<Node/*!*/, Node/*!*/>, Set<Node>>());
      } else {
        // original A#:
        //Set<Node> headers = Set{ d : <n,d> in backEdges };
        Set<Node> headers = new Set<Node>();
        foreach (Pair<Node/*!*/, Node/*!*/> e in backEdges) {

          Contract.Assert(e.First != null);
          Contract.Assert(e.Second != null);
          headers.Add(e.Second);
        }
        // original A#:
        //Map<Node,Set<Node>> backEdgeNodes = Map{ h -> bs  : h in headers, bs = Set<Node>{ b : <b,x> in backEdges, x == h } };
        Map<Node, Set<Node>> backEdgeNodes = new Map<Node, Set<Node>>();
        foreach (Node/*!*/ h in headers) {
          Contract.Assert(h != null);
          Set<Node> bs = new Set<Node>();
          foreach (Pair<Node, Node> backedge in backEdges) {
            Contract.Assert(backedge.First != null);
            Contract.Assert(backedge.Second != null);
            if (backedge.Second.Equals(h)) {
              bs.Add(backedge.First);
            }
          }
          backEdgeNodes.Add(h, bs);
        }

        // original A#:
        //Map<Pair<Node,Node>,Set<Node>> naturalLoops = Map{ e -> NaturalLoop(g,e) : e in backEdges };
        Map<Pair<Node/*!*/, Node/*!*/>, Set<Node>> naturalLoops = new Map<Pair<Node/*!*/, Node/*!*/>, Set<Node>>();
        foreach (Pair<Node/*!*/, Node/*!*/> e in backEdges) {
          Contract.Assert(e.First != null && e.Second != null);
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
      return (backEdgeNodes.ContainsKey(h) ? backEdgeNodes[h] : (IEnumerable<Node>)new Seq<Node>());
    }
    public IEnumerable<Node> NaturalLoops(Node/*!*/ header, Node/*!*/ backEdgeNode) {
      Contract.Requires(header != null);
      Contract.Requires(backEdgeNode != null);
      Pair<Node/*!*/, Node/*!*/> e = new Pair<Node/*!*/, Node/*!*/>(backEdgeNode, header);
      return naturalLoops.ContainsKey(e) ? naturalLoops[e] : (IEnumerable<Node>)new Seq<Node>();
    }

    public void ComputeLoops() {
      ReducibleResult r = ComputeReducible(this, this.source);
      this.reducible = r.reducible;
      this.headers = r.headers;
      this.backEdgeNodes = r.backEdgeNodes;
      this.naturalLoops = r.naturalLoops;
      return;
    }


  } // end: class Graph

  public class GraphProgram {
    static void TestGraph<T>(T/*!*/ source, params Pair<T/*!*/, T/*!*/>[] edges) {
      Contract.Requires(source != null);
      Contract.Requires(Contract.ForAll(edges, pair => pair.First != null && pair.Second != null));
      Set<Pair<T/*!*/, T/*!*/>> es = new Set<Pair<T/*!*/, T/*!*/>>();
      foreach (Pair<T/*!*/, T/*!*/> e in edges) {
        Contract.Assert(e.First != null && e.Second != null);
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
      //Graph<int> g = new Graph<int>(new Set<Pair<int,int>>{ new Pair<int,int>(1,2), new Pair<int,int>(1,3), new Pair<int,int>(2,3) });

      Console.WriteLine("");
      TestGraph<char>('a',
        new Pair<char, char>('a', 'b'),
        new Pair<char, char>('a', 'c'),
        new Pair<char, char>('b', 'c')
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Pair<char, char>('a', 'b'),
        new Pair<char, char>('a', 'c'),
        new Pair<char, char>('b', 'd'),
        new Pair<char, char>('c', 'e'),
        new Pair<char, char>('c', 'f'),
        new Pair<char, char>('d', 'e'),
        new Pair<char, char>('e', 'd'),
        new Pair<char, char>('e', 'f'),
        new Pair<char, char>('f', 'e')
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Pair<char, char>('a', 'b'),
        new Pair<char, char>('a', 'c'),
        new Pair<char, char>('b', 'c'),
        new Pair<char, char>('c', 'b')
      );

      Console.WriteLine("");
      TestGraph<int>(1,
        new Pair<int, int>(1, 2),
        new Pair<int, int>(1, 3),
        new Pair<int, int>(2, 3)
      );

      Console.WriteLine("");
      TestGraph<int>(1,
        new Pair<int, int>(1, 2),
        new Pair<int, int>(1, 3),
        new Pair<int, int>(2, 3),
        new Pair<int, int>(3, 2)
      );

      Console.WriteLine("");
      TestGraph<int>(2,
        new Pair<int, int>(2, 3),
        new Pair<int, int>(2, 4),
        new Pair<int, int>(3, 2)
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Pair<char, char>('a', 'b'),
        new Pair<char, char>('a', 'c'),
        new Pair<char, char>('b', 'c'),
        new Pair<char, char>('b', 'b')
      );


    }
  }

}
