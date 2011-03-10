//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie {
  public delegate System.Collections.IEnumerable/*<Node!>*//*!*/ Adjacency<T>(T/*!*/ node);


  // An SCC is a set of nodes
  public sealed class SCC<Node> : ICollection<Node> {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(nodesMap != null);
    }

    private IDictionary<Node, object>/*!*/ nodesMap = new Dictionary<Node, object>();
    private ICollection<Node>/*!*/ nodes {
      get {
        return cce.NonNull(nodesMap.Keys);
      }
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    System.Collections.IEnumerator/*!*/ System.Collections.IEnumerable.GetEnumerator() {
      Contract.Ensures(Contract.Result<System.Collections.IEnumerator>() != null);

      return ((System.Collections.IEnumerable)nodes).GetEnumerator();
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IEnumerator<Node>/*!*/ IEnumerable<Node>.GetEnumerator() {
      Contract.Ensures(Contract.Result<IEnumerator<Node>>() != null);

      return ((IEnumerable<Node>)nodes).GetEnumerator();
    }

    public int Count {
      get {
        return nodes.Count;
      }
    }
    public bool IsReadOnly {
      get {
        return nodesMap.IsReadOnly;
      }
    }
    public void Add(Node item) {
      nodesMap.Add(item, null);
    }
    public void Clear() {
      nodesMap.Clear();
    }
    [Pure]
    public bool Contains(Node item) {
      return nodesMap.ContainsKey(item);
    }
    public void CopyTo(Node[] array, int arrayIndex) {
      //Contract.Requires(array != null);
      nodes.CopyTo(array, arrayIndex);
    }
    public bool Remove(Node item) {
      return nodesMap.Remove(item);
    }
  }

  public sealed class StronglyConnectedComponents<Node> : IEnumerable<SCC<Node>/*!*/> where Node : class {
    private readonly IDictionary<Node/*!*/, object>/*!*/ graph;
    [ContractInvariantMethod]
    void graphInvariantMethod() {
      Contract.Invariant(Contract.ForAll(graph, entry => entry.Key != null));
      Contract.Invariant(preds != null);
      Contract.Invariant(succs != null);
    }
    private readonly Adjacency<Node>/*!*/ preds;
    private readonly Adjacency<Node>/*!*/ succs;

    private bool computed = false;
    public bool Computed {
      get {
        return computed;
      }
    }

    [NotDelayed]
    public StronglyConnectedComponents(System.Collections.IEnumerable/*<Node!>*/ graph, Adjacency<Node> preds, Adjacency<Node> succs)
      : base() {//BASEMOVE DANGER
      Contract.Requires(succs != null);
      Contract.Requires(preds != null);
      Contract.Requires(graph != null);
      Contract.Ensures(!Computed);
      IDictionary<Node/*!*/, object>/*!*/ dict = new Dictionary<Node/*!*/, object>();
      foreach (Node/*!*/ n in graph) {
        Contract.Assert(n != null);
        dict.Add(n, null);
      }

      this.graph = dict;
      this.preds = preds;
      this.succs = succs;
      //:base();
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    System.Collections.IEnumerator/*!*/ System.Collections.IEnumerable.GetEnumerator() {
      Contract.Ensures(Contract.Result<System.Collections.IEnumerator>() != null);

      return ((System.Collections.IEnumerable)sccs).GetEnumerator();
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IEnumerator<SCC<Node>/*!*/>/*!*/ IEnumerable<SCC<Node>/*!*/>.GetEnumerator() {
      Contract.Ensures(Contract.Result<IEnumerator<SCC<Node>>>() != null);

      Contract.Assume(Computed);
      Contract.Assert(cce.NonNullElements((IEnumerable<SCC<Node>/*!*/>)sccs));//REVIEW
      return ((IEnumerable<SCC<Node>/*!*/>)sccs).GetEnumerator();
    }

    private readonly IList<SCC<Node>/*!*/>/*!*/ sccs = new List<SCC<Node>/*!*/>();
    [ContractInvariantMethod]
    void sccsInvariant() {
      Contract.Invariant(cce.NonNullElements(sccs));
    }


    public void Compute() {
      Contract.Requires(!Computed);
      Contract.Ensures(Computed);
      // Compute post times on graph with edges reversed
      this.dfsNext = this.preds;
      foreach (Node/*!*/ n in cce.NonNull(graph.Keys)) {
        Contract.Assert(n != null);
        if (!seen.ContainsKey(n)) {
          OrderNodes(n);
        }
      }

      // Clear seen
      seen.Clear();

      // Compute SCCs
      this.dfsNext = this.succs;
      while (postOrder.Count > 0) {
        Node/*!*/ n = postOrder.Pop();
        Contract.Assert(n != null);

        if (!seen.ContainsKey(n)) {
          SCC<Node>/*!*/ curr = new SCC<Node>();
          FindSCCs(n, curr);
          sccs.Add(curr);
        }
      }

      // Clear seen
      seen.Clear();

      this.computed = true;
    }

    private Adjacency<Node>/*?*/ dfsNext = null;

    private readonly IDictionary<Node/*!*/, object>/*!*/ seen = new Dictionary<Node/*!*/, object>();
    private readonly Stack<Node/*!*/>/*!*/ postOrder = new Stack<Node/*!*/>();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(seen != null);
      Contract.Invariant(cce.NonNullElements(postOrder));
    }


    // DFS to order nodes by post times
    private void OrderNodes(Node node) {
      Contract.Requires(node != null);
      seen.Add(node, null);

      Contract.Assert(dfsNext != null);
      System.Collections.IEnumerable/*!*/ nexts = dfsNext(node);
      Contract.Assert(nexts != null);
      foreach (Node/*!*/ n in nexts) {
        Contract.Assert(n != null);
        if (graph.ContainsKey(n) && !seen.ContainsKey(n)) {
          OrderNodes(n);
        }
      }

      postOrder.Push(node);
    }

    // DFS to compute SCCs
    private void FindSCCs(Node node, SCC<Node> currSCC) {
      Contract.Requires(currSCC != null);
      Contract.Requires(node != null);
      //modifies currSCC.*;
      seen.Add(node, null);
      currSCC.Add(node);

      Contract.Assert(dfsNext != null);
      System.Collections.IEnumerable/*!*/ nexts = dfsNext(node);
      Contract.Assert(nexts != null);
      foreach (Node/*!*/ n in nexts) {
        Contract.Assert(n != null);
        if (graph.ContainsKey(n) && !seen.ContainsKey(n)) {
          FindSCCs(n, currSCC);
        }
      }
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      string outStr = "";
      int i = 0;

      foreach (ICollection<Node> component in this) {
        string/*!*/ tmp = System.String.Format("\nComponent #{0} = ", i++);
        Contract.Assert(tmp != null);
        outStr += tmp;

        bool firstInRow = true;

        foreach (Node b in component) {
          string/*!*/ tmpComponent = System.String.Format("{0}{1}", firstInRow ? "" : ", ", b);
          Contract.Assert(tmpComponent != null);
          outStr += tmpComponent;
          firstInRow = false;
        }
      }
      return outStr;
    }

  }
}
