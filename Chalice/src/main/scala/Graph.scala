//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

/**
 * Graph algorithms
 */
package chalice;
import scala.collection.mutable;
import scala.collection.immutable;

// Directed simple graph on T. Payload of nodes (of type T) should remain immutable while in graph.
class DiGraph[T] {
  private class Node[T](t: T) {
    val data: T = t;
    var children = mutable.Set.empty[Node[T]];

    // temporary variables
    var index = -1;
    var lowlink = -1;
    var onstack = false;
  }

  private var rep = mutable.Map.empty[T, Node[T]];

  def addNode(t: T) = {
    if (hasNode(t))
      false;
    else {
      rep(t) = new Node(t);
      true;
    }
  }

  def addEdge(a: T, b: T) = {
    assert (hasNode(a));
    assert (hasNode(b));
    if (rep(a).children.contains(rep(b)))
      false
    else {
      rep(a).children += rep(b);
      true;
    }
  }

  def hasNode(a: T) = rep contains a;

  def nodes: immutable.Set[T] =
    immutable.Set() ++ rep.keys
  
  def children(t: T): immutable.Set[T] = {
    assert (rep contains t);
    immutable.Set() ++ (rep(t).children map {x => x.data})
  }

  // Compute topological sort (edges point in forward direction in the list)
  // Terminates but incorrect if not a DAG.
  def computeTopologicalSort: List[T] = {
    rep.values foreach {v => assert(!v.onstack)}
    var l: List[T] = Nil;

    def tarjan(v: Node[T]) {
      if (! v.onstack) {
        v.onstack = true;
        for (w <- v.children) tarjan(w)
        l = v.data :: l;
      }
    }

    rep.values foreach {v => tarjan(v)}
    rep.values foreach {v => assert(v.onstack); v.onstack = false;}
    l
  }
  
  // Compute condensation of the digraph.
  // The resulting digraph has no self loops
  def computeSCC: (DiGraph[List[T]],mutable.Map[T,List[T]]) = {
    // Tarjan's algorithm for finding strongly connected components
    // http://algowiki.net/wiki/index.php/Tarjan%27s_algorithm
    rep.values foreach {x => assert(x.index == -1 && x.lowlink == -1 && !x.onstack)};

    // morphism
    val result = new DiGraph[List[T]];
    val map = mutable.Map.empty[T,List[T]];

    // algorithm
    var index = 0;
    var S:List[Node[T]] = Nil;
    
    def tarjan(v: Node[T]) {
      v.index = index;
      v.lowlink = index;
      index = index + 1;
      S = v :: S; v.onstack = true;
      for (w <- v.children) {
        if (w.index == -1) {
          tarjan(w);
          v.lowlink = scala.math.min(v.lowlink, w.lowlink);
        } else if (w.onstack)
          v.lowlink = scala.math.min(v.lowlink, w.index);
      }

      if (v.lowlink == v.index) {
        var scc:List[T] = Nil;
        var w: Node[T] = null;
        while (v != w) {
          w = S.head;
          S = S.tail; w.onstack = false;
          scc = w.data :: scc;
        }
        result.addNode(scc);
        scc foreach {t => map(t) = scc}
      }
    }

    // compute SCCs
    rep.values foreach {n => if(n.index == -1) tarjan(n)};

    // compute SCCs edges
    rep.values foreach {n => n.children foreach {m =>
        if (map(n.data) != map(m.data))
          result.addEdge(map(n.data), map(m.data))
        }
      }

    // clean-up
    rep.values foreach {x => x.index = -1; x.lowlink = -1; x.onstack = false};
    (result,map);
  }
}

object Test {
  def main(args: Array[String]) {
    val g = new DiGraph[Int];
    assert(g.addNode(0));
    assert(!g.addNode(0));
    assert(g.addNode(1));
    assert(g.addNode(2));
    assert(g.addNode(3));
    assert(g.addNode(4));
    assert(g.addNode(5));
    g.addEdge(0,1);
    g.addEdge(0,1);
    g.addEdge(0,2);
    assert(g.children(0) == Set(1,2));
    g.addEdge(1,1);
    g.addEdge(2,3);
    g.addEdge(3,4);
    g.addEdge(3,5);
    g.addEdge(5,4);
    g.addEdge(4,2);
    g.computeSCC;
    val (d, h) = g.computeSCC;
    assert(h.get(0).get == List(0));
    assert(h.get(1).get == List(1));
    assert(h.get(2).get.size == 4);
    assert(h.get(3).get.size == 4);
    assert(h.get(4).get.size == 4);
    assert(h.get(5).get.size == 4);
    assert(d.children(h.get(0).get) == Set(h.get(1).get, h.get(2).get));
    assert(d.children(h.get(1).get) == Set());
    assert(d.children(h.get(2).get) == Set());
  }
}