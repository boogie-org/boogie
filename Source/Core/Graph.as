using System.Collections;
namespace Graphing;

type Node = object;
type Edge = <Node,Node>;

class PreHeader {
  Node myHeader;
  PreHeader(Node h) { myHeader = h; }
  
  public override string ToString() { return "#" + myHeader.ToString(); }
}

public class Graph {
  private Set<Edge> es;
  private Set<Node> ns;
  private Node source;
  private bool reducible;
  private Set<Node> headers;
  private Map<Node,Set<Node>> backEdgeNodes;
  private Map<Edge,Set<Node>> naturalLoops;
  private Map<Node,Set<Node>> dominatorMap;
  private Map<Node,Set<Node>> immediateDominatorMap;
 
  public Graph(Set<Edge> edges)
  {
    es = edges;
    ns = Set<Node>{ x : <x,y> in es } + Set<Node>{ y : <x,y> in es };
  }
  public Graph()
  { es = Set<Edge>{}; ns = Set<Node>{}; } 
  
  public void AddSource(Node x)
  {
    ns += Set<Node>{x};
    source = x;
  }
  public void AddEdge(Node source, Node dest)
  {
    es += Set<Edge>{<source,dest>};
    ns += Set<Node>{source, dest};
  }
  
  public Set<Node> Nodes { get { return ns; } }
  public Set<Edge> Edges { get { return es; } }
  
  public bool Edge(Node x, Node y) { return <x,y> in es; }  
  Set<Node> predecessors(Node n)
  {
    Set<Node> result = Set{ x : x in Nodes, Edge(x,n) };
    return result;
  }
  public override string ToString() { return es.ToString(); }
  
  public IEnumerable TopologicalSort()
  {
    <bool,Seq<Node>> <res,ns> = TopSort(this);
    return  res ? ns : null;
  }
  public void ComputeLoops()
  {
     <bool, Set<Node>, Map<Node,Set<Node>>, Map<Edge,Set<Node>>>
       <reducible,headers,backEdgeNodes,naturalLoops> = Reducible(this,this.source);
       this.reducible = reducible;
       this.headers = headers;
       this.backEdgeNodes = backEdgeNodes;
       this.naturalLoops = naturalLoops;
     return;
  }
  public bool Reducible { get { return reducible; } }
  public IEnumerable Headers { get { return headers; } }
  public IEnumerable BackEdgeNodes(Node h) { return h in backEdgeNodes ? backEdgeNodes[h] : null; }
  public IEnumerable NaturalLoops(Node header, Node backEdgeNode)
  {  Edge e = <backEdgeNode,header>; return e in naturalLoops ? naturalLoops[e] : null; }
  public bool Acyclic { get { return Acyclic(this,this.source); } }
  public Map<Node,Set<Node>> DominatorMap
  {
    get { 
      if (dominatorMap == null) dominatorMap = ComputeDominators(this, source);
      return dominatorMap;
    }
  }
  public Map<Node,Set<Node>> ImmediateDominatorMap
  {
    get { 
      if (immediateDominatorMap == null)
      {
        immediateDominatorMap = Map{};
        foreach(Node y in Nodes)
        {
          Set<Node> nodesThatYDominates = Set{ x : x in Nodes, x != y && (y in DominatorMap[x]) };
          Set<Node> immediateDominatees = Set{ x : x in nodesThatYDominates,
                                                  !(Exists{ v != y && v != x && (v in DominatorMap[x]) : v in nodesThatYDominates })
                                               };
          immediateDominatorMap[y] = immediateDominatees;
        }
      }
      return immediateDominatorMap;
    }
  }
  public Set<Node> ImmediatelyDominatedBy(Node n) { return ImmediateDominatorMap[n]; }

}

// From AsmL distribution example: TopologicalSort
<bool,Seq<Node>> TopSort(Graph g)
{
  Seq<Node> S = Seq{};
  Set<Node> V = g.Nodes;
  bool change = true;
  while ( change )
  {
    change = false;
    Set<Node> X = V - ((Set<Node>) S);
    if ( X != Set{} )
    {
      Node temp = Choose{ v : v in X, !(Exists{ g.Edge(u,v) : u in X }) ifnone null };
      if ( temp == null )
      {
        return <false,Seq<Node>{}>;
      }
      else if ( temp != Seq<Node>{} )
      {
        S += Seq{temp};
        change = true;
      }
    }
  }
  return <true,S>;
}

bool Acyclic(Graph g, Node source)
{
  <bool,Seq<Node>> <acyc,xs> = TopSort(g);
  return acyc;
}

//
// [Dragon, pp. 670--671]
// returns map D s.t. d in D(n) iff d dom n
//
Map<Node,Set<Node>> ComputeDominators(Graph g, Node source) {
  Set<Node> N = g.Nodes;
  Set<Node> nonSourceNodes = N - Set{source};
  Map<Node,Set<Node>> D = Map{};
  D[source] = Set<Node>{ source };
  foreach (Node n in nonSourceNodes)
  {
    D[n] = N;
  }
  bool change = true;
  while ( change )
  {
    change = false;
    foreach (Node n in nonSourceNodes)
    {
      Set<Set<Node>> allPreds = Set{ D[p] : p in g.predecessors(n) };
      Set<Node> temp = Set<Node>{ n } + BigIntersect(allPreds);
      if ( temp != D[n] )
      {
        change = true;
        D[n] = temp;
      }
    }
  }
  return D;
}

// [Dragon, Fig. 10.15, p. 604. Algorithm for constructing the natural loop.]
Set<Node> NaturalLoop(Graph g, Edge backEdge)
{
  <Node,Node> <n,d> = backEdge;
  Seq<Node> stack = Seq{};
  Set<Node> loop = Set{ d };
  if ( n != d ) // then n is not in loop
  {
    loop += Set{ n };
    stack = Seq{ n } + stack; // push n onto stack
  }
  while ( stack != Seq{} ) // not empty
  {
    Node m = Head(stack);
    stack = Tail(stack); // pop stack
    foreach (Node p in g.predecessors(m))
    {
      if ( !(p in loop) )
      {
        loop += Set{ p };
        stack = Seq{ p } + stack; // push p onto stack
      }
    }
  }
  return loop;
}

// [Dragon, p. 606]
<bool, Set<Node>, Map<Node,Set<Node>>, Map<Edge,Set<Node>>>
  Reducible(Graph g, Node source) {
  // first, compute the dom relation
  Map<Node,Set<Node>> D = g.DominatorMap;
  return Reducible(g,source,D);
}

// [Dragon, p. 606]
<bool, Set<Node>, Map<Node,Set<Node>>, Map<Edge,Set<Node>>>
  Reducible(Graph g, Node source, Map<Node,Set<Node>> DomRelation) {

  Set<Edge> edges = g.Edges;
  Set<Edge> backEdges = Set{};
  Set<Edge> nonBackEdges = Set{};
  foreach (Edge e in edges)
  {
    <Node,Node> <x,y> = e; // so there is an edge from x to y
    if ( y in DomRelation[x] ) // y dom x: which means y dominates x
    {
      backEdges += Set{ e };
    }
    else
    {
      nonBackEdges += Set{ e };
    }
  }
  if ( !Acyclic(new Graph(nonBackEdges), source) )
  {
    return <false,Set<Node>{},Map<Node,Set<Node>>{},Map<Edge,Set<Node>>{}>;
  }
  else
  {
    Set<Node> headers = Set{ d : <n,d> in backEdges };
    Map<Node,Set<Node>> backEdgeNodes = Map{ h -> bs  : h in headers, bs = Set<Node>{ b : <b,x> in backEdges, x == h } };
    Map<Edge,Set<Node>> naturalLoops = Map{ e -> NaturalLoop(g,e) : e in backEdges };
     
    return <true, headers, backEdgeNodes, naturalLoops>;
  }
}
  
// [Dragon, p. 606]
bool OldReducible(Graph g, Node source) {
  // first, compute the dom relation
  Map<Node,Set<Node>> D = ComputeDominators(g, source);
  return OldReducible(g,source,D);
}

// [Dragon, p. 606]
bool OldReducible(Graph g, Node source, Map<Node,Set<Node>> DomRelation) {

  Set<Edge> edges = g.Edges;
  Set<Edge> backEdges = Set{};
  Set<Edge> nonBackEdges = Set{};
  foreach (Edge e in edges)
  {
    <Node,Node> <x,y> = e;
    if ( y in DomRelation[x] ) // y dom x
    {
      backEdges += Set{ e };
    }
    else
    {
      nonBackEdges += Set{ e };
    }
  }
  WriteLine("backEdges: " + backEdges);
  WriteLine("nonBackEdges: " + nonBackEdges);
  if ( Acyclic(new Graph(nonBackEdges), source) )
  {
    foreach(Edge e in backEdges)
    {
      Set<Node> naturalLoop = NaturalLoop(g,e);
      WriteLine("Natural loop for back edge '" + e + "' is: " + naturalLoop);
    }
    Set<Node> headers = Set{ d : <n,d> in backEdges };
    WriteLine("Loop headers = " + headers);
     
    edges -= backEdges; // this cuts all of the back edges
    foreach (Node h in headers)
    {
      Set<Edge> bs = Set{ <n,d> : <n,d> in backEdges, d == h };
      Set<Node> preds = Set<Node>{ p : <p,y> in edges, y == h };
      Node preheader = new PreHeader(h);
      edges += Set{ <preheader,h> };
      foreach (Node p in preds)
      {
        edges -= Set{ <p,h> };
        edges += Set{ <p,preheader> };
      }
    }
    Graph newGraph = new Graph(edges);
    WriteLine("transformed graph = " + newGraph);
    return true;
  }
  else
  {
    return false;
  }
}

void Main()
{
   Graph g;
   Map<Node,Set<Node>> D;
/*   
   g = new Graph(Set<Edge>{ <1,2>, <1,3>, <2,3> });
   g.AddSource(1);
  Map<Node,Set<Node>> doms = ComputeDominators(g,1);
   WriteLine(doms); 
*/
   g = new Graph(Set<Edge>{
          <1,2>, <1,3>,
          <2,3>,
          <3,4>,
          <4,3>, <4,5>, <4,6>,
          <5,7>,
          <6,7>,
          <7,4>, <7,8>,
          <8,3>, <8,9>, <8,10>,
          <9,1>,
          <10,7>
          });
   g.AddSource(1);
   WriteLine("G = " + g);
   D = ComputeDominators(g,1);
   WriteLine("Dom relation: " + D); 
   WriteLine("G's Dominator Map = " + g.DominatorMap);
   WriteLine("G's Immediate Dominator Map = " + g.ImmediateDominatorMap);
   WriteLine("G is reducible: " + OldReducible(g,1,D));
   g.ComputeLoops();
   
   WriteLine("");
   
   g = new Graph(Set<Edge>{ <1,2>, <1,3>, <2,3>, <3,2> });
   g.AddSource(1);
   WriteLine("G = " + g);
   D = ComputeDominators(g,1);
   WriteLine("Dom relation: " + D); 
   WriteLine("G's Dominator Map = " + g.DominatorMap);
   WriteLine("G's Immediate Dominator Map = " + g.ImmediateDominatorMap);
   WriteLine("G is reducible: " + OldReducible(g,1,D));
   g.ComputeLoops();
 
    WriteLine("");
   
   g = new Graph(Set<Edge>{ <1,2>, <2,3>, <2,4>, <3,2> });
   g.AddSource(1);
   WriteLine("G = " + g);
   WriteLine("G's Dominator Map = " + g.DominatorMap);
   WriteLine("G's Immediate Dominator Map = " + g.ImmediateDominatorMap);
//   D = ComputeDominators(g,1);
//   WriteLine("Dom relation: " + D); 
//   WriteLine("G is reducible: " + OldReducible(g,1,D));
   g.ComputeLoops();
  
}