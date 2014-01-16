type lmap;
function dom(lmap) : [int]bool;
function map(lmap): [int]int;

procedure Load({:linear "Node"} l:lmap, i:int) returns({:linear "Node"} l':lmap, v:int);
  requires dom(l)[i];
  ensures  l' == l;
  ensures  v == map(l)[i];

procedure Store({:linear "Node"} l:lmap, i:int, v:int) returns({:linear "Node"} l':lmap);
  requires dom(l)[i];
  ensures  dom(l') == dom(l);
  ensures  map(l') == map(l)[i := v];

procedure Transfer({:linear "Node"} l1:lmap, {:linear "Node"} l2:lmap, d:int) returns({:linear "Node} l1':lmap, {:linear "Node"} l2':lmap);
  requires dom(l1)[i];
  ensures  dom(l1') == intersect(dom(l1), complement(d));
  ensures  dom(l2') == union(dom(l2), d);
  ensures  map(l1') == map(l1);
  ensures  map(l2') == map(l2);


record Node
{
  data: int;
  next: Node;
}

const unique null: Node;
invariant IsNull(null.alloc);
//invariant null.next == null;

var TOP: Node;

const unique EMPTY: int;

procedure {:isatomic} CAS(oldVal: Node, newVal: Node)
returns (r: bool)
{
  r := (TOP == oldVal);
  if(r)
  {
    TOP := newVal;
  }
}

// invariant ReachBetween(Node_next, TOP, null, null) && (forall n: Node :: Connected(Node_next, TOP, n) && n != null ==> IsAlloc(n.alloc)) && (forall n1,n2: Node :: IsDealloc(n1.alloc) ==> n2.next != n1) && (forall n: Node :: !IsAlloc(n.alloc) ==> n.next == null)

procedure push(v: int)
{
  var t, x: Node;
  var g: bool;
  
  x := New Node;
  x.data := v;

  while(true)
  {
    t := TOP;		// Connected(t, TOP)
    x.next := t;	// !Connected(x, TOP)
    call g := CAS(t, x); // x.next == t, !Connected(x, TOP)
    if(g) { break; }
  }
}

procedure pop()
returns (v: int)
{
  var t, x: Node;
  var g: bool;
  
  while(true)
  {
    t := TOP;		// Connected(t, TOP)
    if(t == null)
    {
      v := EMPTY;
      return;
    }
    x := t.next;	// Connected(t, TOP)
    call g := CAS(t, x); // Connected(t, TOP), x == t.next
    if(g) { break; }
  }

  v := t.data;
}