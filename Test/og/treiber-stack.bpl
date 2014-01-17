type Node;
type lmap;
function dom(lmap): [Node]bool;
function map(lmap): [Node]Node;

function {:builtin "MapConst"} MapConst(bool) : [Node]bool;
function {:builtin "MapOr"} MapOr([Node]bool, [Node]bool) : [Node]bool;

procedure Load(i:Node) returns(v:Node);
  requires dom(stack)[i];
  ensures  v == map(stack)[i];

procedure Store({:linear "Node"} l_in:lmap, i:Node, v:Node) returns({:linear "Node"} l_out:lmap);
  requires dom(l_in)[i];
  ensures  dom(l_out) == dom(l_in);
  ensures  map(l_out) == map(l_in)[i := v];

procedure TransferIn({:linear "Node"} l1_in:lmap, d:Node);
  requires dom(l1_in)[d];
  modifies stack;
  ensures  dom(stack) == dom(old(stack))[d := true];
  ensures  map(stack) == map(old(stack))[d := map(l1_in)[d]];

procedure TransferOut(d:Node);
  requires dom(stack)[d];
  modifies stack;
  ensures  dom(stack) == dom(old(stack))[d := false];
  ensures  map(stack) == map(old(stack));

procedure New() returns ({:linear "Node"} l: lmap, d: Node);
ensures dom(l)[d];

const unique null: Node;

var TOP: Node;
var {:linear "Node"} stack: lmap;

procedure {:yields} CAS(oldVal: Node, newVal: Node)
returns (r: bool)
{
  r := (TOP == oldVal);
  if (r) {
    TOP := newVal;
  }
}

procedure {:yields} push()
{
  var t, x: Node;
  var g: bool;
  var {:linear "Node"} x_lmap: lmap;

  call x_lmap, x := New();

  while(true)
  {
    t := TOP;		
    call x_lmap := Store(x_lmap, x, t);
    call g := CAS(t, x); 
    if (g) { 
      call TransferIn(x_lmap, x);
      break; 
    }
  }
}

procedure {:yields} pop()
{
  var t, x: Node;
  var g: bool;

  while(true)
  {
    t := TOP;		
    if (t == null)
    {
      return;
    }
    call x := Load(t);
    call g := CAS(t, x); 
    if (g) { 
      call TransferOut(t);
      break; 
    }
  }
}