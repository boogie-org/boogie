// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory %s > %t
// RUN: %diff %s.expect %t
type Node;
type lmap;
function {:linear "Node"} dom(lmap): [Node]bool;
function map(lmap): [Node]Node;

procedure {:yields} Load(i:Node) returns(v:Node);
requires dom(stack)[i];
ensures {:atomic 0} v == map(stack)[i];

procedure {:yields} Store({:linear "Node"} l_in:lmap, i:Node, v:Node) returns({:linear "Node"} l_out:lmap);
requires dom(l_in)[i];
ensures {:atomic 0} dom(l_out) == dom(l_in) && map(l_out) == map(l_in)[i := v];

procedure {:yields} TransferToStack(oldVal: Node, newVal: Node, {:linear "Node"} l_in:lmap) returns (r: bool, {:linear "Node"} l_out:lmap);
requires dom(l_in)[newVal];
modifies stack, TOP;
ensures {:atomic 0} if oldVal == old(TOP)
		    then newVal == TOP && dom(stack) == dom(old(stack))[newVal := true] && map(stack) == map(old(stack))[newVal := map(l_in)[newVal]]
                    else TOP == old(TOP) && stack == old(stack) && l_out == l_in;

procedure {:yields} TransferFromStack(oldVal: Node, newVal: Node) returns (r: bool, {:linear "Node"} l_out:lmap);
requires dom(stack)[oldVal];
modifies stack, TOP;
ensures {:atomic 0} if oldVal == old(TOP)
		    then dom(stack) == dom(old(stack))[oldVal := false] && map(stack) == map(old(stack)) && dom(l_out)[oldVal] && map(l_out)[oldVal] == map(old(stack))[oldVal]
		    else TOP == old(TOP) && stack == old(stack);

procedure Alloc() returns (d: Node, {:linear "Node"} l: lmap);
ensures dom(l)[d];

procedure Free(d: Node, {:linear "Node"} l: lmap);

const unique null: Node;

var {:qed} TOP: Node;
var {:qed} {:linear "Node"} stack: lmap;

procedure {:yields} push()
{
  var t, x: Node;
  var g: bool;
  var {:linear "Node"} x_lmap: lmap;

  call x, x_lmap := Alloc();

  while(true)
  {
    t := TOP;		
    call x_lmap := Store(x_lmap, x, t);
    call g, x_lmap := TransferToStack(t, x, x_lmap); 
    if (g) { 
      break; 
    }
  }
}

procedure {:yields} pop()
{
  var t, x: Node;
  var g: bool;
  var {:linear "Node"} t_lmap: lmap;

  while(true)
  {
    t := TOP;		
    if (t == null)
    {
      return;
    }
    call x := Load(t);
    call g, t_lmap := TransferFromStack(t, x); 
    if (g) { 
      call Free(t, t_lmap);
      break; 
    }
  }
}