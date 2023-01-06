// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
Highlights:
- Nontrivial use of nested linear maps
- Push and pop use distinct abstractions for read/write of top of stack
- Variable "unused" tracks nodes added to the stack linear map that do 
  not logically become part of the stack
- Push made atomic first before commutativity reasoning for the pop path

The final layer that transforms the stack representation into a functional 
version is not done. We expect that the proof for this layer will use 
reasoning about node reachability.
*/

type {:datatype} Treiber T;
function {:constructor} Treiber<T>(top: RefNode T, stack: Lmap (Node T)): Treiber T;
type RefTreiber T = Ref (Treiber T);

type X; // module type parameter

var {:layer 0, 4} ts: Lmap (Treiber X);
var {:layer 2, 4} unused: [RefTreiber X][RefNode X]bool;

procedure {:layer 4} {:atomic} AtomicPopIntermediate(ref_t: RefTreiber X) returns (success: bool, x: X)
modifies ts;
{
  var new_ref_n: RefNode X;
  assert ts->dom[ref_t];
  if (success) {
    assume ts->val[ref_t]->stack->dom[ts->val[ref_t]->top];
    Node(new_ref_n, x) := ts->val[ref_t]->stack->val[ts->val[ref_t]->top];
    call Lmap_Write(ts->val[ref_t]->top, new_ref_n);
  }
}
procedure {:yields} {:layer 3} {:refines "AtomicPopIntermediate"}
{:yield_preserves "YieldInv#2", ref_t}
{:yield_preserves "YieldInv#3", ref_t}
PopIntermediate(ref_t: RefTreiber X) returns (success: bool, x: X)
requires {:layer 2} ts->dom[ref_t];
{
  var ref_n, new_ref_n: RefNode X;
  var node: Node X;

  success := false;
  call ref_n := ReadTopOfStack#Pop(ref_t);
  if (ref_n == Nil()) {
    return;
  }
  call node := LoadNode(ref_t, ref_n);
  Node(new_ref_n, x) := node;
  call success := WriteTopOfStack#Pop(ref_t, ref_n, new_ref_n);
}

procedure {:layer 3} {:atomic} AtomicPushIntermediate(ref_t: RefTreiber X, x: X) returns (success: bool)
modifies ts, unused;
{
  var {:pool "A"} ref_n: RefNode X;
  var {:pool "A"} new_ref_n: RefNode X;
  assert ts->dom[ref_t];
  assume {:add_to_pool "A", ref_n} true;
  call new_ref_n := Lmap_Add(ts->val[ref_t]->stack, Node(if success then ts->val[ref_t]->top else ref_n, x));
  if (success) {
    call Lmap_Write(ts->val[ref_t]->top, new_ref_n);
  } else {
    unused[ref_t][new_ref_n] := true;
  }
  assume {:add_to_pool "A", new_ref_n} true;
}
procedure {:yields} {:layer 2} {:refines "AtomicPushIntermediate"}
PushIntermediate(ref_t: RefTreiber X, x: X) returns (success: bool)
{
  var ref_n, new_ref_n: RefNode X;
  
  call ref_n := ReadTopOfStack#Push(ref_t);
  call new_ref_n := AllocInStack(ref_t, Node(ref_n, x));
  call success := WriteTopOfStack(ref_t, ref_n, new_ref_n);
  assert {:layer 2} {:add_to_pool "A", ref_n, new_ref_n} true;
  call AddToUnusedNodes(success, ref_t, new_ref_n);
}

procedure {:right} {:layer 3} 
AtomicReadTopOfStack#Pop(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{ 
  assert ts->dom[ref_t];
  assume NilDomain(ts, ref_t, unused)[ref_n];
}
procedure {:yields} {:layer 2} {:refines "AtomicReadTopOfStack#Pop"}
{:yield_preserves "YieldInv#2", ref_t}
ReadTopOfStack#Pop(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{
  call ref_n := ReadTopOfStack(ref_t);
}

procedure {:right} {:layer 2} 
AtomicReadTopOfStack#Push(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{ 
  assert ts->dom[ref_t];
}
procedure {:yields} {:layer 1} {:refines "AtomicReadTopOfStack#Push"} 
ReadTopOfStack#Push(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{
  call ref_n := ReadTopOfStack(ref_t);
}

procedure {:atomic} {:layer 1, 2} 
AtomicReadTopOfStack(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{ 
  assert ts->dom[ref_t];
  ref_n := ts->val[ref_t]->top;
}
procedure {:yields} {:layer 0} {:refines "AtomicReadTopOfStack"} 
ReadTopOfStack(ref_t: RefTreiber X) returns (ref_n: RefNode X);

procedure {:right} {:layer 1, 3} 
AtomicLoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X)
{
  assert ts->dom[ref_t];
  assert ts->val[ref_t]->stack->dom[ref_n];
  node := ts->val[ref_t]->stack->val[ref_n];
}
procedure {:yields} {:layer 0} {:refines "AtomicLoadNode"} 
LoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X);

procedure {:right} {:layer 1, 2} 
AtomicAllocInStack(ref_t: RefTreiber X, node: Node X) returns (ref_n: RefNode X)
modifies ts;
{
  assert ts->dom[ref_t];
  call ref_n := Lmap_Add(ts->val[ref_t]->stack, node);
}
procedure {:yields} {:layer 0} {:refines "AtomicAllocInStack"} 
AllocInStack(ref_t: RefTreiber X, node: Node X) returns (ref_n: RefNode X);

procedure {:atomic} {:layer 3} 
AtomicWriteTopOfStack#Pop(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool)
modifies ts;
{
  assert NilDomain(ts, ref_t, unused)[new_ref_n];
  call r := AtomicWriteTopOfStack(ref_t, old_ref_n, new_ref_n);
}
procedure {:yields} {:layer 2} {:refines "AtomicWriteTopOfStack#Pop"}
{:yield_preserves "YieldInv#2", ref_t}
WriteTopOfStack#Pop(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool)
{
  call r := WriteTopOfStack(ref_t, old_ref_n, new_ref_n);
}

procedure {:atomic} {:layer 1, 3} 
AtomicWriteTopOfStack(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool)
modifies ts;
{ 
  assert ts->dom[ref_t];
  if (old_ref_n == ts->val[ref_t]->top) {
    call Lmap_Write(ts->val[ref_t]->top, new_ref_n);
    r := true;
  }
  else {
    r := false;
  }
}
procedure {:yields} {:layer 0} {:refines "AtomicWriteTopOfStack"} 
WriteTopOfStack(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool);

procedure {:intro} {:layer 2} AddToUnusedNodes(success: bool, ref_t: RefTreiber X, ref_n: RefNode X)
modifies unused;
{
  if (!success) {
    unused[ref_t][ref_n] := true;
  }
}

function {:inline} Domain(ts: Lmap (Treiber X), ref_t: RefTreiber X, unused: [RefTreiber X][RefNode X]bool): [RefNode X]bool {
  Difference(ts->val[ref_t]->stack->dom, unused[ref_t])
}

function {:inline} NilDomain(ts: Lmap (Treiber X), ref_t: RefTreiber X, unused: [RefTreiber X][RefNode X]bool): [RefNode X]bool {
  Union(Singleton(Nil()), Domain(ts, ref_t, unused))
}

procedure {:yield_invariant} {:layer 2} YieldInv#2(ref_t: RefTreiber X);
requires Subset(unused[ref_t], ts->val[ref_t]->stack->dom);
requires NilDomain(ts, ref_t, unused)[ts->val[ref_t]->top];

procedure {:yield_invariant} {:layer 3} YieldInv#3(ref_t: RefTreiber X);
requires Subset(unused[ref_t], ts->val[ref_t]->stack->dom);
requires NilDomain(ts, ref_t, unused)[ts->val[ref_t]->top];
requires (forall ref_n: RefNode X :: Domain(ts, ref_t, unused)[ref_n] ==> NilDomain(ts, ref_t, unused)[ts->val[ref_t]->stack->val[ref_n]->next]);
