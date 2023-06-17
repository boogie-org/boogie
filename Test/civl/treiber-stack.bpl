// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
Highlights:
- Nontrivial use of nested linear maps
- Push and pop use distinct abstractions for read/write of top of stack
- Variable "unused" tracks nodes added to the stack linear map that do
  not logically become part of the stack
- Push made atomic first before commutativity reasoning for the pop path
- The final layer transforms the stack into a functional version. The proof
  for this layer uses an "abstraction function" specified as a pure procedure.
*/

datatype Treiber<T> { Treiber(top: RefNode T, stack: Lheap (Node T)) }
type RefTreiber T = Ref (Treiber T);

type X; // module type parameter

var {:layer 4, 5} Stack: [RefTreiber X]Vec X;
var {:layer 0, 4} ts: Lheap (Treiber X);
var {:layer 2, 4} unused: [RefTreiber X][RefNode X]bool;

atomic action {:layer 5} AtomicPush(ref_t: RefTreiber X, x: X) returns (success: bool)
modifies Stack;
{
  if (success) {
    Stack[ref_t] := Vec_Append(Stack[ref_t], x);
  }
}
yield procedure {:layer 4} Push(ref_t: RefTreiber X, x: X) returns (success: bool)
refines AtomicPush;
preserves call YieldInv#2(ref_t);
preserves call YieldInv#4(ref_t);
{
  call success := PushIntermediate(ref_t, x);
  if (success) {
    call PushStack(ref_t, x);
  }
  call {:layer 4} AbsDefinition(ts->val[ref_t]->top, ts->val[ref_t]->stack->val);
}

atomic action {:layer 5} AtomicPop(ref_t: RefTreiber X) returns (success: bool, x: X)
modifies Stack;
{
  var stack: Vec X;
  stack := Stack[ref_t];
  if (success) {
    assume Vec_Len(stack) > 0;
    x := Vec_Nth(stack, Vec_Len(stack) - 1);
    Stack[ref_t] := Vec_Remove(stack);
  }
}
yield procedure {:layer 4} Pop(ref_t: RefTreiber X) returns (success: bool, x: X)
refines AtomicPop;
preserves call YieldInv#2(ref_t);
preserves call YieldInv#3(ref_t);
preserves call YieldInv#4(ref_t);
{
  call {:layer 4} AbsDefinition(ts->val[ref_t]->top, ts->val[ref_t]->stack->val);
  call success, x := PopIntermediate(ref_t);
  if (success) {
    call PopStack(ref_t);
  }
}

atomic action {:layer 4} AtomicPopIntermediate(ref_t: RefTreiber X) returns (success: bool, x: X)
modifies ts;
{
  var new_ref_n: RefNode X;
  assume ts->dom[ref_t];
  if (success) {
    assume ts->val[ref_t]->top != Nil();
    assume ts->val[ref_t]->stack->dom[ts->val[ref_t]->top];
    Node(new_ref_n, x) := ts->val[ref_t]->stack->val[ts->val[ref_t]->top];
    call Lheap_Write(ts->val[ref_t]->top, new_ref_n);
  }
}
yield procedure {:layer 3} PopIntermediate(ref_t: RefTreiber X) returns (success: bool, x: X)
refines AtomicPopIntermediate;
preserves call YieldInv#2(ref_t);
preserves call YieldInv#3(ref_t);
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

atomic action {:layer 3, 4} AtomicPushIntermediate(ref_t: RefTreiber X, x: X) returns (success: bool)
modifies ts, unused;
{
  var {:pool "A"} ref_n: Lval (RefNode X);
  var {:pool "A"} new_ref_n: Lval (RefNode X);
  assume {:add_to_pool "A", ref_n} ts->dom[ref_t];
  call new_ref_n := Lheap_Alloc(ts->val[ref_t]->stack, Node(if success then ts->val[ref_t]->top else ref_n->val, x));
  if (success) {
    call Lheap_Write(ts->val[ref_t]->top, new_ref_n->val);
  } else {
    unused[ref_t][new_ref_n->val] := true;
  }
  assume {:add_to_pool "A", new_ref_n} true;
}
yield procedure {:layer 2} PushIntermediate(ref_t: RefTreiber X, x: X) returns (success: bool)
refines AtomicPushIntermediate;
preserves call YieldInv#2(ref_t);
{
  var ref_n: RefNode X;
  var new_ref_n: Lval (RefNode X);

  call ref_n := ReadTopOfStack#Push(ref_t);
  call new_ref_n := AllocInStack(ref_t, Node(ref_n, x));
  call success := WriteTopOfStack(ref_t, ref_n, new_ref_n->val);
  assume {:add_to_pool "A", Lval(ref_n), new_ref_n} true;
  call AddToUnusedNodes(success, ref_t, new_ref_n->val);
}

right action {:layer 3} AtomicReadTopOfStack#Pop(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{
  assert ts->dom[ref_t];
  assume NilDomain(ts, ref_t, unused)[ref_n];
}
yield procedure {:layer 2} ReadTopOfStack#Pop(ref_t: RefTreiber X) returns (ref_n: RefNode X)
refines AtomicReadTopOfStack#Pop;
preserves call YieldInv#2(ref_t);
{
  call ref_n := ReadTopOfStack(ref_t);
}

right action {:layer 2} AtomicReadTopOfStack#Push(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{
  assert ts->dom[ref_t];
}
yield procedure {:layer 1} ReadTopOfStack#Push(ref_t: RefTreiber X) returns (ref_n: RefNode X)
refines AtomicReadTopOfStack#Push;
{
  call ref_n := ReadTopOfStack(ref_t);
}

atomic action {:layer 1, 2} AtomicReadTopOfStack(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{
  assert ts->dom[ref_t];
  ref_n := ts->val[ref_t]->top;
}
yield procedure {:layer 0} ReadTopOfStack(ref_t: RefTreiber X) returns (ref_n: RefNode X);
refines AtomicReadTopOfStack;

right action {:layer 1, 3} AtomicLoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X)
{
  assert ts->dom[ref_t];
  assert ts->val[ref_t]->stack->dom[ref_n];
  node := ts->val[ref_t]->stack->val[ref_n];
}
yield procedure {:layer 0} LoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X);
refines AtomicLoadNode;

right action {:layer 1, 2} AtomicAllocInStack(ref_t: RefTreiber X, node: Node X) returns (ref_n: Lval (RefNode X))
modifies ts;
{
  assert ts->dom[ref_t];
  call ref_n := Lheap_Alloc(ts->val[ref_t]->stack, node);
}
yield procedure {:layer 0} AllocInStack(ref_t: RefTreiber X, node: Node X) returns (ref_n: Lval (RefNode X));
refines AtomicAllocInStack;

atomic action {:layer 3} AtomicWriteTopOfStack#Pop(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool)
modifies ts;
{
  assert NilDomain(ts, ref_t, unused)[new_ref_n];
  call r := AtomicWriteTopOfStack(ref_t, old_ref_n, new_ref_n);
}
yield procedure {:layer 2} WriteTopOfStack#Pop(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool)
refines AtomicWriteTopOfStack#Pop;
preserves call YieldInv#2(ref_t);
{
  call r := WriteTopOfStack(ref_t, old_ref_n, new_ref_n);
}

atomic action {:layer 1, 3} AtomicWriteTopOfStack(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool)
modifies ts;
{
  assert ts->dom[ref_t];
  if (old_ref_n == ts->val[ref_t]->top) {
    call Lheap_Write(ts->val[ref_t]->top, new_ref_n);
    r := true;
  }
  else {
    r := false;
  }
}
yield procedure {:layer 0} WriteTopOfStack(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool);
refines AtomicWriteTopOfStack;

atomic action {:layer 1, 4} AtomicAllocTreiber() returns (ref_t: Lval (RefTreiber X))
modifies ts;
{
  var top: Ref (Node X);
  var stack: Lheap (Node X);
  var treiber: Treiber X;
  top := Nil();
  call stack := Lheap_Empty();
  treiber := Treiber(top, stack);
  call ref_t := Lheap_Alloc(ts, treiber);
}
yield procedure {:layer 0} AllocTreiber() returns (ref_t: Lval (RefTreiber X));
refines AtomicAllocTreiber;

action {:layer 4} PushStack(ref_t: RefTreiber X, x: X)
modifies Stack;
{
  Stack[ref_t] := Vec_Append(Stack[ref_t], x);
}

action {:layer 4} PopStack(ref_t: RefTreiber X)
modifies Stack;
{
  assert Vec_Len(Stack[ref_t]) > 0;
  Stack[ref_t] := Vec_Remove(Stack[ref_t]);
}

action {:layer 2} AddToUnusedNodes(success: bool, ref_t: RefTreiber X, ref_n: RefNode X)
modifies unused;
{
  if (!success) {
    unused[ref_t][ref_n] := true;
  }
}

function {:inline} Domain(ts: Lheap (Treiber X), ref_t: RefTreiber X, unused: [RefTreiber X][RefNode X]bool): [RefNode X]bool {
  Difference(ts->val[ref_t]->stack->dom, unused[ref_t])
}

function {:inline} NilDomain(ts: Lheap (Treiber X), ref_t: RefTreiber X, unused: [RefTreiber X][RefNode X]bool): [RefNode X]bool {
  Union(Singleton(Nil()), Domain(ts, ref_t, unused))
}

yield invariant {:layer 2} YieldInv#2(ref_t: RefTreiber X);
invariant ts->dom[ref_t];
invariant Subset(unused[ref_t], ts->val[ref_t]->stack->dom);
invariant NilDomain(ts, ref_t, unused)[ts->val[ref_t]->top];

yield invariant {:layer 3} YieldInv#3(ref_t: RefTreiber X);
invariant ts->dom[ref_t];
invariant Subset(unused[ref_t], ts->val[ref_t]->stack->dom);
invariant NilDomain(ts, ref_t, unused)[ts->val[ref_t]->top];
invariant (forall ref_n: RefNode X :: Domain(ts, ref_t, unused)[ref_n] ==> NilDomain(ts, ref_t, unused)[ts->val[ref_t]->stack->val[ref_n]->next]);

// Boogie currently does not support termination proofs for functions or procedures.
// The following is a manual encoding of the termination proof for the abstraction.
function Abs(ref_n: RefNode X, stackContents: [RefNode X]Node X): Vec X;
pure procedure AbsDefinition(ref_n: RefNode X, stackContents: [RefNode X]Node X)
requires Between(stackContents, ref_n, ref_n, Nil());
ensures Abs(ref_n, stackContents) ==
        if ref_n == Nil() then
        Vec_Empty() else
        (var n := stackContents[ref_n]; Vec_Append(Abs(n->next, stackContents), n->val));
{
  var stack: Vec X;
  call stack := AbsCompute(ref_n, stackContents);
}
pure procedure AbsCompute(ref_n: RefNode X, stackContents: [RefNode X]Node X) returns (stack: Vec X)
requires Between(stackContents, ref_n, ref_n, Nil());
ensures stack ==
        if ref_n == Nil() then
        Vec_Empty() else
        (var n := stackContents[ref_n]; Vec_Append(Abs(n->next, stackContents), n->val));
free ensures stack == Abs(ref_n, stackContents); // trusted fact justified by induction
{
  var n: Node X;
  if (ref_n == Nil()) {
      stack := Vec_Empty();
  } else {
      n := stackContents[ref_n];
      assert Between(stackContents, ref_n, n->next, Nil()); // termination argument for induction
      call stack := AbsCompute(n->next, stackContents);
      stack := Vec_Append(stack, n->val);
  }
}

yield invariant {:layer 4} YieldInv#4(ref_t: RefTreiber X);
invariant Stack[ref_t] == (var t := ts->val[ref_t]; Abs(t->top, t->stack->val));
invariant (var t := ts->val[ref_t]; Between(t->stack->val, t->top, t->top, Nil()));
