// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Treiber<T> { Treiber(top: RefNode T, stack: Lmap (RefNode T) (Node T)) }
type RefTreiber T = Ref (Treiber T);

type X; // module type parameter

var {:layer 4, 5} Stack: [RefTreiber X]Vec X;
var {:layer 0, 4} ts: Lmap (RefTreiber X) (Treiber X);

atomic action {:layer 5} AtomicTreiberAlloc() returns (loc_t: Lval (Loc (Treiber X)))
modifies Stack;
{
  var ref_t: RefTreiber X;
  call loc_t := Loc_New();
  ref_t := Ref(loc_t->val);
  Stack[ref_t] := Vec_Empty();
}
yield procedure {:layer 4} TreiberAlloc() returns (loc_t: Lval (Loc (Treiber X)))
refines AtomicTreiberAlloc;
{
  var ref_t: RefTreiber X;
  call loc_t := Alloc#0();
  ref_t := Ref(loc_t->val);
  call {:layer 4} Stack := Copy(Stack[ref_t := Vec_Empty()]);
  call {:layer 4} AbsDefinition(ts->val[ref_t]->top, ts->val[ref_t]->stack->val);
}

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
    call {:layer 4} Stack := Copy(Stack[ref_t := Vec_Append(Stack[ref_t], x)]);
    assert {:layer 4} ts->val[ref_t]->top != Nil();
    call {:layer 4} AbsDefinition(ts->val[ref_t]->top, ts->val[ref_t]->stack->val);
  }
  
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
    assert {:layer 4} Vec_Len(Stack[ref_t]) > 0;
    call {:layer 4} Stack := Copy(Stack[ref_t := Vec_Remove(Stack[ref_t])]);
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
    ts->val[ref_t]->top := new_ref_n;
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
modifies ts;
{
  var new_loc_n: Lval (Loc (Node X));
  var lmap_n, lmap_n': Lmap (RefNode X) (Node X);
  var t: RefNode X;

  if (success) {
    t := ts->val[ref_t]->top;
    call new_loc_n, lmap_n := Lmap_Alloc(Node(t, x));
    ts->val[ref_t]->top := Ref(new_loc_n->val);
    call lmap_n, lmap_n' := Lmap_Move(lmap_n, ts->val[ref_t]->stack, ts->val[ref_t]->top);
    ts->val[ref_t]->stack := lmap_n';
  }
}
yield procedure {:layer 2} PushIntermediate(ref_t: RefTreiber X, x: X) returns (success: bool)
refines AtomicPushIntermediate;
preserves call YieldInv#2(ref_t);
{
  var ref_n: RefNode X;
  var new_loc_n: Lval (Loc (Node X));
  var lmap_n: Lmap (RefNode X) (Node X);
  var new_ref_n: RefNode X;

  call ref_n := ReadTopOfStack#Push(ref_t);
  call new_loc_n, lmap_n := Lmap_Alloc(Node(ref_n, x));
  new_ref_n := Ref(new_loc_n->val);
  call success := WriteTopOfStack(ref_t, ref_n, new_ref_n);
  if (success) {
    call AllocInStack(ref_t, new_ref_n, lmap_n);
  }
}

right action {:layer 3} AtomicReadTopOfStack#Pop(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{
  assert ts->dom[ref_t];
  assume NilDomain(ts, ref_t)[ref_n];
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

/*
right action {:layer 3} AtomicLoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X)
{
  assert ts->dom[ref_t];
  assert ts->val[ref_t]->stack->dom[ref_n];
  node := ts->val[ref_t]->stack->val[ref_n];
}
yield procedure {:layer 2} LoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X)
refines AtomicLoadNode;
preserves call YieldInv#2(ref_t);
{
  call node := LoadNode#0(ref_t, ref_n);
}
*/

right action {:layer 1,3} AtomicLoadNode#0(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X)
{
  assert ts->dom[ref_t];
  assert ts->val[ref_t]->stack->dom[ref_n];
  node := ts->val[ref_t]->stack->val[ref_n];
}
yield procedure {:layer 0} LoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X);
refines AtomicLoadNode#0;

left action {:layer 1, 2} AtomicAllocInStack(ref_t: RefTreiber X, ref_n: RefNode X, {:linear_in} lmap_n: Lmap (RefNode X) (Node X))
modifies ts;
{
  var lmap_n', lmap_n'': Lmap (RefNode X) (Node X);
  assert ts->dom[ref_t];
  call lmap_n'', lmap_n' := Lmap_Move(lmap_n, ts->val[ref_t]->stack, ref_n);
  ts->val[ref_t]->stack := lmap_n';
}
yield procedure {:layer 0} AllocInStack(ref_t: RefTreiber X, ref_n: RefNode X, {:linear_in} lmap_n: Lmap (RefNode X) (Node X));
refines AtomicAllocInStack;

atomic action {:layer 3} AtomicWriteTopOfStack#Pop(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool)
modifies ts;
{
  assert NilDomain(ts, ref_t)[new_ref_n];
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
  var top: RefNode X;
  assert ts->dom[ref_t];
  top := ts->val[ref_t]->top;
  if (old_ref_n == top) {
    ts->val[ref_t]->top := new_ref_n;
    r := true;
  }
  else {
    r := false;
  }
}
yield procedure {:layer 0} WriteTopOfStack(ref_t: RefTreiber X, old_ref_n: RefNode X, new_ref_n: RefNode X) returns (r: bool);
refines AtomicWriteTopOfStack;

atomic action {:layer 1, 4} AtomicAlloc#0() returns (loc_t: Lval (Loc (Treiber X)))
modifies ts;
{
  var top: Ref (Node X);
  var stack: Lmap (RefNode X) (Node X);
  var treiber: Treiber X;
  var lmap_t: Lmap (RefTreiber X) (Treiber X);
  top := Nil();
  call stack := Lmap_Empty();
  treiber := Treiber(top, stack);
  call loc_t, lmap_t := Lmap_Alloc(treiber);
  call lmap_t, ts := Lmap_Move(lmap_t, ts, Ref(loc_t->val));
}
yield procedure {:layer 0} Alloc#0() returns (loc_t: Lval (Loc (Treiber X)));
refines AtomicAlloc#0;

function {:inline} NilDomain(ts: Lmap (RefTreiber X) (Treiber X), ref_t: RefTreiber X): [RefNode X]bool {
  Union(Singleton(Nil()), ts->val[ref_t]->stack->dom)
}

yield invariant {:layer 1} YieldInv#1(ref_t: RefTreiber X, ref_n: RefNode X);
invariant ts->dom[ref_t];
invariant ts->val[ref_t]->stack->dom[ref_n];

yield invariant {:layer 2} YieldInv#2(ref_t: RefTreiber X);
invariant ts->dom[ref_t];
invariant NilDomain(ts, ref_t)[ts->val[ref_t]->top];

yield invariant {:layer 3} YieldInv#3(ref_t: RefTreiber X);
invariant ts->dom[ref_t];
invariant NilDomain(ts, ref_t)[ts->val[ref_t]->top];
invariant (forall ref_n: RefNode X :: ts->val[ref_t]->stack->dom[ref_n] ==> NilDomain(ts, ref_t)[ts->val[ref_t]->stack->val[ref_n]->next]);

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
// trusted fact justified by induction and determinism of AbsCompute
free ensures stack == Abs(ref_n, stackContents);
{
  var n: Node X;
  if (ref_n == Nil()) {
      stack := Vec_Empty();
  } else {
      n := stackContents[ref_n];
      // termination argument for induction
      assert Between(stackContents, ref_n, n->next, Nil());
      call stack := AbsCompute(n->next, stackContents);
      stack := Vec_Append(stack, n->val);
  }
}

yield invariant {:layer 4} YieldInv#4(ref_t: RefTreiber X);
invariant Stack[ref_t] == (var t := ts->val[ref_t]; Abs(t->top, t->stack->val));
invariant (var t := ts->val[ref_t]; Between(t->stack->val, t->top, t->top, Nil()));
invariant (var t := ts->val[ref_t]; Subset(BetweenSet(t->stack->val, t->top, Nil()), NilDomain(ts, ref_t)));
