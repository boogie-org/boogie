// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Treiber<T> { Treiber(top: RefNode T, stack: Lheap (Node T)) }
type RefTreiber T = Ref (Treiber T);

type X; // module type parameter

var {:layer 4, 5} Stack: Map (RefTreiber X) (Vec X);
var {:layer 0, 4} ts: Lheap (Treiber X);

atomic action {:layer 5} AtomicTreiberAlloc() returns (loc_t: Lval (Loc (Treiber X)))
modifies Stack;
{
  var ref_t: RefTreiber X;
  call loc_t := Loc_New();
  ref_t := Ref(loc_t->val);
  assume !Map_Contains(Stack, ref_t);
  Stack := Map_Update(Stack, ref_t, Vec_Empty());
}
yield procedure {:layer 4} TreiberAlloc() returns (loc_t: Lval (Loc (Treiber X)))
refines AtomicTreiberAlloc;
preserves call DomYieldInv#4();
{
  var ref_t: RefTreiber X;
  call loc_t := Alloc#0();
  ref_t := Ref(loc_t->val);
  call {:layer 4} Stack := Copy(Map_Update(Stack, ref_t, Vec_Empty()));
  call {:layer 4} AbsLemma(ts->val->val[ref_t]->top, ts->val->val[ref_t]->stack->val);
}

atomic action {:layer 5} AtomicPush(ref_t: RefTreiber X, x: X) returns (success: bool)
modifies Stack;
{
  if (success) {
    Stack := Map_Update(Stack, ref_t, Vec_Append(Map_At(Stack, ref_t), x));
  }
}
yield procedure {:layer 4} Push(ref_t: RefTreiber X, x: X) returns (success: bool)
refines AtomicPush;
preserves call YieldInv#2(ref_t);
preserves call YieldInv#4(ref_t);
preserves call DomYieldInv#4();
{
  var {:layer 4} old_top: RefNode X;
  var {:layer 4} old_stack: Map (RefNode X) (Node X);
  call {:layer 4} old_top := Copy(ts->val->val[ref_t]->top);
  call {:layer 4} old_stack := Copy(ts->val->val[ref_t]->stack->val);
  call success := PushIntermediate(ref_t, x);
  if (success) {
    call {:layer 4} FrameLemma(old_top, old_stack, ts->val->val[ref_t]->stack->val);
    call {:layer 4} Stack := Copy(Map_Update(Stack, ref_t, Vec_Append(Map_At(Stack, ref_t), x)));
    assert {:layer 4} ts->val->val[ref_t]->top != Nil();
    call {:layer 4} AbsLemma(ts->val->val[ref_t]->top, ts->val->val[ref_t]->stack->val);
  }
}

atomic action {:layer 5} AtomicPop(ref_t: RefTreiber X) returns (success: bool, x: X)
modifies Stack;
{
  var stack: Vec X;
  stack := Map_At(Stack, ref_t);
  if (success) {
    assume Vec_Len(stack) > 0;
    x := Vec_Nth(stack, Vec_Len(stack) - 1);
    Stack := Map_Update(Stack, ref_t, Vec_Remove(stack));
  }
}
yield procedure {:layer 4} Pop(ref_t: RefTreiber X) returns (success: bool, x: X)
refines AtomicPop;
preserves call YieldInv#2(ref_t);
preserves call YieldInv#3(ref_t);
preserves call YieldInv#4(ref_t);
preserves call DomYieldInv#4();
{
  call {:layer 4} AbsLemma(ts->val->val[ref_t]->top, ts->val->val[ref_t]->stack->val);
  call success, x := PopIntermediate(ref_t);
  if (success) {
    assert {:layer 4} Vec_Len(Map_At(Stack, ref_t)) > 0;
    call {:layer 4} Stack := Copy(Map_Update(Stack, ref_t, Vec_Remove(Map_At(Stack, ref_t))));
  }
}

atomic action {:layer 4} AtomicPopIntermediate(ref_t: RefTreiber X) returns (success: bool, x: X)
modifies ts;
{
  var new_ref_n: RefNode X;
  assume Map_Contains(ts->val, ref_t);
  if (success) {
    assume ts->val->val[ref_t]->top != Nil();
    assume Map_Contains(ts->val->val[ref_t]->stack->val, ts->val->val[ref_t]->top);
    Node(new_ref_n, x) := ts->val->val[ref_t]->stack->val->val[ts->val->val[ref_t]->top];
    ts->val->val[ref_t]->top := new_ref_n;
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
  var lmap_n, lmap_n': Lheap (Node X);
  var t: RefNode X;

  if (success) {
    t := ts->val->val[ref_t]->top;
    call new_loc_n, lmap_n := Lmap_Alloc(Node(t, x));
    call Lmap_Assume(lmap_n, ts->val->val[ref_t]->stack);
    ts->val->val[ref_t]->top := Ref(new_loc_n->val);
    call lmap_n, lmap_n' := Lmap_Move(lmap_n, ts->val->val[ref_t]->stack, ts->val->val[ref_t]->top);
    ts->val->val[ref_t]->stack := lmap_n';
  }
}
yield procedure {:layer 2} PushIntermediate(ref_t: RefTreiber X, x: X) returns (success: bool)
refines AtomicPushIntermediate;
preserves call YieldInv#2(ref_t);
{
  var ref_n: RefNode X;
  var new_loc_n: Lval (Loc (Node X));
  var lmap_n: Lheap (Node X);
  var new_ref_n: RefNode X;

  call ref_n := ReadTopOfStack#Push(ref_t);
  call new_loc_n, lmap_n := Lmap_Alloc(Node(ref_n, x));
  call {:layer 2} Lmap_Assume(lmap_n, ts->val->val[ref_t]->stack);
  new_ref_n := Ref(new_loc_n->val);
  call success := WriteTopOfStack(ref_t, ref_n, new_ref_n);
  if (success) {
    call AllocInStack(ref_t, new_ref_n, lmap_n);
  }
}

right action {:layer 3} AtomicReadTopOfStack#Pop(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{
  assert Map_Contains(ts->val, ref_t);
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
  assert Map_Contains(ts->val, ref_t);
}
yield procedure {:layer 1} ReadTopOfStack#Push(ref_t: RefTreiber X) returns (ref_n: RefNode X)
refines AtomicReadTopOfStack#Push;
{
  call ref_n := ReadTopOfStack(ref_t);
}

atomic action {:layer 1, 2} AtomicReadTopOfStack(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{
  assert Map_Contains(ts->val, ref_t);
  ref_n := ts->val->val[ref_t]->top;
}
yield procedure {:layer 0} ReadTopOfStack(ref_t: RefTreiber X) returns (ref_n: RefNode X);
refines AtomicReadTopOfStack;

right action {:layer 3} AtomicLoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X)
{
  assert Map_Contains(ts->val, ref_t);
  assert Map_Contains(ts->val->val[ref_t]->stack->val, ref_n);
  node := ts->val->val[ref_t]->stack->val->val[ref_n];
}
yield procedure {:layer 2} LoadNode(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X)
refines AtomicLoadNode;
preserves call YieldInv#2(ref_t);
{
  call node := LoadNode#0(ref_t, ref_n);
}

atomic action {:layer 1,2} AtomicLoadNode#0(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X)
{
  assume Map_Contains(ts->val, ref_t);
  assume Map_Contains(ts->val->val[ref_t]->stack->val, ref_n);
  node := ts->val->val[ref_t]->stack->val->val[ref_n];
}
yield procedure {:layer 0} LoadNode#0(ref_t: RefTreiber X, ref_n: RefNode X) returns (node: Node X);
refines AtomicLoadNode#0;

left action {:layer 1, 2} AtomicAllocInStack(ref_t: RefTreiber X, ref_n: RefNode X, {:linear_in} lmap_n: Lheap (Node X))
modifies ts;
{
  var lmap_n', lmap_n'': Lheap (Node X);
  assert Map_Contains(ts->val, ref_t);
  call lmap_n'', lmap_n' := Lmap_Move(lmap_n, ts->val->val[ref_t]->stack, ref_n);
  ts->val->val[ref_t]->stack := lmap_n';
}
yield procedure {:layer 0} AllocInStack(ref_t: RefTreiber X, ref_n: RefNode X, {:linear_in} lmap_n: Lheap (Node X));
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
  assert Map_Contains(ts->val, ref_t);
  top := ts->val->val[ref_t]->top;
  if (old_ref_n == top) {
    ts->val->val[ref_t]->top := new_ref_n;
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
  var stack: Lheap (Node X);
  var treiber: Treiber X;
  var lmap_t: Lheap (Treiber X);
  top := Nil();
  call stack := Lmap_Empty();
  treiber := Treiber(top, stack);
  call loc_t, lmap_t := Lmap_Alloc(treiber);
  call Lmap_Assume(lmap_t, ts);
  call lmap_t, ts := Lmap_Move(lmap_t, ts, Ref(loc_t->val));
}
yield procedure {:layer 0} Alloc#0() returns (loc_t: Lval (Loc (Treiber X)));
refines AtomicAlloc#0;

function {:inline} NilDomain(ts: Lheap (Treiber X), ref_t: RefTreiber X): [RefNode X]bool {
  ts->val->val[ref_t]->stack->val->dom->val[Nil() := true]
}

yield invariant {:layer 1} YieldInv#1(ref_t: RefTreiber X, ref_n: RefNode X);
invariant Map_Contains(ts->val, ref_t);
invariant ts->val->val[ref_t]->stack->val->dom->val[ref_n];

yield invariant {:layer 2} YieldInv#2(ref_t: RefTreiber X);
invariant Map_Contains(ts->val, ref_t);
invariant NilDomain(ts, ref_t)[ts->val->val[ref_t]->top];

yield invariant {:layer 3} YieldInv#3(ref_t: RefTreiber X);
invariant Map_Contains(ts->val, ref_t);
invariant NilDomain(ts, ref_t)[ts->val->val[ref_t]->top];
invariant (var t := ts->val->val[ref_t]; (var m := t->stack->val; (forall ref_n: RefNode X :: m->dom->val[ref_n] ==> NilDomain(ts, ref_t)[m->val[ref_n]->next])));

// The following is a manual encoding of the termination proof for the abstraction.
function Abs(ref_n: RefNode X, map: Map (RefNode X) (Node X)): Vec X;

pure procedure AbsCompute(ref_n: RefNode X, map: Map (RefNode X) (Node X)) returns (absStack: Vec X)
requires Between(map->val, ref_n, ref_n, Nil());
requires IsSubset(BetweenSet(map->val, ref_n, Nil()), map->dom->val[Nil() := true]);
ensures absStack ==
        if ref_n == Nil() then
        Vec_Empty() else
        (var n := Map_At(map, ref_n); Vec_Append(Abs(n->next, map), n->val));
free ensures absStack == Abs(ref_n, map);
{
  var n: Node X;
  if (ref_n == Nil()) {
      absStack := Vec_Empty();
  } else {
      assert Map_Contains(map, ref_n); // soundness of framing
      n := Map_At(map, ref_n);
      assert Between(map->val, ref_n, n->next, Nil()); // soundness of termination (for induction)
      call absStack := AbsCompute(n->next, map);
      absStack := Vec_Append(absStack, n->val);
  }
}

pure procedure AbsLemma(ref_n: RefNode X, map: Map (RefNode X) (Node X))
requires Between(map->val, ref_n, ref_n, Nil());
requires IsSubset(BetweenSet(map->val, ref_n, Nil()), map->dom->val[Nil() := true]);
ensures Abs(ref_n, map) ==
        if ref_n == Nil() then
        Vec_Empty() else
        (var n := Map_At(map, ref_n); Vec_Append(Abs(n->next, map), n->val));
{
  var absStack: Vec X;
  call absStack := AbsCompute(ref_n, map);
}

pure procedure FrameLemma(ref_n: RefNode X, map: Map (RefNode X) (Node X), map': Map (RefNode X) (Node X));
requires Between(map->val, ref_n, ref_n, Nil());
requires IsSubset(BetweenSet(map->val, ref_n, Nil()), map->dom->val[Nil() := true]);
requires IsSubset(map->dom->val, map'->dom->val);
requires MapIte(map->dom->val, map->val, MapConst(Default())) == MapIte(map->dom->val, map'->val, MapConst(Default()));
ensures Abs(ref_n, map) == Abs(ref_n, map');

yield invariant {:layer 4} YieldInv#4(ref_t: RefTreiber X);
invariant Map_Contains(ts->val, ref_t);
invariant Map_At(Stack, ref_t) == (var t := ts->val->val[ref_t]; Abs(t->top, t->stack->val));
invariant (var t := ts->val->val[ref_t]; Between(t->stack->val->val, t->top, t->top, Nil()));
invariant (var t := ts->val->val[ref_t]; IsSubset(BetweenSet(t->stack->val->val, t->top, Nil()), NilDomain(ts, ref_t)));

yield invariant {:layer 4} DomYieldInv#4();
invariant Stack->dom == ts->val->dom;
