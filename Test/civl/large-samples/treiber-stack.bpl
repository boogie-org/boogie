// RUN: %parallel-boogie -lib:base -lib:node -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Treiber<V> { Treiber(top: Option Loc, nodes: Map (One Loc) (Node V)) }

type X; // module type parameter

var {:layer 2, 3} TreiberPool: Map (One Loc) (Vec X);
var {:layer 0, 2} {:linear} TreiberPoolLow: Map (One Loc) (Treiber X);

/// Yield invariants

function {:inline} Domain(ts: Map (One Loc) (Treiber X), loc_t: Loc): Set (One Loc) {
  ts->val[One(loc_t)]->nodes->dom
}

function {:inline} ListInDomain(t: Treiber X): bool {
  (forall x: Loc:: BetweenSet(t->nodes->val, t->top, None())[x] ==> Set_Contains(t->nodes->dom, One(x)))
}

yield invariant {:layer 1} TopInStack(loc_t: Loc);
preserves Map_Contains(TreiberPoolLow, One(loc_t));
preserves (var loc_n := Map_At(TreiberPoolLow, One(loc_t))->top; loc_n is None || Set_Contains(Domain(TreiberPoolLow, loc_t), One(loc_n->t)));
preserves (forall loc_n: Loc :: Set_Contains(Domain(TreiberPoolLow, loc_t), One(loc_n)) ==>
              (var loc_n' := Map_At(Map_At(TreiberPoolLow, One(loc_t))->nodes, One(loc_n))->next;
                loc_n' is None || Set_Contains(Domain(TreiberPoolLow, loc_t), One(loc_n'->t))));

yield invariant {:layer 1} LocInStackOrNone(loc_t: Loc, loc_n: Option Loc);
preserves Map_Contains(TreiberPoolLow, One(loc_t));
preserves loc_n is None || Set_Contains(Domain(TreiberPoolLow, loc_t), One(loc_n->t));

yield invariant {:layer 2} ReachInStack(loc_t: Loc);
preserves Map_Contains(TreiberPoolLow, One(loc_t));
preserves (var t := Map_At(TreiberPoolLow, One(loc_t)); Between(t->nodes->val, t->top, t->top, None()));
preserves (var t := Map_At(TreiberPoolLow, One(loc_t)); ListInDomain(t));
preserves (var loc_n := Map_At(TreiberPoolLow, One(loc_t))->top; loc_n is None || Set_Contains(Domain(TreiberPoolLow, loc_t), One(loc_n->t)));
preserves Map_At(TreiberPool, One(loc_t)) == Abs(Map_At(TreiberPoolLow, One(loc_t)));

yield invariant {:layer 2} StackDom();
preserves TreiberPool->dom == TreiberPoolLow->dom;

yield invariant {:layer 2} PushLocInStack(loc_t: Loc, new_top: Loc, new_node: Node X, {:linear} tag: One (Tag Unit));
preserves Map_Contains(TreiberPoolLow, One(loc_t));
preserves Set_Contains(Domain(TreiberPoolLow, loc_t), One(new_top));
preserves tag->val == Tag(new_top, Unit());
preserves (var t := Map_At(TreiberPoolLow, One(loc_t)); Map_At(t->nodes, One(new_top)) == new_node && !BetweenSet(t->nodes->val, t->top, None())[new_top]);

/// Layered implementation

atomic action {:layer 3} AtomicAlloc() returns ({:linear} tag: One (Tag Unit))
{
  var one_loc_t: One Loc;
  var tags: Set (One (Tag Unit));

  call one_loc_t, tags := Tags_New(UnitSet());
  tag := One(Tag(one_loc_t->val, Unit()));
  call One_Get(tags, tag);
  assume !Map_Contains(TreiberPool, one_loc_t);
  TreiberPool := Map_Update(TreiberPool, one_loc_t, Vec_Empty());
}
yield procedure {:layer 2} Alloc() returns ({:linear} tag: One (Tag Unit))
refines AtomicAlloc;
ensures call TopInStack(tag->val->loc);
ensures call ReachInStack(tag->val->loc);
preserves call StackDom();
{
  var one_loc_t: One Loc;
  var tags: Set (One (Tag Unit));
  var top: Option Loc;
  var stack: Map (One Loc) (Node X);
  var treiber: Treiber X;

  top := None();
  call stack := Map_MakeEmpty();
  treiber := Treiber(top, stack);
  call one_loc_t, tags := Tags_New(UnitSet());
  tag := One(Tag(one_loc_t->val, Unit()));
  call One_Get(tags, tag);
  call AllocTreiber#0(one_loc_t, treiber);
  call {:layer 2} TreiberPool := Copy(Map_Update(TreiberPool, one_loc_t, Vec_Empty()));
  call {:layer 2} AbsLemma(treiber);
}

atomic action {:layer 3} AtomicPush(loc_t: Loc, x: X) returns (success: bool)
{
  if (*) {
    TreiberPool := Map_Update(TreiberPool, One(loc_t), Vec_Append(Map_At(TreiberPool, One(loc_t)), x));
    success := true;
  } else {
    success := false;
  }
}
yield procedure {:layer 2} {:vcs_split_on_every_assert} Push(loc_t: Loc, x: X) returns (success: bool)
refines AtomicPush;
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
preserves call StackDom();
{
  var old_top: Option Loc;
  var new_top: Loc;
  var tag: One (Tag Unit);
  var {:layer 2} old_treiber: Treiber X;

  call {:layer 2} old_treiber := Copy(TreiberPoolLow->val[One(loc_t)]);
  call old_top, new_top, tag := AllocNode#1(loc_t, x);
  call {:layer 2} FrameLemma(old_treiber, TreiberPoolLow->val[One(loc_t)]);
  call ReachInStack(loc_t) | StackDom() | PushLocInStack(loc_t, new_top, Node(old_top, x), tag);
  call success := WriteTopOfStack#0(loc_t, old_top, Some(new_top));
  if (success) {
    call {:layer 2} TreiberPool := Copy(Map_Update(TreiberPool, One(loc_t), Vec_Append(Map_At(TreiberPool, One(loc_t)), x)));
    assert {:layer 2} TreiberPoolLow->val[One(loc_t)]->top != None();
    call {:layer 2} AbsLemma(TreiberPoolLow->val[One(loc_t)]);
  }
}

atomic action {:layer 3} AtomicPop(loc_t: Loc) returns (success: bool, x_opt: Option X)
{
  var stack: Vec X;

  if (*) {
    stack := Map_At(TreiberPool, One(loc_t));
    if (Vec_Len(stack) > 0) {
      x_opt := Some(Vec_Nth(stack, Vec_Len(stack) - 1));
      TreiberPool := Map_Update(TreiberPool, One(loc_t), Vec_Remove(stack));
    } else {
      x_opt := None();
    }
    success := true;
  } else {
    success := false;
    x_opt := None();
  }
}
yield procedure {:layer 2} Pop(loc_t: Loc) returns (success: bool, x_opt: Option X)
refines AtomicPop;
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
preserves call StackDom();
{
  call {:layer 2} AbsLemma(TreiberPoolLow->val[One(loc_t)]);
  call success, x_opt := PopIntermediate(loc_t);
  if (x_opt is Some) {
    assert {:layer 2} Vec_Len(Map_At(TreiberPool, One(loc_t))) > 0;
    call {:layer 2} TreiberPool := Copy(Map_Update(TreiberPool, One(loc_t), Vec_Remove(Map_At(TreiberPool, One(loc_t)))));
  }
}

atomic action {:layer 2} AtomicAllocNode#1(loc_t: Loc, x: X)
  returns (old_top: Option Loc, new_top: Loc, {:linear} tag: One (Tag Unit))
asserts Map_Contains(TreiberPoolLow, One(loc_t));
{
  var one_loc_t: One Loc;
  var treiber: Treiber X;
  var top: Option Loc;
  var stack: Map (One Loc) (Node X);
  var one_loc_n: One Loc;
  var tags: Set (One (Tag Unit));
  
  one_loc_t := One(loc_t);
  call treiber := Map_Get(TreiberPoolLow, one_loc_t);
  Treiber(top, stack) := treiber;
  assume old_top is None || Map_Contains(stack, One(old_top->t));
  call one_loc_n, tags := Tags_New(UnitSet());
  new_top := one_loc_n->val;
  tag := One(Tag(new_top, Unit()));
  call One_Get(tags, tag);
  call Map_Put(stack, one_loc_n, Node(old_top, x));
  treiber := Treiber(top, stack);
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}
yield procedure {:layer 1} AllocNode#1(loc_t: Loc, x: X)
  returns (old_top: Option Loc, new_top: Loc, {:linear} tag: One (Tag Unit))
preserves call TopInStack(loc_t);
ensures call LocInStackOrNone(loc_t, Some(new_top));
refines AtomicAllocNode#1;
{
  var one_loc_n: One Loc;
  var tags: Set (One (Tag Unit));

  call old_top := ReadTopOfStack#0(loc_t);
  call LocInStackOrNone(loc_t, old_top) | TopInStack(loc_t);
  call one_loc_n, tags := Tags_New(UnitSet());
  new_top := one_loc_n->val;
  tag := One(Tag(new_top, Unit()));
  call One_Get(tags, tag);
  call AllocNode#0(loc_t, one_loc_n, Node(old_top, x));
}

atomic action {:layer 2} AtomicPopIntermediate(loc_t: Loc) returns (success: bool, x_opt: Option X)
{
  var one_loc_t: One Loc;
  var loc_n: Option Loc;
  var treiber: Treiber X;
  var top: Option Loc;
  var stack: Map (One Loc) (Node X);
  var x: X;

  assert Map_Contains(TreiberPoolLow, One(loc_t));
  if (*) {
    one_loc_t := One(loc_t);
    call treiber := Map_Get(TreiberPoolLow, one_loc_t);
    Treiber(top, stack) := treiber;
    assume top is Some && Map_Contains(stack, One(top->t));
    Node(loc_n, x) := Map_At(stack, One(top->t));
    treiber := Treiber(loc_n, stack);
    call Map_Put(TreiberPoolLow, one_loc_t, treiber);
    x_opt := Some(x);
    success := true;
  }
  else if (*) {
    assume Map_At(TreiberPoolLow, One(loc_t))->top is None;
    x_opt := None();
    success := true;
  } else {
    x_opt := None();
    success := false;
  }
}
yield procedure {:layer 1} PopIntermediate(loc_t: Loc) returns (success: bool, x_opt: Option X)
refines AtomicPopIntermediate;
preserves call TopInStack(loc_t);
{
  var loc_n, new_loc_n: Option Loc;
  var node: Node X;
  var x: X;

  call loc_n := ReadTopOfStack#0(loc_t);
  if (loc_n == None()) {
    x_opt := None();
    success := true;
    return;
  }
  call LocInStackOrNone(loc_t, loc_n) | TopInStack(loc_t);
  call node := LoadNode#0(loc_t, loc_n->t);
  Node(new_loc_n, x) := node;
  call success := WriteTopOfStack#0(loc_t, loc_n, new_loc_n);
  if (success) {
    x_opt := Some(x);
  } else {
    x_opt := None();
  }
}

/// Primitives

yield procedure {:layer 0} LoadNode#0(loc_t: Loc, loc_n: Loc) returns (node: Node X);
refines right action {:layer 1} _
{
  assert Map_Contains(TreiberPoolLow, One(loc_t));
  assert Map_Contains(Map_At(TreiberPoolLow, One(loc_t))->nodes, One(loc_n));
  node := TreiberPoolLow->val[One(loc_t)]->nodes->val[One(loc_n)];
}

yield procedure {:layer 0} ReadTopOfStack#0(loc_t: Loc) returns (loc_n: Option Loc);
refines atomic action {:layer 1} _
{
  assert Map_Contains(TreiberPoolLow, One(loc_t));
  loc_n := TreiberPoolLow->val[One(loc_t)]->top;
}

yield procedure {:layer 0} WriteTopOfStack#0(
  loc_t: Loc, old_loc_n: Option Loc, new_loc_n: Option Loc) returns (success: bool);
refines atomic action {:layer 1,2} _
{
  assert Map_Contains(TreiberPoolLow, One(loc_t));
  if (old_loc_n == TreiberPoolLow->val[One(loc_t)]->top) {
    TreiberPoolLow->val[One(loc_t)]->top := new_loc_n;
    success := true;
  } else {
    success := false;
  }
}

yield procedure {:layer 0} AllocNode#0(loc_t: Loc, {:linear_in} one_loc_n: One Loc, node: Node X);
refines atomic action {:layer 1} _
{
  var one_loc_t: One Loc;
  var treiber: Treiber X;

  one_loc_t := One(loc_t);
  call treiber := Map_Get(TreiberPoolLow, one_loc_t);
  call Map_Put(treiber->nodes, one_loc_n, node);
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}

yield procedure {:layer 0} AllocTreiber#0({:linear_in} one_loc_t: One Loc, {:linear_in} treiber: Treiber X);
refines atomic action {:layer 1,2} _
{
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}

/// Proof of abstraction with a manual encoding of termination

// Abs and AbsDefinition together model the abstraction function
function Abs(treiber: Treiber X): Vec X;
function {:inline} AbsDefinition(treiber: Treiber X): Vec X {
if treiber->top == None() then
  Vec_Empty() else
  (var n := Map_At(treiber->nodes, One(treiber->top->t));
    (var treiber' := Treiber(n->next, treiber->nodes); 
      Vec_Append(Abs(treiber'), n->val)))
}

pure procedure AbsCompute(treiber: Treiber X, treiber': Treiber X) returns (absStack: Vec X)
requires treiber->top == treiber'->top;
requires IsSubset(treiber->nodes->dom->val, treiber'->nodes->dom->val);
requires MapIte(treiber->nodes->dom->val, treiber->nodes->val, MapConst(Default())) ==
         MapIte(treiber->nodes->dom->val, treiber'->nodes->val, MapConst(Default()));
requires Between(treiber->nodes->val, treiber->top, treiber->top, None());
requires ListInDomain(treiber);
ensures absStack == AbsDefinition(treiber);
ensures absStack == AbsDefinition(treiber');
free ensures absStack == Abs(treiber);
free ensures absStack == Abs(treiber');
{
  var loc_n: Option Loc;
  var n: Node X;

  if (treiber->top == None()) {
      absStack := Vec_Empty();
  } else {
      loc_n := treiber->top;
      assert Map_Contains(treiber->nodes, One(loc_n->t));
      n := Map_At(treiber->nodes, One(loc_n->t));
      // Use well-founded list reachability to prove that recursion will terminate:
      // treiber@caller->top --> treiber@callee->top --> None()
      assert Between(treiber->nodes->val, loc_n, n->next, None());
      call absStack := AbsCompute(Treiber(n->next, treiber->nodes), Treiber(n->next, treiber'->nodes));
      absStack := Vec_Append(absStack, n->val);
  }
}

/// Useful lemmas obtained by wrapping AbsCompute

pure procedure AbsLemma(treiber: Treiber X)
requires Between(treiber->nodes->val, treiber->top, treiber->top, None());
requires ListInDomain(treiber);
ensures Abs(treiber) == AbsDefinition(treiber);
{
  var absStack: Vec X;
  call absStack := AbsCompute(treiber, treiber);
}

pure procedure FrameLemma(treiber: Treiber X, treiber': Treiber X)
requires treiber->top == treiber'->top;
requires IsSubset(treiber->nodes->dom->val, treiber'->nodes->dom->val);
requires MapIte(treiber->nodes->dom->val, treiber->nodes->val, MapConst(Default())) ==
         MapIte(treiber->nodes->dom->val, treiber'->nodes->val, MapConst(Default()));
requires Between(treiber->nodes->val, treiber->top, treiber->top, None());
requires ListInDomain(treiber);
ensures Abs(treiber) == Abs(treiber');
{
  var absStack: Vec X;
  call absStack := AbsCompute(treiber, treiber');
}
