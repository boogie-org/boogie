// RUN: %parallel-boogie -lib:base -lib:node -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Treiber<V> { Treiber(top: Option Loc, nodes: Map (One Loc) (Node V)) }

type X; // module type parameter

var {:layer 2, 3} TreiberPool: Map (One Loc) (Vec X);
var {:layer 0, 2} {:linear} TreiberPoolLow: Map (One Loc) (Treiber X);

/// Yield invariants

function {:inline} Domain(ts: Map (One Loc) (Treiber X), loc_t: Loc): [One Loc]bool {
  ts->val[One(loc_t)]->nodes->dom
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
preserves (var t := Map_At(TreiberPoolLow, One(loc_t)); InDomain(t->nodes, t->top));
preserves (var loc_n := Map_At(TreiberPoolLow, One(loc_t))->top; loc_n is None || Set_Contains(Domain(TreiberPoolLow, loc_t), One(loc_n->t)));
preserves (var t := Map_At(TreiberPoolLow, One(loc_t)); Map_At(TreiberPool, One(loc_t)) == StackAbs(t->top, t->nodes));

yield invariant {:layer 2} StackDom();
preserves TreiberPool->dom == TreiberPoolLow->dom;

yield invariant {:layer 2} PushLocInStack(loc_t: Loc, new_top: Loc, new_node: Node X, {:linear} tag: One (Tag Unit));
preserves Map_Contains(TreiberPoolLow, One(loc_t));
preserves new_top == tag->val->loc;
preserves Set_Contains(Domain(TreiberPoolLow, loc_t), One(new_top));
preserves (var t := Map_At(TreiberPoolLow, One(loc_t));
            Map_At(t->nodes, One(new_top)) == new_node && !Between(t->nodes->val, t->top, Some(new_top), None()));

/// Layered implementation

atomic action {:layer 3} AtomicAlloc() returns ({:linear} tag: One (Tag Unit))
{
  var one_loc_t: One Loc;

  call one_loc_t, tag := Tag_New();
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
  var top: Option Loc;
  var stack: Map (One Loc) (Node X);
  var treiber: Treiber X;

  top := None();
  call stack := Map_MakeEmpty();
  treiber := Treiber(top, stack);
  call one_loc_t, tag := Tag_New();
  call AllocTreiber(one_loc_t, treiber);
  call {:layer 2} TreiberPool := Copy(Map_Update(TreiberPool, one_loc_t, Vec_Empty()));
  call {:layer 2} StackAbsLemma(treiber->top, treiber->nodes);
}

atomic action {:layer 3} AtomicPush(loc_t: Loc, x: X)
{
  TreiberPool := Map_Update(TreiberPool, One(loc_t), Vec_Append(Map_At(TreiberPool, One(loc_t)), x));
}
yield procedure {:layer 2} Push(loc_t: Loc, x: X)
refines AtomicPush;
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
preserves call StackDom();
{
  var old_top: Option Loc;
  var new_top: Loc;
  var tag: One (Tag Unit);
  var {:layer 2} old_treiber, mid_treiber, new_treiber: Treiber X;
  var success: bool;

  while (true)
  invariant {:yields} true;
  invariant call TopInStack(loc_t);
  invariant call ReachInStack(loc_t);
  invariant call StackDom();
  {
    call {:layer 2} old_treiber := Copy(TreiberPoolLow->val[One(loc_t)]);
    call old_top, tag := AddNode(loc_t, x);
    call {:layer 2} mid_treiber := Copy(TreiberPoolLow->val[One(loc_t)]);
    call {:layer 2} StackFrameLemma(old_treiber->top, old_treiber->nodes, mid_treiber->nodes);
    new_top := tag->val->loc;
    call ReachInStack(loc_t) | StackDom() | PushLocInStack(loc_t, new_top, Node(old_top, x), tag);
    call success := WriteTopOfStack(loc_t, old_top, Some(new_top));
    if (success) {
      call {:layer 2} new_treiber := Copy(TreiberPoolLow->val[One(loc_t)]);
      assert {:layer 2} Map_Contains(TreiberPool, One(loc_t));
      call {:layer 2} TreiberPool := Copy(Map_Update(TreiberPool, One(loc_t), Vec_Append(Map_At(TreiberPool, One(loc_t)), x)));
      call {:layer 2} StackAbsLemma(new_treiber->top, new_treiber->nodes);
      break;
    }
  }
}

atomic action {:layer 3} AtomicPop(loc_t: Loc) returns (x_opt: Option X)
{
  var stack: Vec X;

  stack := Map_At(TreiberPool, One(loc_t));
  if (Vec_Len(stack) > 0) {
    x_opt := Some(Vec_Nth(stack, Vec_Len(stack) - 1));
    TreiberPool := Map_Update(TreiberPool, One(loc_t), Vec_Remove(stack));
  } else {
    x_opt := None();
  }
}
yield procedure {:layer 2} Pop(loc_t: Loc) returns (x_opt: Option X)
refines AtomicPop;
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
preserves call StackDom();
{
  var {:layer 2} treiber: Treiber X;
  var success: bool;

  while (true)
  invariant {:yields} true;
  invariant call TopInStack(loc_t);
  invariant call ReachInStack(loc_t);
  invariant call StackDom();
  {
    call {:layer 2} treiber := Copy(TreiberPoolLow->val[One(loc_t)]);
    call {:layer 2} StackAbsLemma(treiber->top, treiber->nodes);
    call success, x_opt := PopIntermediate(loc_t);
    if (x_opt is Some) {
      assert {:layer 2} Vec_Len(Map_At(TreiberPool, One(loc_t))) > 0;
      call {:layer 2} TreiberPool := Copy(Map_Update(TreiberPool, One(loc_t), Vec_Remove(Map_At(TreiberPool, One(loc_t)))));
    }
    if (success) {
      break;
    }
  }
}

atomic action {:layer 2} AtomicAddNode(loc_t: Loc, x: X)
  returns (old_top: Option Loc, {:linear} tag: One (Tag Unit))
asserts Map_Contains(TreiberPoolLow, One(loc_t));
{
  var one_loc_t: One Loc;
  var treiber: Treiber X;
  var top: Option Loc;
  var stack: Map (One Loc) (Node X);
  var one_loc_n: One Loc;
  
  one_loc_t := One(loc_t);
  call treiber := Map_Get(TreiberPoolLow, one_loc_t);
  Treiber(top, stack) := treiber;
  assume old_top is None || Map_Contains(stack, One(old_top->t));
  call one_loc_n, tag := Tag_New();
  call Map_Put(stack, one_loc_n, Node(old_top, x));
  treiber := Treiber(top, stack);
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}
yield procedure {:layer 1} AddNode(loc_t: Loc, x: X)
  returns (old_top: Option Loc, {:linear} tag: One (Tag Unit))
preserves call TopInStack(loc_t);
ensures call LocInStackOrNone(loc_t, Some(tag->val->loc));
refines AtomicAddNode;
{
  var one_loc_n: One Loc;

  call old_top := ReadTopOfStack(loc_t);
  call LocInStackOrNone(loc_t, old_top) | TopInStack(loc_t);
  call one_loc_n, tag := Tag_New();
  call AllocNode(loc_t, one_loc_n, Node(old_top, x));
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

  call loc_n := ReadTopOfStack(loc_t);
  if (loc_n == None()) {
    x_opt := None();
    success := true;
    return;
  }
  call LocInStackOrNone(loc_t, loc_n) | TopInStack(loc_t);
  call node := LoadNode(loc_t, loc_n->t);
  Node(new_loc_n, x) := node;
  call success := WriteTopOfStack(loc_t, loc_n, new_loc_n);
  if (success) {
    x_opt := Some(x);
  } else {
    x_opt := None();
  }
}

/// Primitives

yield procedure {:layer 0} LoadNode(loc_t: Loc, loc_n: Loc) returns (node: Node X);
refines right action {:layer 1} _
{
  call node := Path_Load(TreiberPoolLow->val[One(loc_t)]->nodes->val[One(loc_n)]);
}

yield procedure {:layer 0} ReadTopOfStack(loc_t: Loc) returns (loc_n: Option Loc);
refines atomic action {:layer 1} _
{
  call loc_n := Path_Load(TreiberPoolLow->val[One(loc_t)]->top);
}

yield procedure {:layer 0} WriteTopOfStack(
  loc_t: Loc, old_loc_n: Option Loc, new_loc_n: Option Loc) returns (success: bool);
refines atomic action {:layer 1,2} _
{
  var loc_n: Option Loc;
  call loc_n := Path_Load(TreiberPoolLow->val[One(loc_t)]->top);
  if (old_loc_n == loc_n) {
    call Path_Store(TreiberPoolLow->val[One(loc_t)]->top, new_loc_n);
    success := true;
  } else {
    success := false;
  }
}

yield procedure {:layer 0} AllocNode(loc_t: Loc, {:linear_in} one_loc_n: One Loc, node: Node X);
refines atomic action {:layer 1} _
{
  call Map_Put(TreiberPoolLow->val[One(loc_t)]->nodes, one_loc_n, node);
}

yield procedure {:layer 0} AllocTreiber({:linear_in} one_loc_t: One Loc, {:linear_in} treiber: Treiber X);
refines atomic action {:layer 1,2} _
{
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}