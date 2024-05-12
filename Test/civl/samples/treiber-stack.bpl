// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type TreiberNode _;
type LocTreiberNode T = Loc (TreiberNode T);
type StackElem T = Node (LocTreiberNode T) T;
type StackMap T = Map (LocTreiberNode T) (StackElem T);
datatype Treiber<T> { Treiber(top: Option (LocTreiberNode T), {:linear} stack: StackMap T) }

type X; // module type parameter

var {:layer 4, 5} Stack: Map (Loc (Treiber X)) (Vec X);
var {:layer 0, 4} {:linear} ts: Map (Loc (Treiber X)) (Treiber X);

atomic action {:layer 5} AtomicAlloc() returns (loc_t: Loc (Treiber X))
modifies Stack;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));

  call one_loc_t := One_New();
  loc_t := one_loc_t->val;
  assume !Map_Contains(Stack, loc_t);
  Stack := Map_Update(Stack, loc_t, Vec_Empty());
}
yield procedure {:layer 4} Alloc() returns (loc_t: Loc (Treiber X))
refines AtomicAlloc;
preserves call YieldInvDom#4();
{
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} treiber: Treiber X;
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  top := None();
  call stack := Map_MakeEmpty();
  treiber := Treiber(top, stack);
  call one_loc_t := One_New();
  call cell_t := Cell_Pack(one_loc_t, treiber);
  loc_t := one_loc_t->val;
  call AllocTreiber(cell_t);
  call {:layer 4} Stack := Copy(Map_Update(Stack, loc_t, Vec_Empty()));
  call {:layer 4} AbsLemma(treiber);
}

atomic action {:layer 5} AtomicPush(loc_t: Loc (Treiber X), x: X) returns (success: bool)
modifies Stack;
{
  if (success) {
    Stack := Map_Update(Stack, loc_t, Vec_Append(Map_At(Stack, loc_t), x));
  }
}
yield procedure {:layer 4} Push(loc_t: Loc (Treiber X), x: X) returns (success: bool)
refines AtomicPush;
preserves call YieldInv#2(loc_t);
preserves call YieldInv#4(loc_t);
preserves call YieldInvDom#4();
{
  var {:layer 4} old_treiber: Treiber X;

  call {:layer 4} old_treiber := Copy(ts->val[loc_t]);
  call success := PushIntermediate(loc_t, x);
  if (success) {
    call {:layer 4} FrameLemma(old_treiber, ts->val[loc_t]->stack);
    call {:layer 4} Stack := Copy(Map_Update(Stack, loc_t, Vec_Append(Map_At(Stack, loc_t), x)));
    assert {:layer 4} ts->val[loc_t]->top != None();
    call {:layer 4} AbsLemma(ts->val[loc_t]);
  }
}

atomic action {:layer 5} AtomicPop(loc_t: Loc (Treiber X)) returns (success: bool, x: X)
modifies Stack;
{
  var stack: Vec X;

  if (success) {
    stack := Map_At(Stack, loc_t);
    assume Vec_Len(stack) > 0;
    x := Vec_Nth(stack, Vec_Len(stack) - 1);
    Stack := Map_Update(Stack, loc_t, Vec_Remove(stack));
  }
}
yield procedure {:layer 4} Pop(loc_t: Loc (Treiber X)) returns (success: bool, x: X)
refines AtomicPop;
preserves call YieldInv#2(loc_t);
preserves call YieldInv#3(loc_t);
preserves call YieldInv#4(loc_t);
preserves call YieldInvDom#4();
{
  call {:layer 4} AbsLemma(ts->val[loc_t]);
  call success, x := PopIntermediate(loc_t);
  if (success) {
    assert {:layer 4} Vec_Len(Map_At(Stack, loc_t)) > 0;
    call {:layer 4} Stack := Copy(Map_Update(Stack, loc_t, Vec_Remove(Map_At(Stack, loc_t))));
  }
}

atomic action {:layer 4} AtomicPopIntermediate(loc_t: Loc (Treiber X)) returns (success: bool, x: X)
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var loc_n: Option (LocTreiberNode X);
  var {:linear} treiber: Treiber X;
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  assume Map_Contains(ts, loc_t);
  if (success) {
    call cell_t := Map_Get(ts, loc_t);
    call one_loc_t, treiber := Cell_Unpack(cell_t);
    Treiber(top, stack) := treiber;
    assume top != None();
    assume Map_Contains(stack, top->t);
    Node(loc_n, x) := Map_At(stack, top->t);
    treiber := Treiber(loc_n, stack);
    call cell_t := Cell_Pack(one_loc_t, treiber);
    call Map_Put(ts, cell_t);
  }
}
yield procedure {:layer 3} PopIntermediate(loc_t: Loc (Treiber X)) returns (success: bool, x: X)
refines AtomicPopIntermediate;
preserves call YieldInv#2(loc_t);
preserves call YieldInv#3(loc_t);
{
  var loc_n, new_loc_n: Option (LocTreiberNode X);
  var node: StackElem X;

  success := false;
  call loc_n := ReadTopOfStack#Pop(loc_t);
  if (loc_n == None()) {
    return;
  }
  call node := LoadNode(loc_t, loc_n->t);
  Node(new_loc_n, x) := node;
  call success := WriteTopOfStack#Pop(loc_t, loc_n, new_loc_n);
}

atomic action {:layer 3, 4} AtomicPushIntermediate(loc_t: Loc (Treiber X), x: X) returns (success: bool)
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} one_loc_n: One (LocTreiberNode X);
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  success := false;
  if (*) {
    success := true;
    call cell_t := Map_Get(ts, loc_t);
    call one_loc_t, treiber := Cell_Unpack(cell_t);
    Treiber(top, stack) := treiber;
    call one_loc_n := One_New();
    call cell_n := Cell_Pack(one_loc_n, Node(top, x));
    call Map_Put(stack, cell_n);
    treiber := Treiber(Some(one_loc_n->val), stack);
    call cell_t := Cell_Pack(one_loc_t, treiber);
    call Map_Put(ts, cell_t);
  }
}
yield procedure {:layer 2} PushIntermediate(loc_t: Loc (Treiber X), x: X) returns (success: bool)
refines AtomicPushIntermediate;
preserves call YieldInv#2(loc_t);
{
  var loc_n: Option (LocTreiberNode X);
  var new_loc_n: LocTreiberNode X;
  var {:linear} one_loc_n: One (LocTreiberNode X);
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);

  call loc_n := ReadTopOfStack#Push(loc_t);
  call one_loc_n := One_New();
  new_loc_n := one_loc_n->val;
  call cell_n := Cell_Pack(one_loc_n, Node(loc_n, x));
  call success := WriteTopOfStack(loc_t, loc_n, Some(new_loc_n));
  if (success) {
    call AllocNode(loc_t, cell_n);
  }
}

right action {:layer 3} AtomicReadTopOfStack#Pop(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
{
  assert Map_Contains(ts, loc_t);
  assume loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t);
}
yield procedure {:layer 2} ReadTopOfStack#Pop(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
refines AtomicReadTopOfStack#Pop;
preserves call YieldInv#2(loc_t);
{
  call loc_n := ReadTopOfStack(loc_t);
}

right action {:layer 2} AtomicReadTopOfStack#Push(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
{
  assert Map_Contains(ts, loc_t);
}
yield procedure {:layer 1} ReadTopOfStack#Push(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
refines AtomicReadTopOfStack#Push;
{
  call loc_n := ReadTopOfStack(loc_t);
}

right action {:layer 3} AtomicLoadNode(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X)
modifies ts;
{
  assert Map_Contains(ts, loc_t);
  assert Map_Contains(Map_At(ts, loc_t)->stack, loc_n);
  node := Map_At(Map_At(ts, loc_t)->stack, loc_n);
}
yield procedure {:layer 2} LoadNode(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X)
refines AtomicLoadNode;
preserves call YieldInv#2(loc_t);
{
  call node := LoadNode#0(loc_t, loc_n);
}

atomic action {:layer 3} AtomicWriteTopOfStack#Pop(
  loc_t: Loc (Treiber X), old_loc_n: Option (LocTreiberNode X), new_loc_n: Option (LocTreiberNode X)) returns (r: bool)
modifies ts;
{
  assert new_loc_n is None || Set_Contains(Domain(ts, loc_t), new_loc_n->t);
  call r := AtomicWriteTopOfStack(loc_t, old_loc_n, new_loc_n);
}
yield procedure {:layer 2} WriteTopOfStack#Pop(
  loc_t: Loc (Treiber X), old_loc_n: Option (LocTreiberNode X), new_loc_n: Option (LocTreiberNode X)) returns (r: bool)
refines AtomicWriteTopOfStack#Pop;
preserves call YieldInv#2(loc_t);
{
  call r := WriteTopOfStack(loc_t, old_loc_n, new_loc_n);
}

atomic action {:layer 1, 2} AtomicReadTopOfStack(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  loc_n := treiber->top;
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} ReadTopOfStack(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X));
refines AtomicReadTopOfStack;

atomic action {:layer 1,2} AtomicLoadNode#0(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X)
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} one_loc_n: One (LocTreiberNode X);
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  Treiber(top, stack) := treiber;
  assume Map_Contains(stack, loc_n); // problematic assume
  call cell_n := Map_Get(stack, loc_n);
  call one_loc_n, node := Cell_Unpack(cell_n);
  call cell_n := Cell_Pack(one_loc_n, node);
  call Map_Put(stack, cell_n);
  treiber := Treiber(top, stack);
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} LoadNode#0(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X);
refines AtomicLoadNode#0;

left action {:layer 1, 2} AtomicAllocNode(
  loc_t: Loc (Treiber X), {:linear_in} cell_n: Cell (LocTreiberNode X) (StackElem X))
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  call Map_Put(treiber->stack, cell_n);
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} AllocNode(
  loc_t: Loc (Treiber X), {:linear_in} cell_n: Cell (LocTreiberNode X) (StackElem X));
refines AtomicAllocNode;

atomic action {:layer 1, 3} AtomicWriteTopOfStack(
  loc_t: Loc (Treiber X), old_loc_n: Option (LocTreiberNode X), new_loc_n: Option (LocTreiberNode X)) returns (r: bool)
modifies ts;
{
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var {:linear} one_loc_t: One (Loc (Treiber X));

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  if (old_loc_n == treiber->top) {
    treiber->top := new_loc_n;
    r := true;
  } else {
    r := false;
  }
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} WriteTopOfStack(
  loc_t: Loc (Treiber X), old_loc_n: Option (LocTreiberNode X), new_loc_n: Option (LocTreiberNode X)) returns (r: bool);
refines AtomicWriteTopOfStack;

atomic action {:layer 1, 4} AtomicAllocTreiber({:linear_in} cell_t: Cell (Loc (Treiber X)) (Treiber X))
modifies ts;
{
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} AllocTreiber({:linear_in} cell_t: Cell (Loc (Treiber X)) (Treiber X));
refines AtomicAllocTreiber;

function {:inline} Domain(ts: Map (Loc (Treiber X)) (Treiber X), loc_t: Loc (Treiber X)): Set (LocTreiberNode X) {
  ts->val[loc_t]->stack->dom
}

yield invariant {:layer 2} YieldInv#2(loc_t: Loc (Treiber X));
invariant Map_Contains(ts, loc_t);
invariant (var loc_n := Map_At(ts, loc_t)->top; loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t));

yield invariant {:layer 3} YieldInv#3(loc_t: Loc (Treiber X));
invariant Map_Contains(ts, loc_t);
invariant (var loc_n := Map_At(ts, loc_t)->top; loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t));
invariant (forall loc_n: LocTreiberNode X ::
              Set_Contains(Domain(ts, loc_t), loc_n) ==> 
              (var loc_n' := Map_At(Map_At(ts, loc_t)->stack, loc_n)->next; 
                    loc_n' is None || Set_Contains(Domain(ts, loc_t), loc_n'->t)));

yield invariant {:layer 4} YieldInv#4(loc_t: Loc (Treiber X));
invariant Map_Contains(ts, loc_t);
invariant Map_At(Stack, loc_t) == Abs(Map_At(ts, loc_t));
invariant (var t := ts->val[loc_t]; Between(t->stack->val, t->top, t->top, None()));
invariant (var t := ts->val[loc_t]; IsSubset(BetweenSet(t->stack->val, t->top, None()), Domain(ts, loc_t)->val));

yield invariant {:layer 4} YieldInvDom#4();
invariant Stack->dom == ts->dom;

// The following is a manual encoding of the termination proof for the abstraction.
function Abs(treiber: Treiber X): Vec X;

function {:inline} AbsDefinition(treiber: Treiber X): Vec X {
if treiber->top == None() then
  Vec_Empty() else
  (var n := Map_At(treiber->stack, treiber->top->t);
    (var treiber' := Treiber(n->next, treiber->stack); 
      Vec_Append(Abs(treiber'), n->val)))
}

pure procedure AbsCompute(treiber: Treiber X) returns (absStack: Vec X)
requires Between(treiber->stack->val, treiber->top, treiber->top, None());
requires IsSubset(BetweenSet(treiber->stack->val, treiber->top, None()), treiber->stack->dom->val);
ensures absStack == AbsDefinition(treiber);
free ensures absStack == Abs(treiber);
{
  var loc_n: Option (LocTreiberNode X);
  var n: StackElem X;

  if (treiber->top == None()) {
      absStack := Vec_Empty();
  } else {
      loc_n := treiber->top;
      assert Map_Contains(treiber->stack, loc_n->t); // soundness of framing
      n := Map_At(treiber->stack, loc_n->t);
      assert Between(treiber->stack->val, loc_n, n->next, None()); // soundness of termination (for induction)
      call absStack := AbsCompute(Treiber(n->next, treiber->stack));
      absStack := Vec_Append(absStack, n->val);
  }
}

pure procedure AbsLemma(treiber: Treiber X)
requires Between(treiber->stack->val, treiber->top, treiber->top, None());
requires IsSubset(BetweenSet(treiber->stack->val, treiber->top, None()), treiber->stack->dom->val);
ensures Abs(treiber) == AbsDefinition(treiber);
{
  var absStack: Vec X;
  call absStack := AbsCompute(treiber);
}

pure procedure FrameLemma(treiber: Treiber X, map': StackMap X);
requires Between(treiber->stack->val, treiber->top, treiber->top, None());
requires IsSubset(BetweenSet(treiber->stack->val, treiber->top, None()), treiber->stack->dom->val);
requires IsSubset(treiber->stack->dom->val, map'->dom->val);
requires MapIte(treiber->stack->dom->val, treiber->stack->val, MapConst(Default())) == 
         MapIte(treiber->stack->dom->val, map'->val, MapConst(Default()));
ensures Abs(treiber) == Abs(Treiber(treiber->top, map'));
