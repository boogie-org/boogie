// RUN: %parallel-boogie -lib:base -lib:node -timeLimit:0 -vcsSplitOnEveryAssert "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype LocPiece { Right() }
function {:inline} AllLocPieces(): Set LocPiece {
  Set_Add(Set_Empty(), Right())
}

type LocTreiberStack = Loc;
type LocTreiberNode = Loc;
type StackElem T = Node LocTreiberNode T;
type StackMap T = Map LocTreiberNode (StackElem T);
datatype Treiber<T> { Treiber(top: Option LocTreiberNode, {:linear} nodes: StackMap T) }

type X; // module type parameter

var {:layer 4, 5} TreiberPool: Map Loc (Vec X);
var {:layer 0, 4} {:linear} TreiberPoolLow: Map Loc (Treiber X);

/// Proof outline
/*
Layer 1: Simplify LoadNode and convert its mover type to right mover
Layer 2: Create abstractions of ReadTopOfStack for Push and Pop separately
- right mover ReadTopOfStack#Push
- atomic ReadTopOfStack#Pop
Layer 3:
- Convert PopIntermediate to atomic action using right mover LoadNode
- Convert CreateNewTopOfStack to atomic action using right mover ReadTopOfStack#Push
Layer 4: Introduce TreiberPool and abstract TreiberPoolLow to TreiberPool
*/

/// Yield invariants

function {:inline} Domain(ts: Map LocTreiberStack (Treiber X), loc_t: LocTreiberStack): Set LocTreiberNode {
  ts->val[loc_t]->nodes->dom
}

yield invariant {:layer 1} Yield();

yield invariant {:layer 2} TopInStack(loc_t: LocTreiberStack);
invariant Map_Contains(TreiberPoolLow, loc_t);
invariant (var loc_n := Map_At(TreiberPoolLow, loc_t)->top; loc_n is None || Set_Contains(Domain(TreiberPoolLow, loc_t), loc_n->t));
invariant (forall loc_n: LocTreiberNode :: Set_Contains(Domain(TreiberPoolLow, loc_t), loc_n) ==>
              (var loc_n' := Map_At(Map_At(TreiberPoolLow, loc_t)->nodes, loc_n)->next; loc_n' is None || Set_Contains(Domain(TreiberPoolLow, loc_t), loc_n'->t)));

yield invariant {:layer 2} LocInStackOrNone(loc_t: LocTreiberStack, loc_n: Option LocTreiberNode);
invariant Map_Contains(TreiberPoolLow, loc_t);
invariant loc_n is None || Set_Contains(Domain(TreiberPoolLow, loc_t), loc_n->t);

yield invariant {:layer 3} LocInStack(loc_t: LocTreiberStack, loc_n: LocTreiberNode);
invariant Map_Contains(TreiberPoolLow, loc_t);
invariant Set_Contains(Domain(TreiberPoolLow, loc_t), loc_n);

yield invariant {:layer 4} ReachInStack(loc_t: LocTreiberStack);
invariant Map_Contains(TreiberPoolLow, loc_t);
invariant (var t := TreiberPoolLow->val[loc_t]; Between(t->nodes->val, t->top, t->top, None()));
invariant (var t := TreiberPoolLow->val[loc_t]; IsSubset(BetweenSet(t->nodes->val, t->top, None()), Domain(TreiberPoolLow, loc_t)->val));
invariant (var loc_n := Map_At(TreiberPoolLow, loc_t)->top; loc_n is None || Set_Contains(Domain(TreiberPoolLow, loc_t), loc_n->t));
invariant Map_At(TreiberPool, loc_t) == Abs(Map_At(TreiberPoolLow, loc_t));

yield invariant {:layer 4} StackDom();
invariant TreiberPool->dom == TreiberPoolLow->dom;

yield invariant {:layer 4} PushLocInStack(loc_t: LocTreiberStack, node: StackElem X, new_loc_n: LocTreiberNode, {:linear} right_loc_piece: One (TaggedLoc LocPiece));
invariant Map_Contains(TreiberPoolLow, loc_t);
invariant Set_Contains(Domain(TreiberPoolLow, loc_t), new_loc_n);
invariant right_loc_piece->val == TaggedLoc(new_loc_n, Right());
invariant (var t := TreiberPoolLow->val[loc_t]; Map_At(t->nodes, new_loc_n) == node && !BetweenSet(t->nodes->val, t->top, None())[new_loc_n]);

/// Layered implementation

atomic action {:layer 5} AtomicAlloc() returns ({:linear} right_loc_piece: One (TaggedLoc LocPiece))
{
  var {:linear} one_loc_t: One LocTreiberStack;
  var {:linear} loc_pieces: Set (TaggedLoc LocPiece);

  call one_loc_t, loc_pieces := TaggedLocSet_New(AllLocPieces());
  call right_loc_piece := One_Get(loc_pieces, TaggedLoc(one_loc_t->val, Right()));
  assume !Map_Contains(TreiberPool, one_loc_t->val);
  TreiberPool := Map_Update(TreiberPool, one_loc_t->val, Vec_Empty());
}
yield procedure {:layer 4} Alloc() returns ({:linear} right_loc_piece: One (TaggedLoc LocPiece))
refines AtomicAlloc;
ensures call TopInStack(right_loc_piece->val->loc);
ensures call ReachInStack(right_loc_piece->val->loc);
preserves call StackDom();
{
  var {:linear} one_loc_t: One LocTreiberStack;
  var {:linear} loc_pieces: Set (TaggedLoc LocPiece);
  var top: Option LocTreiberNode;
  var {:linear} stack: StackMap X;
  var {:linear} treiber: Treiber X;

  top := None();
  call stack := Map_MakeEmpty();
  treiber := Treiber(top, stack);
  call one_loc_t, loc_pieces := TaggedLocSet_New(AllLocPieces());
  call right_loc_piece := One_Get(loc_pieces, TaggedLoc(one_loc_t->val, Right()));
  call AllocTreiber#0(one_loc_t, treiber);
  call {:layer 4} TreiberPool := Copy(Map_Update(TreiberPool, one_loc_t->val, Vec_Empty()));
  call {:layer 4} AbsLemma(treiber);
}

atomic action {:layer 5} AtomicPush(loc_t: LocTreiberStack, x: X) returns (success: bool)
{
  if (*) {
    TreiberPool := Map_Update(TreiberPool, loc_t, Vec_Append(Map_At(TreiberPool, loc_t), x));
    success := true;
  } else {
    success := false;
  }
}
yield procedure {:layer 4} Push(loc_t: LocTreiberStack, x: X) returns (success: bool)
refines AtomicPush;
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
preserves call StackDom();
{
  var loc_n: Option LocTreiberNode;
  var new_loc_n: LocTreiberNode;
  var {:linear} right_loc_piece: One (TaggedLoc LocPiece);
  var {:layer 4} old_treiber: Treiber X;

  call {:layer 4} old_treiber := Copy(TreiberPoolLow->val[loc_t]);
  call loc_n, new_loc_n, right_loc_piece := CreateNewTopOfStack(loc_t, x);
  call {:layer 4} FrameLemma(old_treiber, TreiberPoolLow->val[loc_t]);
  par ReachInStack(loc_t) | StackDom() | PushLocInStack(loc_t, Node(loc_n, x), new_loc_n, right_loc_piece);
  call success := WriteTopOfStack#0(loc_t, loc_n, Some(new_loc_n));
  if (success) {
    call {:layer 4} TreiberPool := Copy(Map_Update(TreiberPool, loc_t, Vec_Append(Map_At(TreiberPool, loc_t), x)));
    assert {:layer 4} TreiberPoolLow->val[loc_t]->top != None();
    call {:layer 4} AbsLemma(TreiberPoolLow->val[loc_t]);
  }
}

atomic action {:layer 5} AtomicPop(loc_t: LocTreiberStack) returns (success: bool, x_opt: Option X)
{
  var stack: Vec X;

  if (*) {
    stack := Map_At(TreiberPool, loc_t);
    if (Vec_Len(stack) > 0) {
      x_opt := Some(Vec_Nth(stack, Vec_Len(stack) - 1));
      TreiberPool := Map_Update(TreiberPool, loc_t, Vec_Remove(stack));
    } else {
      x_opt := None();
    }
    success := true;
  } else {
    success := false;
    x_opt := None();
  }
}
yield procedure {:layer 4} Pop(loc_t: LocTreiberStack) returns (success: bool, x_opt: Option X)
refines AtomicPop;
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
preserves call StackDom();
{
  call {:layer 4} AbsLemma(TreiberPoolLow->val[loc_t]);
  call success, x_opt := PopIntermediate(loc_t);
  if (x_opt is Some) {
    assert {:layer 4} Vec_Len(Map_At(TreiberPool, loc_t)) > 0;
    call {:layer 4} TreiberPool := Copy(Map_Update(TreiberPool, loc_t, Vec_Remove(Map_At(TreiberPool, loc_t))));
  }
}

atomic action {:layer 4} AtomicCreateNewTopOfStack(loc_t: LocTreiberStack, x: X)
  returns (loc_n: Option LocTreiberNode, new_loc_n: LocTreiberNode, {:linear} right_loc_piece: One (TaggedLoc LocPiece))
asserts Map_Contains(TreiberPoolLow, loc_t);
{
  var {:linear} one_loc_t: One LocTreiberStack;
  var {:linear} treiber: Treiber X;
  var top: Option LocTreiberNode;
  var {:linear} stack: StackMap X;
  var {:linear} one_loc_n: One LocTreiberNode;
  var {:linear} loc_pieces: Set (TaggedLoc LocPiece);
  
  call one_loc_t, treiber := Map_Get(TreiberPoolLow, loc_t);
  Treiber(top, stack) := treiber;
  assume loc_n is None || Map_Contains(stack, loc_n->t);
  call one_loc_n, loc_pieces := TaggedLocSet_New(AllLocPieces());
  new_loc_n := one_loc_n->val;
  call right_loc_piece := One_Get(loc_pieces, TaggedLoc(new_loc_n, Right()));
  call Map_Put(stack, one_loc_n, Node(loc_n, x));
  treiber := Treiber(top, stack);
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}
yield procedure {:layer 3} CreateNewTopOfStack(loc_t: LocTreiberStack, x: X)
  returns (loc_n: Option LocTreiberNode, new_loc_n: LocTreiberNode, {:linear} right_loc_piece: One (TaggedLoc LocPiece))
preserves call TopInStack(loc_t);
ensures call LocInStackOrNone(loc_t, Some(new_loc_n));
refines AtomicCreateNewTopOfStack;
{
  var {:linear} one_loc_n: One LocTreiberNode;
  var {:linear} loc_pieces: Set (TaggedLoc LocPiece);

  call loc_n := ReadTopOfStack#Push(loc_t);
  call one_loc_n, loc_pieces := TaggedLocSet_New(AllLocPieces());
  new_loc_n := one_loc_n->val;
  call right_loc_piece := One_Get(loc_pieces, TaggedLoc(new_loc_n, Right()));
  call AllocNode#0(loc_t, one_loc_n, Node(loc_n, x));
}

atomic action {:layer 4} AtomicPopIntermediate(loc_t: LocTreiberStack) returns (success: bool, x_opt: Option X)
{
  var {:linear} one_loc_t: One LocTreiberStack;
  var loc_n: Option LocTreiberNode;
  var {:linear} treiber: Treiber X;
  var top: Option LocTreiberNode;
  var {:linear} stack: StackMap X;
  var x: X;

  assert Map_Contains(TreiberPoolLow, loc_t);
  if (*) {
    call one_loc_t, treiber := Map_Get(TreiberPoolLow, loc_t);
    Treiber(top, stack) := treiber;
    assume top is Some && Map_Contains(stack, top->t);
    Node(loc_n, x) := Map_At(stack, top->t);
    treiber := Treiber(loc_n, stack);
    call Map_Put(TreiberPoolLow, one_loc_t, treiber);
    x_opt := Some(x);
    success := true;
  }
  else if (*) {
    assume Map_At(TreiberPoolLow, loc_t)->top is None;
    x_opt := None();
    success := true;
  } else {
    x_opt := None();
    success := false;
  }
}
yield procedure {:layer 3} PopIntermediate(loc_t: LocTreiberStack) returns (success: bool, x_opt: Option X)
refines AtomicPopIntermediate;
preserves call TopInStack(loc_t);
{
  var loc_n, new_loc_n: Option LocTreiberNode;
  var node: StackElem X;
  var x: X;

  call loc_n := ReadTopOfStack#Pop(loc_t);
  if (loc_n == None()) {
    x_opt := None();
    success := true;
    return;
  }
  par LocInStack(loc_t, loc_n->t) | LocInStackOrNone(loc_t, loc_n) | TopInStack(loc_t);
  call node := LoadNode#0(loc_t, loc_n->t);
  call Yield();
  Node(new_loc_n, x) := node;
  call success := WriteTopOfStack#0(loc_t, loc_n, new_loc_n);
  if (success) {
    x_opt := Some(x);
  } else {
    x_opt := None();
  }
}

yield procedure {:layer 2} ReadTopOfStack#Push(loc_t: LocTreiberStack) returns (loc_n: Option LocTreiberNode)
preserves call TopInStack(loc_t);
ensures call LocInStackOrNone(loc_t, loc_n);
refines right action {:layer 3} _ {
  assert Map_Contains(TreiberPoolLow, loc_t);
  assume loc_n is None || Set_Contains(Domain(TreiberPoolLow, loc_t), loc_n->t);
}
{
  call loc_n := ReadTopOfStack#0(loc_t);
}

yield procedure {:layer 2} ReadTopOfStack#Pop(loc_t: LocTreiberStack) returns (loc_n: Option LocTreiberNode)
preserves call TopInStack(loc_t);
ensures call LocInStackOrNone(loc_t, loc_n);
refines atomic action {:layer 3} _
{
  assert Map_Contains(TreiberPoolLow, loc_t);
  assume if loc_n is None then Map_At(TreiberPoolLow, loc_t)->top is None else Set_Contains(Domain(TreiberPoolLow, loc_t), loc_n->t);
}
{
  call loc_n := ReadTopOfStack#0(loc_t);
}

right action {:layer 2,3} AtomicLoadNode#1(loc_t: LocTreiberStack, loc_n: LocTreiberNode) returns (node: StackElem X)
{
  assert Map_Contains(TreiberPoolLow, loc_t);
  assert Map_Contains(Map_At(TreiberPoolLow, loc_t)->nodes, loc_n);
  node := Map_At(Map_At(TreiberPoolLow, loc_t)->nodes, loc_n);
}

/// Primitives

atomic action {:layer 1} AtomicLoadNode#0(loc_t: LocTreiberStack, loc_n: LocTreiberNode) returns (node: StackElem X)
refines AtomicLoadNode#1;
{
  var {:linear} one_loc_t: One LocTreiberStack;
  var {:linear} treiber: Treiber X;
  var top: Option LocTreiberNode;
  var {:linear} stack: StackMap X;
  var {:linear} one_loc_n: One LocTreiberNode;

  call one_loc_t, treiber := Map_Get(TreiberPoolLow, loc_t);
  Treiber(top, stack) := treiber;
  call one_loc_n, node := Map_Get(stack, loc_n);
  call Map_Put(stack, one_loc_n, node);
  treiber := Treiber(top, stack);
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}
yield procedure {:layer 0} LoadNode#0(loc_t: LocTreiberStack, loc_n: LocTreiberNode) returns (node: StackElem X);
refines AtomicLoadNode#0;

yield procedure {:layer 0} ReadTopOfStack#0(loc_t: LocTreiberStack) returns (loc_n: Option LocTreiberNode);
refines atomic action {:layer 1,2} _
{
  var {:linear} one_loc_t: One LocTreiberStack;
  var {:linear} treiber: Treiber X;

  call one_loc_t, treiber := Map_Get(TreiberPoolLow, loc_t);
  loc_n := treiber->top;
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}

yield procedure {:layer 0} WriteTopOfStack#0(
  loc_t: LocTreiberStack, old_loc_n: Option LocTreiberNode, new_loc_n: Option LocTreiberNode) returns (success: bool);
refines atomic action {:layer 1,4} _
{
  var {:linear} one_loc_t: One LocTreiberStack;
  var {:linear} treiber: Treiber X;

  call one_loc_t, treiber := Map_Get(TreiberPoolLow, loc_t);
  if (old_loc_n == treiber->top) {
    treiber->top := new_loc_n;
    success := true;
  } else {
    success := false;
  }
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}

yield procedure {:layer 0} AllocNode#0(loc_t: LocTreiberStack, {:linear_in} one_loc_n: One LocTreiberNode, node: StackElem X);
refines atomic action {:layer 1,3} _
{
  var {:linear} one_loc_t: One LocTreiberStack;
  var {:linear} treiber: Treiber X;

  call one_loc_t, treiber := Map_Get(TreiberPoolLow, loc_t);
  call Map_Put(treiber->nodes, one_loc_n, node);
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}

yield procedure {:layer 0} AllocTreiber#0({:linear_in} one_loc_t: One LocTreiberStack, {:linear_in} treiber: Treiber X);
refines atomic action {:layer 1,4} _
{
  call Map_Put(TreiberPoolLow, one_loc_t, treiber);
}

/// Proof of abstraction with a manual encoding of termination

// Abs and AbsDefinition together model the abstraction function
function Abs(treiber: Treiber X): Vec X;
function {:inline} AbsDefinition(treiber: Treiber X): Vec X {
if treiber->top == None() then
  Vec_Empty() else
  (var n := Map_At(treiber->nodes, treiber->top->t);
    (var treiber' := Treiber(n->next, treiber->nodes); 
      Vec_Append(Abs(treiber'), n->val)))
}

pure procedure AbsCompute(treiber: Treiber X, treiber': Treiber X) returns (absStack: Vec X)
requires treiber->top == treiber'->top;
requires IsSubset(treiber->nodes->dom->val, treiber'->nodes->dom->val);
requires MapIte(treiber->nodes->dom->val, treiber->nodes->val, MapConst(Default())) ==
         MapIte(treiber->nodes->dom->val, treiber'->nodes->val, MapConst(Default()));
requires Between(treiber->nodes->val, treiber->top, treiber->top, None());
requires IsSubset(BetweenSet(treiber->nodes->val, treiber->top, None()), treiber->nodes->dom->val);
ensures absStack == AbsDefinition(treiber);
ensures absStack == AbsDefinition(treiber');
free ensures absStack == Abs(treiber);
free ensures absStack == Abs(treiber');
{
  var loc_n: Option LocTreiberNode;
  var n: StackElem X;

  if (treiber->top == None()) {
      absStack := Vec_Empty();
  } else {
      loc_n := treiber->top;
      assert Map_Contains(treiber->nodes, loc_n->t);
      n := Map_At(treiber->nodes, loc_n->t);
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
requires IsSubset(BetweenSet(treiber->nodes->val, treiber->top, None()), treiber->nodes->dom->val);
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
requires IsSubset(BetweenSet(treiber->nodes->val, treiber->top, None()), treiber->nodes->dom->val);
ensures Abs(treiber) == Abs(treiber');
{
  var absStack: Vec X;
  call absStack := AbsCompute(treiber, treiber');
}
