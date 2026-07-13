// RUN: %parallel-boogie -lib:base -lib:node -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Lock-coupling (hand-over-hand) linked-list implementation of a set

// Thread identifiers are abstract; lock ownership is modelled with
// Option Tid, so None() means the lock is not currently held.
type Tid;

type X = int;

datatype LCList { LCList(head: Loc, nodes: Map (One Loc) (Node X)) }

var {:layer 0, 1} {:linear} list: LCList;

var {:layer 0, 1} locks: [Loc](Option Tid);

/// ////////////////////////////////////////////////////////////////
/// Yield invariants.
/// ////////////////////////////////////////////////////////////////

yield invariant {:layer 1} ListInv();
preserves Between(list->nodes->val, Some(list->head), None(), None());
preserves (forall loc: Loc :: Between(list->nodes->val, Some(list->head), Some(loc), None()) ==> Map_Contains(list->nodes, One(loc)));
preserves (var hn := Map_At(list->nodes, One(list->head))->next;
            (forall a, b: Loc :: Between(list->nodes->val, hn, Some(a), None()) && Between(list->nodes->val, Some(a), Some(b), None()) && a != b ==>
                Map_At(list->nodes, One(a))->val < Map_At(list->nodes, One(b))->val));

yield invariant {:layer 1} LockedBy(p: Loc, c: Option Loc, e: X, {:linear} tid: One Tid);
preserves locks[p] == Some(tid->val);
preserves Map_Contains(list->nodes, One(p));
preserves Between(list->nodes->val, Some(list->head), Some(p), None());
preserves Map_At(list->nodes, One(p))->next == c;
preserves p == list->head || Map_At(list->nodes, One(p))->val < e;

yield invariant {:layer 1} CorrectPosition(c: Option Loc, e: X);
preserves c == None() || (Map_Contains(list->nodes, One(c->t)) && Map_At(list->nodes, One(c->t))->val >= e);

// locate(e) walks the list holding the previous node's lock, until
// the current node's value is >= e.  Returns the previous pointer p
// (locked) and the current pointer c (unlocked).
yield procedure {:layer 1} locate({:linear} tid: One Tid, e: X)
returns (p: Loc, c: Option Loc)
preserves call ListInv();
ensures call LockedBy(p, c, e, tid);
ensures call CorrectPosition(c, e);
{
  var v: X;

  call p := ReadHead();
  call Lock(tid, p);
  call c := ReadNext(tid, p);
  while (true)
  invariant {:yields} true;
  invariant call ListInv();
  invariant call LockedBy(p, c, e, tid);
  {
    if (c is None) { break; }
    call v := ReadValue(c->t);
    if (v >= e) { break; }
    call Lock(tid, c->t);
    call Unlock(tid, p);
    p := c->t;
    call c := ReadNext(tid, p);
  }
}

// remove(e) removes e from the set if present.
yield procedure {:layer 1} remove({:linear} tid: One Tid, e: X)
preserves call ListInv();
{
  var x: Loc;
  var y, z: Option Loc;
  var v: X;

  call x, y := locate(tid, e);
  if (y is None) { return; }
  call v := ReadValue(y->t);
  if (v == e) {
    call Lock(tid, y->t);
    call z := ReadNext(tid, y->t);
    call WriteNext(tid, x, z);
    call Unlock(tid, y->t);
  }
  call Unlock(tid, x);
}

// add(e) adds e to the set if not already present.
yield procedure {:layer 1} add({:linear} tid: One Tid, e: X)
preserves call ListInv();
{
  var x, y: Loc;
  var z: Option Loc;
  var v: X;
  var toAdd: bool;

  call x, z := locate(tid, e);
  if (z is None) {
    toAdd := true;
  } else {
    call v := ReadValue(z->t);
    toAdd := v != e;
  }
  if (toAdd) {
    call y := AllocNode(Node(z, e));
    call WriteNext(tid, x, Some(y));
  }
  call Unlock(tid, x);
}

/// ////////////////////////////////////////////////////////////////
/// Layer-0 primitives.  Each refines an atomic action at layer 1.
/// ////////////////////////////////////////////////////////////////

// Acquire the lock on node a; blocks until it is free.
yield procedure {:layer 0} Lock({:linear} tid: One Tid, a: Loc);
refines right action {:layer 1} _
{
  assert Map_Contains(list->nodes, One(a));
  assume locks[a] == None();
  locks[a] := Some(tid->val);
}

// Release the lock on node a; the caller must own it.
yield procedure {:layer 0} Unlock({:linear} tid: One Tid, a: Loc);
refines left action {:layer 1} _
{
  assert Map_Contains(list->nodes, One(a));
  assert locks[a] == Some(tid->val);
  locks[a] := None();
}

// Read the head
yield procedure {:layer 0} ReadHead() returns (h: Loc);
refines both action {:layer 1} _
{
  h := list->head;
}

// Read the tail pointer of node a.  Caller must hold a's lock.
yield procedure {:layer 0} ReadNext({:linear} tid: One Tid, a: Loc)
returns (next: Option Loc);
refines both action {:layer 1} _
{
  assert Map_Contains(list->nodes, One(a));
  assert locks[a] == Some(tid->val);
  next := Map_At(list->nodes, One(a))->next;
}

// Read the immutable value field of node a.  No lock required
// because the value field of a node never changes after allocation.
yield procedure {:layer 0} ReadValue(a: Loc) returns (v: X);
refines both action {:layer 1} _
{
  assert Map_Contains(list->nodes, One(a));
  v := Map_At(list->nodes, One(a))->val;
}

// Overwrite the tail pointer of node a.  Caller must hold a's lock.
yield procedure {:layer 0} WriteNext({:linear} tid: One Tid, a: Loc,
                                     next: Option Loc);
refines both action {:layer 1} _
{
  assert Map_Contains(list->nodes, One(a));
  assert locks[a] == Some(tid->val);
  call Path_Store(list->nodes->val[One(a)]->next, next);
}

// Allocate a fresh node with the given payload, return its address.
// The fresh node starts out unlocked.
yield procedure {:layer 0} AllocNode(node: Node X)
returns (loc: Loc);
refines atomic action {:layer 1} _
{
  var one_loc: One Loc;

  call one_loc := Loc_New();
  call Map_Put(list->nodes, one_loc, node);
  loc := one_loc->val;
  locks[loc] := None();
}
