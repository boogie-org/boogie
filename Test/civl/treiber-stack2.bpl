// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *

type {:datatype} Treiber T;
function {:constructor} Treiber<T>(top: RefNode T, stack: Lmap (Node T)): Treiber T;
type RefTreiber T = Ref (Treiber T);

type X; // module type parameter 
var {:layer 0, 3} ts: Lmap (Treiber X);

procedure {:layer 4} {:atomic} AtomicPush(ref_t: RefTreiber X, x: X)
{
  // In terms of abstract stack
}

procedure {:layer 4} {:atomic} AtomicPop(ref_t: RefTreiber X) returns (x: X)
{
  // In terms of abstract stack
}

procedure {:layer 3} {:atomic} AtomicPushIntermediate(ref_t: RefTreiber X, x: X)
modifies ts;
{
  var ref_n: Ref (Node X);
  assert ts->dom[ref_t];
  call ref_n := Lmap_Add(ts->val[ref_t]->stack, Node(ts->val[ref_t]->top, x));
  call Lmap_Write(ts->val[ref_t]->top, ref_n);
}

procedure {:right} {:layer 2} 
AtomicReadTopOfStack#Push(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{ 
  assert ts->dom[ref_t];
}

procedure {:right} {:layer 3} 
AtomicReadTopOfStack#Pop(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{ 
  assert ts->dom[ref_t];
  assume ref_n == Nil() || ts->val[ref_t]->stack->dom[ref_n]; 
}

procedure {:atomic} {:layer 1,2} 
AtomicReadTopOfStack(ref_t: RefTreiber X) returns (ref_n: RefNode X)
{ 
  assert ts->dom[ref_t];
  ref_n := ts->val[ref_t]->top;
}
procedure {:yields} {:layer 0} {:refines "AtomicReadTopOfStack"} 
ReadTopOfStack(ref_t: RefTreiber X) returns (ref_n: RefNode X);

procedure {:right} {:layer 1,3} 
AtomicLoadNext(ref_t: RefTreiber X, ref_n: RefNode X) returns (next_ref_n: RefNode X)
{
  assert ts->dom[ref_t];
  assert ts->val[ref_t]->stack->dom[ref_n];
  next_ref_n := ts->val[ref_t]->stack->val[ref_n]->next;
}
procedure {:yields} {:layer 0} {:refines "AtomicLoadNext"} 
LoadNext(ref_t: RefTreiber X, ref_n: RefNode X) returns (next_ref_n: RefNode X);

procedure {:right} {:layer 1,2} 
AtomicTransferToStack(ref_t: RefTreiber X, {:linear_in} l_in: Lmap (Node X))
modifies ts;
{
  assert ts->dom[ref_t];
  call Lmap_Transfer(l_in, ts->val[ref_t]->stack);
}
procedure {:yields} {:layer 0} {:refines "AtomicTransferToStack"} 
TransferToStack(ref_t: RefTreiber X, {:linear_in} l_in: Lmap (Node X));

procedure {:atomic} {:layer 1,3} 
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

procedure {:yield_invariant} {:layer 2} YieldInv(ref_t: RefTreiber X);
requires ts->dom[ref_t];
requires BetweenSet(ts->val[ref_t]->stack->val, ts->val[ref_t]->top, Nil())[ts->val[ref_t]->top];
requires Subset(BetweenSet(ts->val[ref_t]->stack->val, ts->val[ref_t]->top, Nil()), Union(Singleton(Nil()), ts->val[ref_t]->stack->dom));

// Contents of node.bpl

type {:datatype} Node T;
type RefNode T = Ref (Node T);
function Nil<T>(): RefNode T;
function {:constructor} Node<T>(next: RefNode T, val: T): Node T;

function Between<T>(f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T): bool;
function Avoiding<T>(f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T): bool;
function {:inline} BetweenSet<T>(f:[RefNode T]Node T, x: RefNode T, z: RefNode T): [RefNode T]bool
{
  (lambda y: RefNode T :: Between(f, x, y, z))
}

// reflexive
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T :: Between(f, x, x, x));

// step
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T, w: RefNode T :: {Between(f, y, z, w), f[x]} Between(f, x, f[x]->next, f[x]->next));

// reach
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T :: {f[x], Between(f, x, y, y)} Between(f, x, y, y) ==> x == y || Between(f, x, f[x]->next, y));

// cycle
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y:RefNode T :: {f[x], Between(f, x, y, y)} f[x]->next == x && Between(f, x, y, y) ==> x == y);

// sandwich
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T :: {Between(f, x, y, x)} Between(f, x, y, x) ==> x == y);

// order1
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T :: {Between(f, x, y, y), Between(f, x, z, z)} Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T :: {Between(f, x, y, z)} Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T :: {Between(f, x, y, y), Between(f, y, z, z)} Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T, w: RefNode T :: {Between(f, x, y, z), Between(f, y, w, z)} Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T, w: RefNode T :: {Between(f, x, y, z), Between(f, x, w, y)} Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, u:RefNode T, x: RefNode T :: {Between(f, u, x, x)} Between(f, u, x, x) ==> Between(f, u, u, x));

// relation between Avoiding and Between
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T :: {Avoiding(f, x, y, z)} Avoiding(f, x, y, z) <==> (Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z))));
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, x: RefNode T, y: RefNode T, z: RefNode T :: {Between(f, x, y, z)} Between(f, x, y, z) <==> (Avoiding(f, x, y, z) && Avoiding(f, x, z, z)));

// update
axiom {:ctor "Node"} (forall<T> f: [RefNode T]Node T, u: RefNode T, v: RefNode T, x: RefNode T, p: RefNode T, q: Node T :: {Avoiding(f[p := q], u, v, x)} Avoiding(f[p := q], u, v, x) <==> ((Avoiding(f, u, v, p) && Avoiding(f, u, v, x)) || (Avoiding(f, u, p, x) && p != x && Avoiding(f, q->next, v, p) && Avoiding(f, q->next, v, x))));

function {:inline} Empty<T>(): [RefNode T]bool
{
  MapConst(false)
}

function {:inline} Singleton<T>(a: RefNode T): [RefNode T]bool 
{
  MapOne(a)
}

function {:inline} Union<T>(x: [RefNode T]bool, y: [RefNode T]bool): [RefNode T]bool
{
  MapOr(x, y)
}

function {:inline} Subset<T>(x: [RefNode T]bool, y: [RefNode T]bool): bool
{
  MapDiff(x, y) == MapConst(false)
}