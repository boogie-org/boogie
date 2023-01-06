// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *

type {:datatype} Node T;
type RefNode T = Ref (Node T);
function Nil<T>(): RefNode T;
function {:constructor} Node<T>(next: RefNode T, val: T): Node T;

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

function {:inline} Difference<T>(x: [RefNode T]bool, y: [RefNode T]bool): [RefNode T]bool
{
  MapDiff(x, y)
}

function {:inline} Subset<T>(x: [RefNode T]bool, y: [RefNode T]bool): bool
{
  MapDiff(x, y) == MapConst(false)
}

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
