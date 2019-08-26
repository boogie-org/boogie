// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const null: int;
type lmap;
function {:linear "Node"} dom(lmap): [int]bool;
function map(lmap): [int]int;
function {:builtin "MapConst"} MapConstBool(bool) : [int]bool;

function EmptyLmap(): (lmap);
axiom (dom(EmptyLmap()) == MapConstBool(false));

function Add(x: lmap, i: int, v: int): (lmap);
axiom (forall x: lmap, i: int, v: int :: dom(Add(x, i, v)) == dom(x)[i:=true] && map(Add(x, i, v)) == map(x)[i := v]);

function Remove(x: lmap, i: int): (lmap);
axiom (forall x: lmap, i: int :: dom(Remove(x, i)) == dom(x)[i:=false] && map(Remove(x, i)) == map(x));

procedure {:right} {:layer 1} AtomicReadTopOfStack() returns (v:int)
{ assume v == null || dom(Stack)[v] || Used[v]; }

procedure {:yields} {:layer 0} {:refines "AtomicReadTopOfStack"} ReadTopOfStack() returns (v:int);

procedure {:right} {:layer 1} AtomicLoad(i:int) returns (v:int)
{
  assert dom(Stack)[i] || Used[i];
  if (dom(Stack)[i]) {
    v := map(Stack)[i];
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load(i:int) returns (v:int);

procedure {:both} {:layer 1} AtomicStore({:linear_in "Node"} l_in:lmap, i:int, v:int) returns ({:linear "Node"} l_out:lmap)
{ assert dom(l_in)[i]; l_out := Add(l_in, i, v); }

procedure {:yields} {:layer 0} {:refines "AtomicStore"} Store({:linear_in "Node"} l_in:lmap, i:int, v:int) returns ({:linear "Node"} l_out:lmap);

procedure {:atomic} {:layer 1} AtomicTransferToStack(oldVal: int, newVal: int, {:linear_in "Node"} l_in:lmap) returns (r: bool, {:linear "Node"} l_out:lmap)
modifies TopOfStack, Stack;
{
  assert dom(l_in)[newVal];
  if (oldVal == TopOfStack) {
    TopOfStack := newVal;
    l_out := EmptyLmap();
    Stack := Add(Stack, newVal, map(l_in)[newVal]);
    r := true;
  } else {
    l_out := l_in;
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferToStack"} TransferToStack(oldVal: int, newVal: int, {:linear_in "Node"} l_in:lmap) returns (r: bool, {:linear "Node"} l_out:lmap);

procedure {:atomic} {:layer 1} AtomicTransferFromStack(oldVal: int, newVal: int) returns (r: bool)
modifies TopOfStack, Used, Stack;
{
  assert oldVal != null;
  assert Inv(TopOfStack, Stack);
  if (oldVal == TopOfStack) {
    TopOfStack := newVal;
    Used[oldVal] := true;
    Stack := Remove(Stack, oldVal);
    r := true;
  }
  else {
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromStack"} TransferFromStack(oldVal: int, newVal: int) returns (r: bool);

var {:layer 0,2} TopOfStack: int;
var {:linear "Node"} {:layer 0,2} Stack: lmap;


function {:inline} Inv(TopOfStack: int, Stack: lmap) : (bool)
{
  BetweenSet(map(Stack), TopOfStack, null)[TopOfStack] &&
  Subset(BetweenSet(map(Stack), TopOfStack, null), Union(Singleton(null), dom(Stack)))
}

var {:linear "Node"} {:layer 0,2} Used: [int]bool;

function {:inline} {:linear "Node"} NodeCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "Node"} NodeSetCollector(x: [int]bool) : [int]bool
{
  x
}

procedure {:atomic} {:layer 2} atomic_push(x: int, {:linear_in "Node"} x_lmap: lmap)
modifies Stack, TopOfStack;
{ assert dom(x_lmap)[x]; Stack := Add(Stack, x, TopOfStack); TopOfStack := x; }

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: int, {:linear_in "Node"} x_lmap: lmap)
requires {:layer 1} dom(x_lmap)[x];
requires {:layer 1} Inv(TopOfStack, Stack);
ensures {:layer 1} Inv(TopOfStack, Stack);
{
  var t: int;
  var g: bool;
  var {:linear "Node"} t_lmap: lmap;

  yield;
  assert {:layer 1} Inv(TopOfStack, Stack);
  t_lmap := x_lmap;
  while (true)
  invariant {:layer 1} dom(t_lmap) == dom(x_lmap);
  invariant {:layer 1} Inv(TopOfStack, Stack);
  {
    call t := ReadTopOfStack();
    call t_lmap := Store(t_lmap, x, t);
    call g, t_lmap := TransferToStack(t, x, t_lmap);
    if (g) {
      break;
    }
    yield;
    assert {:layer 1} dom(t_lmap) == dom(x_lmap);
    assert {:layer 1} Inv(TopOfStack, Stack);
  }
  yield;
  assert {:expand} {:layer 1} Inv(TopOfStack, Stack);
}

procedure {:atomic} {:layer 2} atomic_pop() returns (t: int)
modifies Used, TopOfStack, Stack;
{ assert Inv(TopOfStack, Stack); assume TopOfStack != null; t := TopOfStack; Used[t] := true; TopOfStack := map(Stack)[t]; Stack := Remove(Stack, t); }

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (t: int)
requires {:layer 1} Inv(TopOfStack, Stack);
ensures {:layer 1} Inv(TopOfStack, Stack);
{
  var g: bool;
  var x: int;

  yield;
  assert {:layer 1} Inv(TopOfStack, Stack);
  while (true)
  invariant {:layer 1} Inv(TopOfStack, Stack);
  {
    call t := ReadTopOfStack();
    if (t != null) {
      call x := Load(t);
      call g := TransferFromStack(t, x);
      if (g) {
        break;
      }
    }
    yield;
    assert {:layer 1} Inv(TopOfStack, Stack);
  }
  yield;
  assert {:layer 1} Inv(TopOfStack, Stack);
}

function Equal([int]bool, [int]bool) returns (bool);
function Subset([int]bool, [int]bool) returns (bool);

function Empty() returns ([int]bool);
function Singleton(int) returns ([int]bool);
function Union([int]bool, [int]bool) returns ([int]bool);

axiom(forall x:int :: !Empty()[x]);

axiom(forall x:int, y:int :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall y:int :: {Singleton(y)} Singleton(y)[y]);

axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T)[x]}{Union(S,T),S[x]}{Union(S,T),T[x]} Union(S,T)[x] <==> S[x] || T[x]);

axiom(forall S:[int]bool, T:[int]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x],Subset(S,T)}{T[x],Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall S:[int]bool, T:[int]bool :: {Subset(S,T)} Subset(S,T) || (exists x:int :: S[x] && !T[x]));

////////////////////
// Between predicate
////////////////////
function Between(f: [int]int, x: int, y: int, z: int) returns (bool);
function Avoiding(f: [int]int, x: int, y: int, z: int) returns (bool);


//////////////////////////
// Between set constructor
//////////////////////////
function BetweenSet(f: [int]int, x: int, z: int) returns ([int]bool);

////////////////////////////////////////////////////
// axioms relating Between and BetweenSet
////////////////////////////////////////////////////
axiom(forall f: [int]int, x: int, y: int, z: int :: {BetweenSet(f, x, z)[y]} BetweenSet(f, x, z)[y] <==> Between(f, x, y, z));
axiom(forall f: [int]int, x: int, y: int, z: int :: {Between(f, x, y, z), BetweenSet(f, x, z)} Between(f, x, y, z) ==> BetweenSet(f, x, z)[y]);
axiom(forall f: [int]int, x: int, z: int :: {BetweenSet(f, x, z)} Between(f, x, x, x));
axiom(forall f: [int]int, x: int, z: int :: {BetweenSet(f, x, z)} Between(f, z, z, z));


//////////////////////////
// Axioms for Between
//////////////////////////

// reflexive
axiom(forall f: [int]int, x: int :: Between(f, x, x, x));

// step
axiom(forall f: [int]int, x: int, y: int, z: int, w:int :: {Between(f, y, z, w), f[x]} Between(f, x, f[x], f[x]));

// reach
axiom(forall f: [int]int, x: int, y: int :: {f[x], Between(f, x, y, y)} Between(f, x, y, y) ==> x == y || Between(f, x, f[x], y));

// cycle
axiom(forall f: [int]int, x: int, y:int :: {f[x], Between(f, x, y, y)} f[x] == x && Between(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [int]int, x: int, y: int :: {Between(f, x, y, x)} Between(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [int]int, x: int, y: int, z: int :: {Between(f, x, y, y), Between(f, x, z, z)} Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom(forall f: [int]int, x: int, y: int, z: int :: {Between(f, x, y, z)} Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom(forall f: [int]int, x: int, y: int, z: int :: {Between(f, x, y, y), Between(f, y, z, z)} Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom(forall f: [int]int, x: int, y: int, z: int, w: int :: {Between(f, x, y, z), Between(f, y, w, z)} Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom(forall f: [int]int, x: int, y: int, z: int, w: int :: {Between(f, x, y, z), Between(f, x, w, y)} Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom(forall f: [int]int, u:int, x: int :: {Between(f, u, x, x)} Between(f, u, x, x) ==> Between(f, u, u, x));

// relation between Avoiding and Between
axiom(forall f: [int]int, x: int, y: int, z: int :: {Avoiding(f, x, y, z)} Avoiding(f, x, y, z) <==> (Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z))));
axiom(forall f: [int]int, x: int, y: int, z: int :: {Between(f, x, y, z)} Between(f, x, y, z) <==> (Avoiding(f, x, y, z) && Avoiding(f, x, z, z)));

// update
axiom(forall f: [int]int, u: int, v: int, x: int, p: int, q: int :: {Avoiding(f[p := q], u, v, x)} Avoiding(f[p := q], u, v, x) <==> ((Avoiding(f, u, v, p) && Avoiding(f, u, v, x)) || (Avoiding(f, u, p, x) && p != x && Avoiding(f, q, v, p) && Avoiding(f, q, v, x))));

axiom (forall f: [int]int, p: int, q: int, u: int, w: int :: {BetweenSet(f[p := q], u, w)} Avoiding(f, u, w, p) ==> Equal(BetweenSet(f[p := q], u, w), BetweenSet(f, u, w)));
axiom (forall f: [int]int, p: int, q: int, u: int, w: int :: {BetweenSet(f[p := q], u, w)} p != w && Avoiding(f, u, p, w) && Avoiding(f, q, w, p) ==> Equal(BetweenSet(f[p := q], u, w), Union(BetweenSet(f, u, p), BetweenSet(f, q, w))));
axiom (forall f: [int]int, p: int, q: int, u: int, w: int :: {BetweenSet(f[p := q], u, w)} Avoiding(f, u, w, p) || (p != w && Avoiding(f, u, p, w) && Avoiding(f, q, w, p)) || Equal(BetweenSet(f[p := q], u, w), Empty()));
