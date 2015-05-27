// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type Node = int;
const unique null: Node;
type lmap;
function {:linear "Node"} dom(lmap): [Node]bool;
function map(lmap): [Node]Node;
function {:builtin "MapConst"} MapConstBool(bool) : [Node]bool;

function EmptyLmap(): (lmap);
axiom (dom(EmptyLmap()) == MapConstBool(false));

function Add(x: lmap, i: Node, v: Node): (lmap);
axiom (forall x: lmap, i: Node, v: Node :: dom(Add(x, i, v)) == dom(x)[i:=true] && map(Add(x, i, v)) == map(x)[i := v]);

function Remove(x: lmap, i: Node): (lmap);
axiom (forall x: lmap, i: Node :: dom(Remove(x, i)) == dom(x)[i:=false] && map(Remove(x, i)) == map(x));

procedure {:yields} {:layer 0,1} ReadTopOfStack() returns (v:Node);
ensures {:right} |{ A: assume dom(Stack)[v] || dom(Used)[v]; return true; }|;

procedure {:yields} {:layer 0,1} Load(i:Node) returns (v:Node);
ensures {:right} |{ A: assert dom(Stack)[i] || dom(Used)[i]; goto B,C;
	            B: assume dom(Stack)[i]; v := map(Stack)[i]; return true; 
		    C: assume !dom(Stack)[i]; return true; }|;

procedure {:yields} {:layer 0,1} Store({:linear_in "Node"} l_in:lmap, i:Node, v:Node) returns ({:linear "Node"} l_out:lmap);
ensures {:both} |{ A: assert dom(l_in)[i]; l_out := Add(l_in, i, v); return true; }|;

procedure {:yields} {:layer 0,1} TransferToStack(oldVal: Node, newVal: Node, {:linear_in "Node"} l_in:lmap) returns (r: bool, {:linear "Node"} l_out:lmap);
ensures {:atomic} |{ A: assert dom(l_in)[newVal];
		        goto B,C;
                        B: assume oldVal == TopOfStack; TopOfStack := newVal; l_out := EmptyLmap(); Stack := Add(Stack, newVal, map(l_in)[newVal]); r := true; return true;
			C: assume oldVal != TopOfStack; l_out := l_in; r := false; return true; }|;

procedure {:yields} {:layer 0,1} TransferFromStack(oldVal: Node, newVal: Node) returns (r: bool);
ensures {:atomic} |{ A: goto B,C;
                        B: assume oldVal == TopOfStack; TopOfStack := newVal; Used := Add(Used, oldVal, map(Stack)[oldVal]); Stack := Remove(Stack, oldVal); r := true; return true;
		        C: assume oldVal != TopOfStack; r := false; return true; }|;

var {:layer 0} TopOfStack: Node;
var {:linear "Node"} {:layer 0} Stack: lmap;


function {:inline} Inv(TopOfStack: Node, Stack: lmap) : (bool)
{
  BetweenSet(map(Stack), TopOfStack, null)[TopOfStack] &&
  Subset(BetweenSet(map(Stack), TopOfStack, null), Union(Singleton(null), dom(Stack)))
}

var {:linear "Node"} {:layer 0} Used: lmap;

procedure {:yields} {:layer 1} push(x: Node, {:linear_in "Node"} x_lmap: lmap)
requires {:layer 1} dom(x_lmap)[x];
requires {:layer 1} Inv(TopOfStack, Stack);
ensures {:layer 1} Inv(TopOfStack, Stack);
ensures {:atomic} |{ A: Stack := Add(Stack, x, TopOfStack); TopOfStack := x; return true; }|;
{
  var t: Node;
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
      assert {:layer 1} map(Stack)[x] == t;
      break;
    }
    yield; 
    assert {:layer 1} dom(t_lmap) == dom(x_lmap);
    assert {:layer 1} Inv(TopOfStack, Stack);
  }
  yield; 
  assert {:expand} {:layer 1} Inv(TopOfStack, Stack);
}

procedure {:yields} {:layer 1} pop() returns (t: Node)
requires {:layer 1} Inv(TopOfStack, Stack);
ensures {:layer 1} Inv(TopOfStack, Stack);
ensures {:atomic} |{ A: assume TopOfStack != null; t := TopOfStack; Used := Add(Used, t, map(Stack)[t]); TopOfStack := map(Stack)[t]; Stack := Remove(Stack, t); return true; }|;
{
  var g: bool;
  var x: Node;

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
function Reachable([int,int]bool, int) returns ([int]bool);
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