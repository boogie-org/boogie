// RUN: %boogie /proverOpt:SOLVER=noop /proverLog:"%t.smt2" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"

// One builtin per path by which Boogie hands a name to a symbol of its own: a selector, a datatype
// constructor, an incarnation and a bound variable. Nil is claimed through its tester, which Boogie spells
// is-Nil, so it is Nil that gets renamed.

datatype List { Nil(), Cons(head: int, tail: List) }
function {:builtin "|head#Cons|"} h(l: List): int;
function {:builtin "is-Nil"} n(l: List): bool;

var x: int;
function {:builtin "x@0"} x0(): int;

function {:builtin "y"} c(): int;

procedure P(l: List)
  modifies x;
{
  havoc x;
  assume h(l) == 0 && n(l) && x0() == 2 && x == 1 && (forall y: int :: c() == y);
  assert false;
}
// CHECK-L: (((Nil@@0 ) (Cons (|head#Cons@@0| Int)
// CHECK-L: (declare-fun x@0@@0 () Int)
// CHECK-L: (forall ((y@@0 Int) ) (! (= y y@@0)
