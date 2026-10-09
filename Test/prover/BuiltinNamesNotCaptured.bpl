// RUN: %boogie /proverOpt:SOLVER=noop /proverLog:"%t.smt2" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t.smt2" "%s"

// Boogie names its own symbols around a {:builtin} function's: the selector of head, the incarnation of x and
// the bound y would be head#Cons, x@0 and y.

datatype List { Nil(), Cons(head: int, tail: List) }
function {:builtin "|head#Cons|"} h(l: List): int;

var x: int;
function {:builtin "x@0"} x0(): int;

function {:builtin "y"} c(): int;

procedure P(l: List)
  modifies x;
{
  havoc x;
  assume h(l) == 0 && x0() == 2 && x == 1 && (forall y: int :: c() == y);
  assert false;
}
// CHECK-L: (|head#Cons@@0| Int)
// CHECK-L: (declare-fun x@0@@0 () Int)
// CHECK: \(= \(\|head#Cons\| l\) 0\).*\(= x@0 2\).*\(= x@0@@0 1\).*\(forall \(\(y@@0 Int\) \) \(! \(= y y@@0\)
